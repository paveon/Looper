(*
 * Copyright (c) 2018-present
 *
 * Vladimir Marcin (xmarci10@stud.fit.vutbr.cz)
 * Automated Analysis and Verification Research Group (VeriFIT)
 * Brno University of Technology, Czech Republic
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)
  open! IStd
  open Graph
  open Traverse
  module F = Format
  module L = Logging

  module LockEvent = struct
    type t = AccessPath.t * Location.t

    (* compare (AccessPath.t * Location.t) (AccessPath.t * Location.t) *)

    (* AccessPath.t = base * access list *)
    
    let compare (((base, aclist) as lock), _) ((((base'), aclist') as lock' ), _) =
      if phys_equal lock lock' then 0
      else begin
        let res = AccessPath.compare_base base base' in
        if not (Int.equal res 0) then res
        else
          List.compare AccessPath.compare_access aclist aclist'
      end

    let equal lock lock' = Int.equal 0 (compare lock lock')

    let hash (lock, _) = Hashtbl.hash lock

    let pp fmt ((((_,_), _) as lock), loc) =
      F.fprintf fmt "lock %a on %a" AccessPath.pp lock Location.pp loc;
  end

  module LockWarning = struct
    (** IssueType := DoubleLocking | DoubleUnlocking | ReleaseWithoutAcquisition
     *)
    type t = LockEvent.t list * Location.t * Procname.t * string * IssueType.t [@@deriving compare]
    
    let pp fmt _ = F.fprintf fmt "Locking error\n"
    
    let make_string_of_lock : LockEvent.t -> string =
      fun lock ->
        F.asprintf "%a" LockEvent.pp lock
  end

  (*TODO replace Edges module with LocksGraph module*)
  module LocksGraph = struct
    include Imperative.Digraph.Concrete(LockEvent)
  end

  module DfsLG = struct
    include Dfs(LocksGraph)
  end

  module Edge = struct
    type t = {edge:LocksGraph.E.t; pname: Procname.t} 

    let compare edge edge' =
      let edge1 = edge.edge in
      let edge2 = edge'.edge in
      if phys_equal edge.edge edge'.edge then 0
      else begin
        let res = LockEvent.compare (fst edge1) (fst edge2) in
        if (Int.equal res 0) then begin
          let res = LockEvent.compare (snd edge1) (snd edge2) in
          if (Int.equal res 0) then 0
          else res
        end
        else
          res
      end    

    let equal edge edge' =
      if LockEvent.equal (fst edge) (fst edge') && 
        LockEvent.equal (snd edge) (snd edge') then
        true
      else
        false

    let pp : F.formatter -> t -> unit =
      fun fmt astate ->
        F.fprintf fmt "%a -> %a in %a" 
          LockEvent.pp (fst astate.edge) 
          LockEvent.pp (snd astate.edge)
          (MarkupFormatter.wrap_monospaced Procname.pp)
          astate.pname
  end

  module Lockset = AbstractDomain.FiniteSet(LockEvent)
  module Edges = AbstractDomain.FiniteSet(Edge)
  module ReportSet = AbstractDomain.FiniteSet(LockWarning)

  type t = 
  {
    (* PRECONDITION *)
    locked: Lockset.t;  (* locks that should be locked before calling the function*)
    unlocked: Lockset.t; (* locks that should be unlocked before calling the function*)
    (* POSTCONDITION *)
    lockset: Lockset.t;  (* the currently locked locks *)
    unlockset: Lockset.t; (* the currently unlocked locks *)
    dependencies: Edges.t; (* dependecies of the type A->B: B got locked at a moment when A was still locked *)
    order: Edges.t; (* dependencies of the unlock->lock type, to safely determine the order of operations *)
    wereLocked: Lockset.t (* all the locks that were locked in the function *) 
  }

  let empty = 
  {
    lockset = Lockset.empty; 
    unlockset = Lockset.empty; 
    dependencies = Edges.empty; 
    locked = Lockset.empty; 
    unlocked = Lockset.empty; 
    order = Edges.empty;
    wereLocked = Lockset.empty 
  }

  let reportMap = ref ReportSet.empty

  let is_local : LockEvent.t -> bool =
    fun (((base,_), _), _) ->
      match base with
      | LogicalVar _ -> false
      | ProgramVar pvar -> Pvar.is_local pvar

  let is_formal ((base,_), _) extras =
    FormalMap.is_formal base extras 
    
  let acquire lockid astate loc extras pname =
    let lock : LockEvent.t = (lockid, loc) in
    
    (* Compare each element of a set with the currently released lock. *)    
    let cmp elem =  if (LockEvent.equal elem lock) then true else false in
    
    (* For each element in the current 'lockset' create a pair (element, acquired_lock). *)
    let add_pair elem acc = 
      Edges.add {edge = (elem, lock); pname = pname} acc
    in

    let new_astate : t =
      let locked = astate.locked in
      let unlocked = 
        if (Lockset.exists cmp astate.locked) || 
          (Lockset.exists cmp astate.unlocked) ||
          ((is_local lock) && (not(is_formal lock extras))) then 
          astate.unlocked
        else
          if not(Lockset.exists cmp astate.unlockset) then
            (** Lock is the first operation with a given lock, so this lock is
             *  added to the precondition ('unlocked' set) of the analysed function.
             *  (only globals or formals are added to the precondition) 
             *)
            Lockset.add lock astate.unlocked
          else
            astate.unlocked
      in
      let lockset =
        if ((Lockset.exists cmp astate.lockset)) then begin 
          if Config.locking_error then
            (** Double locking and heuritics turned on (Config.locking_error=True). 
              *  We assume that our analyser used a non-existent path to reach the lock statement
              *  so we discard the current locket (no longer trustworthy), and the only
              *  lock left in it is currently acquired onw, as it is the only one about we
              *  can safely say that is locked.
              *)
            Lockset.add lock Lockset.empty
          else begin
            (** Double locking and heuritics turned off (Config.locking_error=False). 
             *  We assume that program is in inconsistent state, so warning is reported.
             *)
            reportMap := ReportSet.add ([lock], loc, pname, "Double locking", IssueType.double_locking) !reportMap;
            Lockset.add lock astate.lockset
          end
        end
        else
          Lockset.add lock astate.lockset 
      in
      let unlockset = Lockset.remove lock astate.unlockset in
      let dependencies =
        if ((Lockset.exists cmp astate.lockset) && Config.locking_error) then
          (** Double locking and heuritics turned on (Config.locking_error=True). 
           *  Don't emit an edge with the currently acquired lock, since current
           *  lockset is no longer trustworthy.
           *)
          astate.dependencies
        else   
          Lockset.fold add_pair astate.lockset astate.dependencies 
      in
      let order = Lockset.fold add_pair astate.unlockset astate.order in
      let wereLocked = 
        (* Only globals or formals are added to the 'wereLocked' set *)
        if((is_local lock) && (not(is_formal lock extras))) then
          astate.wereLocked
        else
          Lockset.add lock astate.wereLocked 
      in
      { lockset; unlockset; dependencies; locked; unlocked; order; wereLocked }
    in
    new_astate

  let release lockid astate loc extras pname =
    let lock : LockEvent.t = (lockid, loc) in
    (* Compare each element of a set with the currently released lock. *)    
    let cmp elem =  if (LockEvent.equal elem lock) then true else false in

    let new_astate : t =
      let locked =
        if (Lockset.exists cmp astate.locked) || 
          (Lockset.exists cmp astate.unlocked) ||
          ((is_local lock) && (not(is_formal lock extras))) then
          astate.locked
        else
          if not(Lockset.exists cmp astate.lockset) then 
            (** Release is the first operation with a given lock, so this lock is
             *  added to the precondition ('locked' set) of the analysed function.
             *  (only globals or formals are added to the precondition) 
             *)
            Lockset.add lock astate.locked
          else
            astate.locked
      in
      let unlocked = astate.unlocked in
      let lockset =
        (* if(not(Lockset.exists cmp astate.lockset) && not(Lockset.exists cmp astate.locked)) then *)
        if (Lockset.exists cmp astate.unlockset) then 
          if Config.locking_error then
            (** Double unlocking and heuritics turned on (Config.locking_error=True). 
             *  We assume that our analyser used a non-existent path to reach the unlock statement
             *  so we discard the current locket (no longer trustworthy), thereby eliminating any
             *  dependencies that straddle the locking error. 
             *) 
            Lockset.empty
          else begin
            (** Double unlocking and heuritics turned of (Config.locking_error=False). 
             *  We assume that program is in inconsistent state, so warning is reported.
             *)
            reportMap := ReportSet.add ([lock], loc, pname, "Double unlocking", IssueType.double_unlocking) !reportMap;
            Lockset.remove lock astate.lockset
          end
        else 
          Lockset.remove lock astate.lockset 
      in
      let unlockset = Lockset.add lock astate.unlockset in
      let dependencies = astate.dependencies in
      let order = astate.order in
      let wereLocked = astate.wereLocked in
      { lockset; unlockset; dependencies; locked; unlocked; order; wereLocked }
    in
    new_astate


  let integrate_summary astate callee_pname loc callee_summary callee_formals actuals caller_pname= 
    let formal_to_access_path : Mangled.t * Typ.t -> AccessPath.t = fun (name, typ) ->
      let pvar = Pvar.mk name callee_pname in
      AccessPath.base_of_pvar pvar typ, []
    in

    let get_corresponding_actual formal =
      let rec find x lst =
        match lst with
        | [] -> -1
        | h :: t -> if AccessPath.equal x (formal_to_access_path h) then 0 else 1 + find x t 
      in
      List.nth actuals (find formal callee_formals) 
      |> Option.value_map ~default:[] ~f:HilExp.get_access_exprs 
      |> List.hd |> Option.map ~f:HilExp.AccessExpression.to_access_path
    in

    let replace_formals_with_actuals summary_set formal =
      let replace_basis ((summary_element, loc) as le) = 
          if AccessPath.is_prefix (formal_to_access_path formal) summary_element then begin
            let actual = get_corresponding_actual (formal_to_access_path formal) in
            (* create an element with base of acutal and acl of summ_element*)
            match actual with
            | Some a ->
                let new_element = (AccessPath.append a (snd summary_element), loc) in
                new_element
            | None -> 
                le
          end
          else le
      in
      Lockset.map replace_basis summary_set
    in

    let replace_formals_with_actuals_dependencies summary_dependencies formal =
      let update_edge : Edge.t -> Edge.t =
        fun edge_t ->
          let edge = edge_t.edge in
          if AccessPath.is_prefix (formal_to_access_path formal) (fst (fst edge)) then begin
            let actual = get_corresponding_actual (fst (fst edge)) in
            match actual with
            | Some a ->
                let loc = (snd (fst edge)) in
                let new_element = ((AccessPath.append a (snd (fst (fst edge)))), loc) in
                let new_edge = (new_element, (snd edge)) in
                {edge = new_edge; pname = edge_t.pname}
            | None -> edge_t
          end
          else if AccessPath.is_prefix (formal_to_access_path formal) (fst (snd edge)) then begin  
            let actual = get_corresponding_actual (fst (snd edge)) in
            match actual with
            | Some a ->
                let loc = (snd (snd edge)) in
                let new_element = ((AccessPath.append a (snd (fst (snd edge)))), loc) in
                let new_edge = ((fst edge), new_element) in
                {edge = new_edge; pname = edge_t.pname}
            | None -> edge_t
          end       
          else
            edge_t
      in
      Edges.map update_edge summary_dependencies
    in

    (* Replace formals with acutals in the summary. *)
    (* List.map  *)

    (* [1,2,3,4,5] acc:0 f(x acc -> acc + x) *)

    let summary_lockset =
      List.fold callee_formals ~init:callee_summary.lockset ~f:replace_formals_with_actuals in
    let summary_unlockset =
      List.fold callee_formals ~init:callee_summary.unlockset ~f:replace_formals_with_actuals in
    let summary_locked =
      List.fold callee_formals ~init:callee_summary.locked ~f:replace_formals_with_actuals in
    let summary_unlocked =
      List.fold callee_formals ~init:callee_summary.unlocked ~f:replace_formals_with_actuals in
    let summary_wereLocked = 
      List.fold callee_formals ~init:callee_summary.wereLocked ~f:replace_formals_with_actuals in
    let summary_dependencies =
      List.fold callee_formals ~init:callee_summary.dependencies ~f:replace_formals_with_actuals_dependencies in
    let summary_order =
      List.fold callee_formals ~init:callee_summary.order ~f:replace_formals_with_actuals_dependencies in
    
    (* Check of a precondition *)
    if (not(Lockset.is_empty (Lockset.inter astate.lockset summary_unlocked)) &&
       not(Config.locking_error)) then begin
      (* Double locking *)
      let erroneously_locks = Lockset.elements (Lockset.inter summary_unlocked astate.lockset) in
      reportMap := ReportSet.add (erroneously_locks, loc, callee_pname, "Double locking", IssueType.double_locking) !reportMap;
    end;
    if (not(Lockset.is_empty (Lockset.inter astate.unlockset summary_locked)) &&
       not(Config.locking_error)) then begin
      (* Double unlocking *)
      let erroneously_locks = Lockset.elements (Lockset.inter summary_locked astate.unlockset) in  
      reportMap := ReportSet.add (erroneously_locks, loc, callee_pname, "Double unlocking", IssueType.double_unlocking) !reportMap
    end;

    let new_astate : t =
      let locked = Lockset.fold (fun elem acc ->
        (** Check that all the locks that should be locked before calling the callee
         *  are in the current 'lockset'. I they are not, it means that they must be 
         *  locked even before the currently analysed function, so we update its 
         *  precondition (by adding the lock to its 'locked' set).
         *)
        if not(Lockset.exists (fun p ->if (LockEvent.equal p elem) then true else false) astate.lockset) then 
          Lockset.add elem acc 
        else acc) summary_locked astate.locked 
      in
      let unlocked = Lockset.fold (fun elem acc ->
        (** Same as above, but instead of checking locked locks, we check those which
         *  should be unlocked (so now we look to the 'unlockset').
         *)
        if not(Lockset.exists (fun p ->if (LockEvent.equal p elem) then true else false) astate.unlockset) then 
          Lockset.add elem acc 
        else acc) summary_unlocked astate.unlocked 
      in
      let unlockset = Lockset.union (Lockset.diff astate.unlockset summary_lockset) summary_unlockset in
      let order = Edges.union astate.order summary_order in 
      let wereLocked = Lockset.union astate.wereLocked summary_wereLocked in
      if ( ( not(Lockset.is_empty (Lockset.inter astate.lockset summary_unlocked))
          || not(Lockset.is_empty (Lockset.inter astate.unlockset summary_locked)) )
          && Config.locking_error ) then begin
        (** Double locking/unlocking and heuritics turned on (Config.locking_error=True). 
         *  Our analyser used a non-existent path to reach the function call and
         *  therefore the current lockset is discarded (no longer trustworthy).
         *  Also, no new dependency will be generated with locks in the bad lockset.
         *)
        let lockset = summary_lockset in
        let dependencies = Edges.union astate.dependencies summary_dependencies in  
        { lockset; unlockset; dependencies; locked; unlocked; order; wereLocked }
      end 
      else begin
        let lockset = Lockset.diff (Lockset.union astate.lockset summary_lockset) summary_unlockset in
        (** Add a new dependecies between currently held locks and locks which 'wereLocked'
         *  in the callee. Before adding a newly created dependency X->Y, we need to verify
         *  whether the lock X from the current 'lockset' was not unlocked before locking 
         *  the lock Y in the callee (to do that we use the 'order' set in the summary of a callee).
         *)
        let dependencies = 
          let add_pair : Lockset.elt -> Edges.t -> Edges.t = 
            fun astate_lockest_elem astate_dependencies ->
              Lockset.fold (fun summary_wereLocked_elem astate_dependencies ->
                let inter_check : Edges.elt -> bool =
                  fun p (* item of order *) ->
                    if (Edge.equal p.edge (astate_lockest_elem, summary_wereLocked_elem)) then true
                    else false
                in
                if not(Edges.exists inter_check summary_order) then
                  Edges.add {edge = (astate_lockest_elem, summary_wereLocked_elem); pname = caller_pname} astate_dependencies
                else
                  astate_dependencies) summary_wereLocked astate_dependencies 
          in
          let emit_dependencies = Lockset.fold add_pair astate.lockset astate.dependencies in
          Edges.union astate.dependencies emit_dependencies 
        in  
        { lockset; unlockset; dependencies; locked; unlocked; order; wereLocked }
      end              
    in
    new_astate

  let ( <= ) ~lhs ~rhs =
    Lockset.leq ~lhs:lhs.lockset ~rhs:rhs.lockset &&
    Lockset.leq ~lhs:lhs.unlockset ~rhs:rhs.unlockset &&
    Edges.leq ~lhs:lhs.dependencies ~rhs:rhs.dependencies &&
    Lockset.leq ~lhs:lhs.locked ~rhs:rhs.locked &&
    Lockset.leq ~lhs:lhs.unlocked ~rhs:rhs.unlocked &&
    Edges.leq ~lhs:lhs.order ~rhs:rhs.order &&
    Lockset.leq ~lhs:lhs.wereLocked ~rhs:rhs.wereLocked

  let leq ~lhs ~rhs = (<=) ~lhs ~rhs

  let join astate1 astate2 =
    let new_astate : t =
      let lockset = Lockset.union astate1.lockset astate2.lockset in
      let unlockset = Lockset.union astate1.unlockset astate2.unlockset in
      let dependencies = Edges.union astate1.dependencies astate2.dependencies in
      let locked = Lockset.union astate1.locked astate2.locked in 
      let unlocked = Lockset.union astate1.unlocked astate2.unlocked in
      let order = Edges.inter astate1.order astate2.order in
      let wereLocked = Lockset.union astate1.wereLocked astate2.wereLocked in
      { lockset; unlockset; dependencies; locked; unlocked; order; wereLocked}
    in
    new_astate 
  
  let widen ~prev ~next ~num_iters:_ =
    join prev next

  let pp : F.formatter -> t -> unit =
    fun fmt astate -> 
      F.fprintf fmt "locked=%a\n" Lockset.pp astate.locked;
      F.fprintf fmt "unlocked=%a\n" Lockset.pp astate.unlocked;
      F.fprintf fmt "lockset=%a\n" Lockset.pp astate.lockset;
      F.fprintf fmt "unlockset=%a\n" Lockset.pp astate.unlockset;
      F.fprintf fmt "dependencies=%a\n" Edges.pp astate.dependencies;
      F.fprintf fmt "order=%a\n" Edges.pp astate.order;
      F.fprintf fmt "wereLocked=%a\n" Lockset.pp astate.wereLocked;

  type summary = t