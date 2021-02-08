(* Author: Ondrej Pavela <xpavel34@stud.fit.vutbr.cz> *)


open! IStd


module GraphData : sig
  type t = {
    last_node: LooperDomain.DCP.Node.t;
    loophead_stack: Procdesc.Node.t Stack.t;
    nodes: LooperDomain.DCP.NodeSet.t;
    edges: LooperDomain.DCP.EdgeSet.t;
    edge_data: LooperDomain.DCP.EdgeData.t;
    ident_map: LooperDomain.EdgeExp.t Ident.Map.t;
    node_map: LooperDomain.DCP.Node.t Procdesc.NodeMap.t;
    potential_norms: LooperDomain.EdgeExp.Set.t;
    norms: LooperDomain.EdgeExp.Set.t;
    loop_heads: Location.t list;
    loop_modified: LooperDomain.AccessSet.t;
    
    scope_locals: LooperDomain.AccessSet.t list;
    locals: LooperDomain.AccessSet.t;
    formals: Pvar.Set.t;
    type_map: Typ.t LooperDomain.PvarMap.t;
    tenv: Tenv.t;
    analysis_data: LooperDomain.summary InterproceduralAnalysis.t;
    call_summaries: LooperDomain.summary Location.Map.t;

    (* Hack workaround for now *)
    log_file: Utils.outfile;
  }
end


module GraphConstructor : sig
  val create_lts: 
    Tenv.t -> Procdesc.t -> LooperDomain.summary InterproceduralAnalysis.t -> Utils.outfile -> GraphData.t
end