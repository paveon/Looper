(* Author: Ondrej Pavela <xpavel34@stud.fit.vutbr.cz> *)


open! IStd
module DCP = DifferenceConstraintProgram


module GraphData : sig
  type t = {
    last_node: DCP.Node.t;
    loophead_stack: Procdesc.Node.t Stack.t;
    nodes: DCP.NodeSet.t;
    edges: DCP.EdgeSet.t;
    edge_data: DCP.EdgeData.t;
    ident_map: EdgeExp.t Ident.Map.t;
    node_map: DCP.Node.t Procdesc.NodeMap.t;
    potential_norms: EdgeExp.Set.t;
    norms: EdgeExp.Set.t;
    loop_heads: Location.t list;
    loop_modified: LooperUtils.AccessSet.t;
    
    scope_locals: LooperUtils.AccessSet.t list;
    locals: LooperUtils.AccessSet.t;
    formals: Pvar.Set.t;
    type_map: Typ.t LooperUtils.PvarMap.t;
    tenv: Tenv.t;
    analysis_data: LooperSummary.t InterproceduralAnalysis.t;
    call_summaries: LooperSummary.t Location.Map.t;
  }
end


module GraphConstructor : sig
  val create_lts: Tenv.t -> Procdesc.t -> LooperSummary.t InterproceduralAnalysis.t -> GraphData.t
end