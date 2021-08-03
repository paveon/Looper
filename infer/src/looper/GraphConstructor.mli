(* Author: Ondrej Pavela <xpavel34@stud.fit.vutbr.cz> *)


open! IStd
module LTS = LabeledTransitionSystem


type procedure_data = {
  nodes: LTS.NodeSet.t;
  edges: LTS.EdgeSet.t;
  norms: EdgeExp.Set.t;
  formals: AccessPath.BaseSet.t;
  analysis_data: LooperSummary.t InterproceduralAnalysis.t;
  call_summaries: LooperSummary.t Location.Map.t;
  lts: LTS.t
}


val construct: Tenv.t -> Procdesc.t -> LooperSummary.t InterproceduralAnalysis.t -> procedure_data