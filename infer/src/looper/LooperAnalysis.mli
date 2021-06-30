(* Author: Ondrej Pavela <xpavel34@stud.fit.vutbr.cz> *)

open! IStd

val analyze_procedure : 
  LooperDomain.Summary.t InterproceduralAnalysis.t -> LooperDomain.Summary.t option