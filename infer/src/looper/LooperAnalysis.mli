(* Author: Ondrej Pavela <xpavel34@stud.fit.vutbr.cz> *)

open! IStd

val analyze_procedure : 
  LooperDomain.summary InterproceduralAnalysis.t -> LooperDomain.summary option