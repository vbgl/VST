(* Concurrent Compiler Correcntess *)

(** Prove a simulation between the Clight concurrent semantics and 
    the x86 concurrent semantics.
*)

Require Import VST.concurrency.compiler.HybridMachine_simulation.

(*Clight Machine *)
Require Import VST.concurrency.common.DryMachineSource.
(*Asm Machine*)
Require Import VST.concurrency.common.dry_context.

Require Import VST.concurrency.compiler.concurrent_compiler_simulation.


Section ConcurrentCopmpilerSpecification.
  (*Import the Clight Hybrid Machine*)
  Import THE_DRY_MACHINE_SOURCE.
  Import DMS.

  (*Import the Asm Hybrid Machine*)
  Import AsmContext.
  Context (Clight_g : Clight.genv).
  Context (Asm_g : Clight.genv).

  (*TODO: Define this thing!!! *)
  Context (Asm_semantics : Semantics).


  (* Definition ClightConcurSem := @ClightMachine Clight_g. *)
  Definition AsmHybridMachine    := @dryCoarseMach Asm_semantics.
  Definition AsmConcurSem    := HybridMachineSig.HybridMachineSig.ConcurMachineSemantics
                                  (HybridMachine:= AsmHybridMachine).

  Definition ConcurrentCompilerCorrectness_specification: Type:=
    forall U r,
      HybridMachine_simulation _ _ _ _ _ _ _
                               (ClightConcurSem(ge:=Clight_g) U r) (AsmConcurSem U r).

End ConcurrentCopmpilerSpecification.