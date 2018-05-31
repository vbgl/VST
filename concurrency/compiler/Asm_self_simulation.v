Require Import compcert.x86.Asm.

Require Import VST.concurrency.compiler.self_simulation.

Definition Asm_self_simulation tp:
  self_simulation (Asm.semantics tp) _ State.
(*ia32.Asm.get_mem*)
Admitted.

