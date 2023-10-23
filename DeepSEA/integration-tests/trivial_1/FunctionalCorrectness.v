Require Import DataTypeOps.
Require Import LayerCONTRACT.

Require Import DeepSpec.lib.Monad.StateMonadOption.
Require Import DeepSpec.lib.Monad.RunStateTInv.
Require Import lib.ArithInv.
Import DeepSpec.lib.Monad.Monad.MonadNotation.

Require Import ZArith.
Require Import cclib.Maps.
Require Import cclib.Integers.


Import core.MemoryModel. 
Section WithMem.
Context {memModelOps : MemoryModelOps mem}.

Open Scope Z.

Theorem boolToIntCorrect : forall d me,
   runStateT (Trivial_trivial_opt me) d = Some (tt, d).
Proof.
  Transparent Trivial_trivial_opt.
  unfold Trivial_trivial_opt; simpl; reflexivity. 
Qed.

End WithMem.