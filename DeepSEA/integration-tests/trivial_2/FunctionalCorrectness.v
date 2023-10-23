Require Import DataTypeOps.
Require Import LayerCONTRACT.

Require Import DeepSpec.lib.Monad.StateMonadOption.
Require Import DeepSpec.lib.Monad.RunStateTInv.
Require Import lib.ArithInv.
Import DeepSpec.lib.Monad.Monad.MonadNotation.

Require Import ZArith.
Require Import cclib.Maps.
Require Import cclib.Integers.

Require Import Lia.

Import core.MemoryModel. 
Section WithMem.
Context {memModelOps : MemoryModelOps mem}.

Open Scope Z.

Theorem boolToIntCorrect : forall d me,
   runStateT (Trivial_boolToInt_opt true me) d = Some (1, d) /\
   runStateT (Trivial_boolToInt_opt false me) d = Some (0, d).
Proof.
  Transparent Trivial_boolToInt_opt.
  split; unfold Trivial_boolToInt_opt; simpl; reflexivity. 
Qed.

End WithMem.