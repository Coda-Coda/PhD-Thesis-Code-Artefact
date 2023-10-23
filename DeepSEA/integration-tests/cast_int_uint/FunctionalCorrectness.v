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

Theorem eq_correct_one_direction : forall i u d d' me b,
   runStateT (Contract_eq_opt i u me) d = Some (b, d') ->
   i = Int256.unsigned u ->
   u = Int256.repr i ->
   b = true.
Proof.
  intros.
  Transparent Contract_eq_opt. unfold Contract_eq_opt in H.
  inv_runStateT_branching.
  Search Int256.eq "=".
  destruct u.
  simpl in *. subst.
  apply andb_true_intro.
  split.
  apply Z.eqb_refl.
  rewrite H1.
  apply Int256.eq_true.
Qed.

End WithMem.