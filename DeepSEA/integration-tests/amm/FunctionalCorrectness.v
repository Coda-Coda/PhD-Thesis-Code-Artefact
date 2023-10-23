Require Import DataTypeOps.
Require Import LayerAMM.
Require Import LayerAMMLIB.

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

(* Could add proofs here, however the tests currently do not
   involve FunctionalCorrectness.v *)

End WithMem.