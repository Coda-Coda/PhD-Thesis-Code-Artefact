Require Import Crowdfunding.DataTypeOps.
Require Import Crowdfunding.LayerCONTRACT.

Require Import DeepSpec.lib.Monad.StateMonadOption.
Require Import DeepSpec.lib.Monad.RunStateTInv.
Require Import lib.ArithInv.
Import DeepSpec.lib.Monad.Monad.MonadNotation.

Require Import Lia.
Require Import List.
Require Import Bool.
Require Import ZArith.
Require Import cclib.Maps.
Require Import cclib.Integers.

Require Import Crowdfunding.DataTypes.
Require Import backend.MachineModel.

Import ListNotations.

Require Import core.MemoryModel. 
Require Import HyperTypeInst.

Require Import Maps.
Import Maps.Int256Tree_Properties.
Import Maps.Int256Tree.

Require Import Crowdfunding.ContractModel.
Import Crowdfunding.ContractModel.ContractModel.

Open Scope Z.

Delimit Scope int256_scope with int256.
Infix "+" := Int256.add : int256_scope.
Infix "-" := Int256.sub : int256_scope.
Infix "=?" := Int256.eq (at level 70, no associativity) : int256_scope.

Lemma fold_snd_map : 
  forall  A B (m : list (A * B)) x f,
  (fold_left (fun (a : B) (p : A * B) => f a (snd p))
   m x) = 
  (fold_left f
  (List.map snd m) x).
Proof.
    intro.
    induction m.
    - intros. simpl. reflexivity.
    - intros. simpl. rewrite IHm. reflexivity.
Qed.

Lemma sum_starting_from_init_equals_sum_plus_init_arbitrary_start : 
forall (x init : Z) (m : Int256Tree.t Z),
Int256Tree.fold1 Z.add m (init + x) = Z.add (Int256Tree.fold1 Z.add m x) init.
Proof.
  intros.
  repeat rewrite Int256Tree.fold1_spec.
  assert(
  forall x,
    (fold_left (fun (a : Z) (p : Int256Tree.elt * Z) => Z.add a (snd p))
    (Int256Tree.elements m) x) = 
    (fold_left Z.add
    (List.map snd (Int256Tree.elements m)) x)).
    {
      intros.
      apply fold_snd_map.
    }
  repeat rewrite H. clear H.
  rewrite <- fold_left_last.
  repeat rewrite fold_symmetric; try (intros; lia).
  remember (List.map snd (Int256Tree.elements m)) as l.
  clear Heql. clear m. generalize dependent l.
  induction l.
    - simpl. lia.
    - simpl.
    rewrite IHl.
    reflexivity.
Qed.

Lemma sum_starting_from_init_equals_sum_plus_init : 
forall (init : Z) (m : Int256Tree.t Z),
Int256Tree.fold1 Z.add m init = Z.add (Int256Tree.fold1 Z.add m 0) init.
Proof.
  intros.
  rewrite <- sum_starting_from_init_equals_sum_plus_init_arbitrary_start.
  rewrite Z.add_0_r.
  reflexivity.
Qed.

Lemma Int256Tree_sum_set_value_initially_zero : 
  forall (m: Int256Tree.t Z32)  k v, Int256Tree.get_default 0 k m = 0
                -> Int256Tree_Properties.sum (Int256Tree.set k v m) = 
                   Int256Tree_Properties.sum m + v.
Proof.
  unfold Z32.
  intros.
  pose (@Int256Tree_Properties.sum_get_default 0 k v (Int256Tree.set k v m)) as Lemma1.
  simpl in Lemma1.
  unfold Int256Tree_Properties.sum.
  rewrite Lemma1; [|  unfold Int256Tree.get_default;
                      rewrite Int256Tree.gss;
                      reflexivity].
  rewrite Int256Tree_Properties.fold1_remove_set; [|intros; lia].
  unfold Int256Tree.get_default in H.

  destruct (Int256Tree.get k m) eqn:Case.
  - rewrite H in Case.
     assert(Zswap : forall x y a : Z, a + x + y = a + y + x) by (intros; lia).
     epose (Int256Tree_Properties.fold1_get Z.add Zswap v Case) as H0.
     rewrite Z.add_0_r in H0.
     rewrite <- H0.
     pose Int256Tree_Properties.sum_extensional.
     apply sum_starting_from_init_equals_sum_plus_init.
   - 
   assert(Int256Tree.get_default 0 k m = 0).
   unfold Int256Tree.get_default.
   rewrite Case. reflexivity. 
   pose (@Int256Tree_Properties.sum_get_default v k 0 m H0).
   rewrite Z.add_0_r in e.
   rewrite <- e.
   apply sum_starting_from_init_equals_sum_plus_init.
Qed.

Lemma sum_set_y_remove_from_starting_x : 
  forall k m x y,
  Int256Tree.fold1 Z.add (Int256Tree.set k y m) x =
  Int256Tree.fold1 Z.add (Int256Tree.remove k m) x + y.
Proof.
  intros.
  pose (Int256Tree.grs k m).
  pose (Int256Tree_Properties.set_permutation 0 e).
  rewrite <- Int256Tree_Properties.elements_set_decompose in p.
  rewrite fold1_set by lia.
  rewrite sum_starting_from_init_equals_sum_plus_init.
  symmetry.
  rewrite sum_starting_from_init_equals_sum_plus_init.
  rewrite Z.add_assoc.
  reflexivity.
Qed.

Lemma sum_set_zero_remove_from_starting_x : 
  forall k m x,
  Int256Tree.fold1 Z.add (Int256Tree.set k 0 m) x =
  Int256Tree.fold1 Z.add (Int256Tree.remove k m) x.
Proof.
  intros.
  rewrite sum_set_y_remove_from_starting_x.
  rewrite Z.add_0_r.
  reflexivity.
Qed.

Lemma sum_set_zero_remove : 
  forall k m,
  Int256Tree.fold1 Z.add (Int256Tree.set k 0 m) 0 =
  Int256Tree.fold1 Z.add (Int256Tree.remove k m) 0.
Proof.
  intros.
  apply sum_set_zero_remove_from_starting_x.
Qed.

Lemma sum_set_x_minus_from_arbitrary_init : 
  forall (k : elt) (m : t Z) (v x init : Z),
  get_default 0 k m = v ->
  fold1 Z.add (set k x m) init = fold1 Z.add m init + (x - v).
Proof.
unfold sum.
  intros.
  unfold Int256Tree_Properties.sum.
  unfold Int256Tree.get_default in H.
  destruct (Int256Tree.get k m) eqn:Case.
    - subst.
      assert((forall x y a : Z, a + x + y = a + y + x)) by (intros; lia).
      epose (Int256Tree_Properties.fold1_get Z.add H init Case).
      rewrite e.
      simpl.
      assert (init + v = v + init) by apply Z.add_comm.
      rewrite H0. clear H0.
      rewrite (sum_starting_from_init_equals_sum_plus_init_arbitrary_start init).
      rewrite sum_set_y_remove_from_starting_x.
      lia.
    - subst.
      assert((forall x y a : Z, a + x + y = a + y + x)) by (intros; lia).
      simpl.
      rewrite Z.sub_0_r.
      rewrite sum_set_y_remove_from_starting_x.
      assert(get_default 0 k m = 0). unfold get_default. rewrite Case. reflexivity.
      pose proof (@sum_get_default init k 0 m H0).
      rewrite Z.add_0_r in H1.
      rewrite <- H1.
      reflexivity.
Qed.

Lemma sum_set_zero_minus_from_arbitrary_init : 
  forall (k : elt) (m : t Z) (v init : Z),
  get_default 0 k m = v ->
  fold1 Z.add (set k 0 m) init = fold1 Z.add m init - v.
Proof.
intros.
apply sum_set_x_minus_from_arbitrary_init; assumption.
Qed.

Lemma sum_set_zero_minus : forall k m v, Int256Tree.get_default 0 k m = v ->
    Int256Tree_Properties.sum (Int256Tree.set k 0 m)
  = Int256Tree_Properties.sum m - v.
Proof.
  intros.
  unfold sum.
  apply sum_set_zero_minus_from_arbitrary_init.
  assumption.
Qed.

Lemma Int256Tree_sum_minus_equality : 
  forall m k x,
    Int256Tree_Properties.sum m >= x ->
      Int256Tree_Properties.sum (Int256Tree.set k 0 m) 
    = (Int256Tree_Properties.sum m) - (Int256Tree.get_default 0 k m).
Proof.
intros.
unfold sum.
rewrite sum_set_zero_minus_from_arbitrary_init with (v:= Int256Tree.get_default 0 k m) by reflexivity.
reflexivity.
Qed.

Lemma Int256Tree_sum_minus_from_starting_x :
  forall (m : t Z) (k : elt) (x : Z),
      fold1 Z.add (set k 0 m) x =
      fold1 Z.add m x - get_default 0 k m.
Proof.
  intros.
  rewrite sum_set_zero_minus_from_arbitrary_init with (v:= Int256Tree.get_default 0 k m) by reflexivity.
  reflexivity.
Qed.

Lemma Int256Tree_sum_minus : 
  forall m k x,
    Int256Tree_Properties.sum m <= x
    ->
       Int256Tree_Properties.sum (Int256Tree.set k 0 m)
    <= x - (Int256Tree.get_default 0 k m).
Proof.
intros.
rewrite sum_set_zero_minus with (v:= Int256Tree.get_default 0 k m) by reflexivity.
lia.
Qed.

Lemma addZeroBalance : forall sender recipient balances a,
  update_balances sender recipient 0 balances a = balances a.
Proof.
  intros.
  unfold update_balances.
  destruct (Int256.eq sender recipient).
  - reflexivity.
  - destruct (Int256.eq a sender) eqn:Case.
    + rewrite Z.sub_0_r.
    apply Int256eq_true in Case. subst.
    reflexivity.
    + destruct (Int256.eq a recipient) eqn:SCase.
      * rewrite Z.add_0_r.
        apply Int256eq_true in SCase. subst.
        reflexivity.
      * reflexivity.
Qed.

(* To see the NoLeftoverOutgoings lemma, please see line 579 of Chapter-5-Case-Study-Crowdfunding/proofs/Crowdfunding.v:
   https://github.com/Coda-Coda/PhD-Thesis-Code-Artefact/blob/main/Chapter-5-Case-Study-Crowdfunding/proofs/Crowdfunding.v#L579 *)

Ltac me_transfer_cases :=
  try match goal with
    H : (Int256.one =? Int256.one)%int256 = false |- _ => 
      rewrite Int256.eq_true in H; discriminate
      end;
  try match goal with
    H : runStateT mzero _ = ret _ |- _ => 
    simpl in H; discriminate
  end.

Ltac ds_inv :=
  repeat ( try inv_runStateT_branching;
           let Case := fresh "NoOverflowOrUnderflowInTransferCase" in
           try match goal with | H : context[me_transfer _  _ _] |- _ => 
             unfold me_transfer, make_machine_env in H;
             destruct (noOverflowOrUnderflowInTransfer _ _ _ _ && (_ _ _ _ _)) eqn:Case
           end );
  me_transfer_cases.

(* To see the HLinks tactic, please see line 636 of Chapter-5-Case-Study-Crowdfunding/proofs/Crowdfunding.v:
   https://github.com/Coda-Coda/PhD-Thesis-Code-Artefact/blob/main/Chapter-5-Case-Study-Crowdfunding/proofs/Crowdfunding.v#L636 *)