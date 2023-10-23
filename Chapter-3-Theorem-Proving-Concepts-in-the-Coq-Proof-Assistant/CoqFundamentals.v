Require Import Lia.
Require Import String.
Module example.

Inductive nat :=
 | O : nat
 | S : nat -> nat.

Check nat_ind.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Infix "+" := plus.

Lemma plus_O_n : forall x:nat, x = O + x.
Proof.
  reflexivity.
Qed.

Lemma plus_x_O : forall x:nat, x = x + O.
Proof.
intros.
induction x.
- (* Case: P O *)
simpl.
reflexivity.
- (* Case: P x -> P (S x) *)
simpl.
rewrite <- IHx.
reflexivity. 
Qed.

Definition plus_n_O_as_def : forall n:nat, n = n + O.
Proof.
  intros. induction n.
  - (* Case: [P O]. *) reflexivity.
  - (* Case: [P n -> P (S n)]. *) simpl. rewrite <- IHn. reflexivity. 
Qed.

End example.

(** ** Example: Even Numbers *)

Definition Even (n : nat) : Prop :=
  exists m, n = 2 * m.

Fixpoint evenb (n : nat) : bool :=
  match n with
    | 0 => true
    | 1 => false
    | S (S n) => evenb n
  end.

Definition evenb' : nat -> bool :=
  fix evenb' (n:nat) : bool :=
    match n with
    | 0 => true
    | 1 => false
    | S (S n) => evenb' n
  end.

Definition nat_ind_SS
  (P : nat -> Type)
  (ev_0 : P 0)
  (ev_1 : P 1)
  (ev_SS : forall n, P n -> P (S (S n)))
    : forall n, P n := 
    fix nat_ind_SS n :=
      match n with
      | 0 => ev_0
      | 1 => ev_1
      | S (S m) => ev_SS m (nat_ind_SS m)
    end.

Theorem evenb_correct :
  forall n, evenb n = true <-> Even n.
Proof.
split. 
  - (* Case: "->" *)
    induction n using nat_ind_SS. 
    + (* Base case: 0 *)
      exists 0. simpl. reflexivity.
    + (* Base case: 1 *)
      intros.  simpl in H. exfalso. discriminate.
    + (* Inductive case: +2 *) intros. 
      simpl in *. apply IHn in H. 
      unfold Even in H. unfold Even. 
      destruct H. 
      exists (x + 1). 
      rewrite -> H. simpl. 
      lia.
  - (* Case: "<-" *) 
    induction n using nat_ind_SS.
    + (* Base case: 0 *) intros. simpl.  reflexivity.
    + (* Base case: 1 *) intros. destruct H. lia.
    + (* Inductive case: +2 *)
      intros. 
      assert(Even n). { 
        destruct H. 
        destruct x as [|x'] eqn:Case.
        * exfalso. clear -H. simpl in H. discriminate.
        * unfold Even. exists x'. lia.
      }
      apply IHn in H0. simpl. 
      assumption.
Qed.