Require Import Lia.
Require Import NArith.
Require Import List.
Import ListNotations.
Section Refinement.

(** ** Layer 2: Expression Trees with Unary Natural Numbers *)

Inductive L2_op :=
  | L2Const (n : nat)
  | L2ReadX
  | L2WriteX (ops1 ops2 : L2_op)
  | L2Add (ops1 ops2 : L2_op)
  | L2Sub (ops1 ops2 : L2_op)
  | L2Mul (ops1 ops2 : L2_op).

Definition example_L2 := (L2WriteX
                           (L2Mul
                             (L2Const 2)
                             L2ReadX )
                           (L2Add
                             L2ReadX 
                             (L2Const 4))).

Open Scope nat.

Fixpoint eval_L2_op (ops : L2_op) (x : nat) : nat :=
  match ops with
    | L2Const n => n
    | L2ReadX => x
    | L2WriteX ops1 ops2 => (eval_L2_op ops2 (eval_L2_op ops1 x))
    | L2Add ops1 ops2 => (eval_L2_op ops1 x) + (eval_L2_op ops2 x)
    | L2Sub ops1 ops2 => (eval_L2_op ops1 x) - (eval_L2_op ops2 x)
    | L2Mul ops1 ops2 => (eval_L2_op ops1 x) * (eval_L2_op ops2 x)
  end.
Close Scope nat.

Open Scope nat.
Eval compute in (eval_L2_op example_L2 1).
Eval compute in (eval_L2_op example_L2 3).
Close Scope nat.

Definition L1_op := nat -> nat.

Definition eval_L1_op (f : L1_op) (x : nat) := f x.

Open Scope nat.
Fixpoint synth_L1_op (ops : L2_op) : L1_op :=
  match ops with
    | L2Const n => fun x => n
    | L2ReadX => fun x => x
    | L2WriteX ops1 ops2 => fun x => let xNew := (eval_L1_op (synth_L1_op ops1) x) in (eval_L1_op (synth_L1_op ops2) xNew)
    | L2Add ops1 ops2 => fun x => (eval_L1_op (synth_L1_op ops1) x) + (eval_L1_op (synth_L1_op ops2) x)
    | L2Sub ops1 ops2 => fun x => (eval_L1_op (synth_L1_op ops1) x) - (eval_L1_op (synth_L1_op ops2) x)
    | L2Mul ops1 ops2 => fun x => (eval_L1_op (synth_L1_op ops1) x) * (eval_L1_op (synth_L1_op ops2) x)
  end.
Close Scope nat.

Open Scope nat.
Opaque Nat.add Nat.sub Nat.mul.
Goal synth_L1_op example_L2 = synth_L1_op example_L2.
remember (synth_L1_op example_L2) as example.
rewrite Heqexample at 2.
unfold example_L2.
repeat (cbv beta delta fix; cbv match).
rewrite Heqexample. (* See goal here *)
reflexivity.
Close Scope nat.
Qed.
Transparent Nat.add Nat.sub Nat.mul.

(** ** Layer 1-2 Refinement: Coq Functions to Expression Trees *)

Definition input_relation_L1L2 (L1x L2x : nat) : Prop := L1x = L2x.
Definition result_relation_L1L2 (L1x L2x : nat) : Prop := L1x = L2x.

Lemma refinement_proof_L1L2 : 
  forall (ops : L2_op) L1x L2x (ValidInit : input_relation_L1L2 L1x L2x),
    result_relation_L1L2 (eval_L1_op (synth_L1_op ops) L1x) (eval_L2_op ops L2x).
Proof.
  induction ops.
  - intros; unfold result_relation_L1L2, synth_L1_op, eval_L1_op, eval_L2_op; simpl; reflexivity.
  - intros; unfold result_relation_L1L2, synth_L1_op, eval_L1_op, eval_L2_op, input_relation_L1L2 in *; simpl; assumption.
  - intros; unfold input_relation_L1L2 in *;
    simpl; unfold eval_L1_op; unfold result_relation_L1L2; simpl.
    apply IHops2; apply IHops1; assumption.
  - intros;
    unfold input_relation_L1L2, result_relation_L1L2, eval_L1_op in *;  subst; simpl; unfold eval_L1_op in *; simpl.
    rewrite <- (IHops1 L2x) by reflexivity;
    rewrite <- (IHops2 L2x) by reflexivity; simpl.
    reflexivity.
  -
    intros; 
    unfold input_relation_L1L2, result_relation_L1L2, eval_L1_op in *; subst;
    simpl;
    rewrite <- (IHops1 L2x) by reflexivity;
    rewrite <- (IHops2 L2x) by reflexivity;
    reflexivity.
  -
    intros; 
    unfold input_relation_L1L2, result_relation_L1L2, eval_L1_op in *; subst;
    simpl;
    rewrite <- (IHops1 L2x) by reflexivity;
    rewrite <- (IHops2 L2x) by reflexivity;
    reflexivity.
Qed.

(** ** Layer 3: Expression Trees with Binary Natural Numbers *)

Print nat.
Print N.
Print positive.

Inductive L3_op :=
  | L3Const (n : N)
  | L3ReadX
  | L3WriteX (ops1 ops2 : L3_op)
  | L3Add (ops1 ops2 : L3_op)
  | L3Sub (ops1 ops2 : L3_op)
  | L3Mul (ops1 ops2 : L3_op).

Fixpoint synth_L3_op (ops : L2_op) : L3_op := 
  match ops with
  | L2Const n => L3Const (N.of_nat n)
  | L2ReadX => L3ReadX
  | L2WriteX ops1 ops2 => L3WriteX (synth_L3_op ops1) (synth_L3_op ops2)
  | L2Add ops1 ops2 => L3Add (synth_L3_op ops1) (synth_L3_op ops2)
  | L2Sub ops1 ops2 => L3Sub (synth_L3_op ops1) (synth_L3_op ops2)
  | L2Mul ops1 ops2 => L3Mul (synth_L3_op ops1) (synth_L3_op ops2)
  end.

Eval compute in (synth_L3_op example_L2).

Open Scope N.
Fixpoint eval_L3_op (ops : L3_op) (x : N) : N :=
  match ops with
    | L3Const n => n
    | L3ReadX => x
    | L3WriteX ops1 ops2 => (eval_L3_op ops2 (eval_L3_op ops1 x))
    | L3Add ops1 ops2 => (eval_L3_op ops1 x) + (eval_L3_op ops2 x)
    | L3Sub ops1 ops2 => (eval_L3_op ops1 x) - (eval_L3_op ops2 x)
    | L3Mul ops1 ops2 => (eval_L3_op ops1 x) * (eval_L3_op ops2 x)
  end.
Close Scope N.

(** ** Layer 2-3 Refinement: Unary Natural Numbers to their Binary Representation *)

Definition input_relation_L2L3 L2x L3x : Prop := N.of_nat L2x = L3x.
Definition result_relation_L2L3 L2x L3x : Prop := N.of_nat L2x = L3x.

Lemma refinement_proof_L2L3 : 
  forall (ops : L2_op) L2x L3x (ValidInit : input_relation_L2L3 L2x L3x),
    result_relation_L2L3 (eval_L2_op ops L2x) (eval_L3_op (synth_L3_op ops) L3x).
  Proof.
    induction ops.
    - intros; unfold result_relation_L2L3, synth_L1_op, eval_L3_op; simpl; reflexivity.
    - intros; unfold result_relation_L2L3, synth_L1_op, eval_L3_op, input_relation_L2L3 in *; simpl. 
    assumption.
    - intros; unfold input_relation_L1L2 in *;
      simpl.
      pose proof (IHops1 _ _ ValidInit);
      pose proof (IHops2 _ _ H);
      assumption.
      - intros;
      unfold input_relation_L2L3, result_relation_L2L3;
      simpl.
      rewrite Nat2N.inj_add.
      rewrite <- (IHops1 L2x) by assumption;
      rewrite <- (IHops2 L2x) by assumption;
      reflexivity.
    - intros;
      unfold input_relation_L2L3, result_relation_L2L3;
      simpl.
      rewrite Nat2N.inj_sub;
      rewrite <- (IHops1 L2x) by assumption;
      rewrite <- (IHops2 L2x) by assumption;
      reflexivity.
    - intros;
      unfold input_relation_L2L3, result_relation_L2L3;
      simpl.
      rewrite Nat2N.inj_mul;
      rewrite <- (IHops1 L2x) by assumption;
      rewrite <- (IHops2 L2x) by assumption;
      reflexivity.
Qed.

(** ** Layer 4: Stack Machine with Binary Natural Numbers *)

Inductive L4_cmd :=
  | L4Const (l : N)
  | L4ReadX
  | L4WriteXStart
  | L4WriteXEnd
  | L4Add
  | L4Sub
  | L4Mul.

Definition L4_op := list L4_cmd.
Definition stack := list N.

Fixpoint synth_L4_op (n : L3_op) (ops : L4_op) : L4_op := 
  match n with
  | L3Const l => (L4Const l) :: ops
  | L3ReadX => L4ReadX :: ops
  | L3WriteX ops1 ops2 => (synth_L4_op ops1 []) ++ [L4WriteXStart] ++ (synth_L4_op ops2 []) ++ [L4WriteXEnd] ++  ops
  | L3Add ops1 ops2 => (synth_L4_op ops2 []) ++ (synth_L4_op ops1 []) ++ [L4Add] ++ ops
  | L3Sub ops1 ops2 => (synth_L4_op ops2 []) ++ (synth_L4_op ops1 []) ++ [L4Sub] ++ ops
  | L3Mul ops1 ops2 => (synth_L4_op ops2 []) ++ (synth_L4_op ops1 []) ++ [L4Mul] ++ ops
  end.

Open Scope N.

Fixpoint eval_L4_op (ops : L4_op) (s : stack) (xVals : stack) : option stack :=
  match ops with
    | h :: tl =>
    match h with
      | L4Const l => eval_L4_op tl ((l :: s)) xVals
      | L4ReadX => 
        match xVals with 
          | x :: xs => eval_L4_op tl ((x :: s)) xVals
          | _ => None
        end
      | L4WriteXStart => 
        match s with
        | x' :: tl2 => eval_L4_op tl tl2 (x' :: xVals)
        | [] => None
        end
      | L4WriteXEnd => 
        match xVals with
        | x' :: tl2 => eval_L4_op tl s tl2
        | [] => None
        end
      | L4Add =>
        match s with
        | h1 :: h2 :: tl2 => eval_L4_op tl (((h1 + h2) :: tl2)) xVals
        | _ => None
        end
      | L4Sub =>
        match s with
        | h1 :: h2 :: tl2 => eval_L4_op tl (((h1 - h2) :: tl2)) xVals
        | _ => None
        end
      | L4Mul =>
        match s with
        | h1 :: h2 :: tl2 => eval_L4_op tl (((h1 * h2) :: tl2)) xVals
        | _ => None
        end
    end
    | [] => Some s
  end.
Close Scope N.

(** ** Layer 3-4 Refinement: Expression Trees to Stack Machine *)

Definition input_relation_L3L4  (L3x : N) (L4x : stack) : Prop := [L3x] = L4x.
Definition result_relation_L3L4 (L3x : N) (L4x : option stack) : Prop := Some [L3x] = L4x.

Lemma refinement_proof_helper : forall (ops : L3_op) additionalOps s x xs,
    eval_L4_op additionalOps ((eval_L3_op ops x) :: s) (x::xs) 
  = eval_L4_op (synth_L4_op ops [] ++ additionalOps) s (x::xs).
Proof.
  induction ops.
  - reflexivity.
  - reflexivity.
  - intros.
  unfold synth_L4_op, synth_L3_op;
  fold synth_L4_op; fold synth_L3_op;
  repeat rewrite app_assoc_reverse.
  rewrite <- IHops1. simpl.
  rewrite <- IHops2. simpl.
  reflexivity.
- intros.
unfold synth_L4_op, synth_L3_op;
fold synth_L4_op; fold synth_L3_op;
repeat rewrite app_assoc_reverse.
rewrite <- IHops2. simpl.
rewrite <- IHops1. simpl.
reflexivity.
- intros.
unfold synth_L4_op, synth_L3_op;
fold synth_L4_op; fold synth_L3_op;
repeat rewrite app_assoc_reverse.
rewrite <- IHops2. simpl.
rewrite <- IHops1. simpl.
reflexivity.
- intros.
unfold synth_L4_op, synth_L3_op;
fold synth_L4_op; fold synth_L3_op;
repeat rewrite app_assoc_reverse.
rewrite <- IHops2. simpl.
rewrite <- IHops1. simpl.
reflexivity.
Qed.

Lemma refinement_proof_L3L4 :
  forall (ops : L3_op) Ax Cx (ValidInit : input_relation_L3L4 Ax Cx),
    result_relation_L3L4
      (eval_L3_op (ops) Ax)
      (eval_L4_op (synth_L4_op (ops) []) [] Cx).
Proof.
  intros. 
  unfold input_relation_L3L4, result_relation_L3L4 in *. subst.
  pose proof (refinement_proof_helper ops [] [] Ax []) as helper.
  simpl in *.
  rewrite app_nil_r in helper.
  assumption.
Qed.

(** ** Layer 1-4 Stepwise Refinement: Coq Functions (Unary) to Stack Machine (Binary) *)

Definition result_relation_L1L4 l1 l4 := exists l2 l3, (result_relation_L1L2 l1 l2) /\ (result_relation_L2L3 l2 l3) /\ (result_relation_L3L4 l3 l4).

Theorem stepwise_refinement_proof : 
  forall (ops : L2_op) L1x L2x L3x L4x
    (ValidInit12 : input_relation_L1L2 L1x L2x)
    (ValidInit23 : input_relation_L2L3 L2x L3x)
    (ValidInit34 : input_relation_L3L4 L3x L4x),
      result_relation_L1L4
        (eval_L1_op (synth_L1_op ops) L1x)
        (eval_L4_op (synth_L4_op (synth_L3_op ops) []) [] L4x).
Proof.
  intros.
  unfold input_relation_L1L2, input_relation_L2L3,
         input_relation_L3L4, result_relation_L1L4 in *.
  exists (eval_L2_op ops L2x).
  exists (eval_L3_op (synth_L3_op ops) L3x).
  split; [|split].
  - apply refinement_proof_L1L2; assumption.
  - apply refinement_proof_L2L3; assumption.
  - apply refinement_proof_L3L4; assumption.
  Qed.

Close Scope N.

(** ** Proving a Property of a Simple Arithmetic Expression *)

Open Scope nat.
Opaque Nat.add Nat.sub Nat.mul.
Goal synth_L1_op example_L2 = synth_L1_op example_L2.
remember (synth_L1_op example_L2) as example.
rewrite Heqexample at 2.
unfold example_L2.
repeat (cbv beta delta fix; cbv match).
rewrite Heqexample. (* See goal *)
reflexivity.
Close Scope nat.
Qed.
Transparent Nat.add Nat.sub Nat.mul.

Open Scope nat.
Definition Even (n : nat) : Prop :=
  exists m, n = 2 * m.

Lemma Even_example_L2_proof : forall x, Even (eval_L1_op (synth_L1_op example_L2) x).
Proof.
  intros; unfold synth_L1_op, eval_L1_op, example_L2, Even.
  exists (x + 2). (* .no-hyps .out *)
  lia.
Qed.

Definition ValidL4x (L4x : stack) :=
  match L4x with
    | [_] => True
    | _ => False
  end.

Lemma result_relation_L1_L4_helper : forall L1 L1' L4, 
      result_relation_L1L4 L1 L4
  ->  result_relation_L1L4 L1' L4
  -> L1 = L1'.
Proof.
  intros. 
  unfold result_relation_L1L4 in *.
  destruct H as [L2x [L3x]].
  destruct H0 as [L2x' [L3x']].
  destruct H as [H12 [H23 H34]].
  destruct H0 as [H12' [H23' H34']].
  unfold result_relation_L1L2 in *.
  unfold result_relation_L2L3 in *.
  unfold result_relation_L3L4 in *.
  subst.
  inversion H34'.
  apply Nat2N.inj in H0; auto.
Qed.

Theorem Even_example_L2 : 
forall L4x,
  ValidL4x L4x ->
forall result,
  result_relation_L1L4
    result
    (eval_L4_op (synth_L4_op (synth_L3_op example_L2) []) [] L4x)
-> Even result.
Proof.
  intros. 
  destruct L4x. 
  contradiction. 
  destruct L4x; [|contradiction]. 
  assert(input_relation_L1L2 (N.to_nat n) (N.to_nat n)) as H12 by 
  reflexivity.
  assert (input_relation_L2L3 (N.to_nat n) n) as H23. 
  unfold input_relation_L2L3. 
  apply N2Nat.id. 
  assert (input_relation_L3L4 n [n]) as H34 by reflexivity. 
  pose proof (stepwise_refinement_proof example_L2 (N.to_nat n) (N.to_nat n)  n [n]) H12 H23 H34.
  clear H12 H23 H34. 
  pose proof (result_relation_L1_L4_helper _ _ _ H0 H1).
  rewrite H2.
  apply Even_example_L2_proof.
Qed.

(** ** Verified Compilation of Simple Arithmetic Expressions *)

Definition compile (ops : L2_op) := synth_L4_op (synth_L3_op ops) [].

Open Scope nat.
Eval compute in compile example_L2.
Close Scope nat.

End Refinement.