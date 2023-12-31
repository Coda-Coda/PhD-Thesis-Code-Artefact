(* This may need to be changed quite a bit, see the readme file. 

*)

(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** This module defines the type of values that is used in the dynamic
  semantics of all our intermediate languages. *)

Require Import cclib.Coqlib.
Require Import cclib.Integers.
Require Import cclib.Maps.
Require Import backend.AST.
Require Import backend.IndexLib.
Require Import backend.Values.LowValues.


(* we want maps that are initialized to 0 by default,
which requires an IMap instead of a PTree *)
Module IdentIndexed <: INDEXED_TYPE.

Definition t := positive.
Definition index (i: positive) : positive := i.
Definition index_inv (i: positive) : positive := i.

Lemma index_invertible : forall x, index_inv (index x) = x.
Proof. reflexivity. Qed.

Lemma index_inj: forall (x y: positive), index x = index y -> x = y.
Proof.
simpl. intros x y H. exact H.
Qed.
Definition eq := peq.

End IdentIndexed.

Module IdentMap := IMap(IdentIndexed).

(* Extended identifier,
so a single identifier (i.e. array name)
can refer to multiple values *)

Section ExtendedIdent.

  (*Extended Ident 2:
    An extended identifier has a base that is either Global or Local,
    with a positive integer used to distinguish local contexts. From
    the base new extended identifiers are generated by indexing into
    an array or accessing an identifier as a field in a struct (treating
    top-level variables as fields as well.) *)
  
  Inductive ident_ext : Type :=
  | Global: ident_ext
  | Local:  int256 -> ident_ext
  | Field: ident_ext -> ident -> ident_ext
  | Index: ident_ext -> int256 -> ident_ext
  .

End ExtendedIdent.

(* Allow extended identifiers to be used as the index of a map. *)
Module IdentExtIndexed <: INDEXED_TYPE.

  Definition t := ident_ext.

  Fixpoint index (eid : ident_ext) : positive :=
    match eid with
    | Global => xH
    | Local ctx => int_index ctx
    | Field eid id => inject_positive (index eid) id
    | Index eid i => inject_positive (index eid) (int_index i)
    end.

Definition index_inv (p : positive) : ident_ext.
Admitted.

Lemma index_invertible : forall x, index_inv (index x) = x.
Admitted.

Lemma index_inj: forall (x y: ident_ext), index x = index y -> x = y.
Proof.
Admitted.
(*  induction x; intro y; destruct y; try discriminate.
-
  unfold index. intro H; injection H; clear H.
  intro H; rewrite H; reflexivity.
-
  simpl. intro H; injection H; clear H.
  intro.
  assert ((index x)=(index y)).
  apply injective_positive_1 with (int_index i) (int_index i0). exact H.
  replace y with x.
  assert ((int_index i)=(int_index i0)).
  apply injective_positive_2 with (index x) (index y). exact H. clear H.
  replace i0 with i.
  reflexivity.
  apply int_index_injective; assumption.
  apply IHx; assumption.
Qed.*)

Lemma eq: forall (x y: ident_ext), {x = y} + {x <> y}.
Proof.
  induction x; destruct y; intros; decide equality;
  try decide equality; try apply Int256.eq_dec;
    try apply Pos.eq_dec.
Qed.

End IdentExtIndexed.

Module IdentExtMap := IMap(IdentExtIndexed).

(* `ident_ext_extends i1 i2` is true if `i2` is of the form
   `Ihash (Ihash ... i1 ... ofs') ofs`. In other words, i2
    designates a sub-part of the object located at i1. *)
Inductive ident_ext_extends : forall (i1 i2 : ident_ext), Prop :=
| IIE_refl : forall eid, ident_ext_extends eid eid
| IIE_index : forall eid1 eid2 i,
    ident_ext_extends eid1 eid2 ->
    ident_ext_extends eid1 (Index eid2 i)
| IIE_field : forall eid1 eid2 id,
    ident_ext_extends eid1 eid2 ->
    ident_ext_extends eid1 (Field eid2 id).

Definition ident_ext_extends_inversion': forall i i2,
    ident_ext_extends i i2 ->
    forall i1 o f, (i = (Index i1 o) \/ i = (Field i1 f)) ->
    ident_ext_extends i1 i2.
Proof.                      
  induction 1; destruct 1; subst; constructor. 
  - constructor.
  - constructor.
  - unshelve (eapply IHident_ext_extends; eauto); (exact (1%positive) || exact Int256.zero).
  - unshelve (eapply IHident_ext_extends; eauto); (exact (1%positive) || exact Int256.zero).
  - unshelve (eapply IHident_ext_extends; eauto); (exact (1%positive) || exact Int256.zero).
  - unshelve (eapply IHident_ext_extends; eauto); (exact (1%positive) || exact Int256.zero).
Qed.    

Lemma ident_ext_extends_inversion_Index: forall i1 i2 o,
    ident_ext_extends (Index i1 o) i2 ->
    ident_ext_extends i1 i2.
Proof.                      
  intros; eapply ident_ext_extends_inversion' with (f:= 1%positive); eauto.
Qed.

Lemma ident_ext_extends_inversion_Field: forall i1 i2 f,
    ident_ext_extends (Field i1 f) i2 ->
    ident_ext_extends i1 i2.
Proof.                      
  intros; eapply ident_ext_extends_inversion' with (o := Int256.zero); eauto.
Qed.

Fixpoint ident_ext_length i :=
  match i with
  | Global => O
  | Local _ => O
  | Field i _ => S (ident_ext_length i)
  | Index i _ => S (ident_ext_length i)
  end.

Lemma ident_ext_extends_longer : forall i j,
    ident_ext_extends i j ->
    (ident_ext_length i <= ident_ext_length j)%nat.
Proof.
  induction 1; simpl; lia.
Qed.

Lemma ident_ext_extends_disjoint_Index : forall o1 o2,
    o1 <> o2 ->
    forall i' i0,
    ident_ext_extends (Index i0 o1) i' ->
    ~ ident_ext_extends (Index i0 o2) i'.
Proof.
  intros o1 o2 Hneq.
  unfold not.
  induction i'; intros i0 H1 H2.
  - inversion H1.
  - inversion H1.
  - inversion H1; inversion H2; subst.
    apply IHi' with i0; auto.
  - inversion H1; inversion H2; subst.
    + congruence.
    + apply ident_ext_extends_longer in H6.
      simpl in H6.
      lia.
    + apply ident_ext_extends_longer in H3.
      simpl in H3.
      lia.
    + unfold not in IHi'; eapply IHi'; eassumption.
Qed.

Fixpoint ident_ext_base (eid : ident_ext) : ident :=
  match eid with
  | Field Global id => id
  | Field (Local _) id => id
  | Field eid _ => ident_ext_base eid
  | Index eid _ => ident_ext_base eid
  | Global => 1%positive  (* dummy, should not happen *)
  | Local _ => 1%positive  (* dummy, should not happen *)
  end.



Section HValue.

  (** A high value extends low values with extended-identifier pointers: *)
  Inductive val : Type :=
  | Vunit: val
  | Vint: int256 -> val
  | Vptr: lval -> val
  | Vhash: val -> val
  | Vhash2: val -> val -> val
  with lval :=
  | LVeid: ident_ext -> lval
  | LVhash: int256 -> lval
  | LVhash2: lval -> int256 -> lval.

  Definition Vzero: val := Vint Int256.zero.
  Definition Vone: val := Vint Int256.one.
  Definition Vmone: val := Vint Int256.mone.

  Definition Vtrue: val := Vint Int256.one.
  Definition Vfalse: val := Vint Int256.zero.

  Fixpoint OfLow (v:LowValues.val) : val :=
    match v with
    | LowValues.Vunit => Vunit
    | LowValues.Vint i => Vint i
    | LowValues.Vhash v => Vhash (OfLow v)
    | LowValues.Vhash2 v1 v2 => Vhash2 (OfLow v1) (OfLow v2)
    end.

  Fixpoint ToLowErr (v:val) : option LowValues.val :=
    match v with
    | Vunit => Some LowValues.Vunit
    | Vint i => Some (LowValues.Vint i)
    | Vhash v => option_map LowValues.Vhash (ToLowErr v) 
    | Vhash2 v1 v2 =>
      match ToLowErr v1, ToLowErr v2 with
      | Some v1', Some v2' => Some (LowValues.Vhash2 v1' v2')
      | _,_ => None
      end
    | Vptr _ => None
    end.
  
End HValue.
