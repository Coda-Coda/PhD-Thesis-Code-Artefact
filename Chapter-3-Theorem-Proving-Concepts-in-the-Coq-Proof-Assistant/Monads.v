Require Import Lia.
Require Import String.

(** ** Monad *)

Section Monad.

Class Monad (M : Type -> Type) :=
{ 
  ret : forall {T : Type}, T -> M T;
  bind : forall {T U : Type}, M T -> (T -> M U) -> M U;
  left_identity_prf : forall {T U : Type} a f, @bind T U (ret a) f = f a;
  right_identity_prf : forall {T : Type} (m : M T), @bind T T m ret = m;
  associativity_prf : forall {T U V : Type} (m : M T) (g : T -> M U) (h : U -> M V), 
    @bind U V (@bind T U m g) h = @bind T V m (fun x => @bind U V (g x) h)
}.

Notation "a >>= b" := (bind a b) (at level 58, left associativity).
Notation "f >=> g" := (fun x => (f x >>= g)) (at level 58, left associativity).

Require Import Coq.Logic.FunctionalExtensionality.

Lemma kleisli_assoc : forall (A B C D : Type) (m : Type -> Type) `{Monad m} 
  (f : A -> m B) (g : B -> m C) (h : C -> m D),
  (f >=> g) >=> h = f >=> (g >=> h).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  apply Monad.associativity_prf.
Qed.

Search (forall a f, ret a >>= f = f a).
Search (forall m, m >>= ret = m).
Search (forall m g h, m >>= g >>= h = m >>= (g >=> h)).

(** ** Maybe Monad *)

Inductive Maybe (T : Type) : Type := 
  | None : Maybe T
  | Some : T -> Maybe T.
Arguments None {T}.
Arguments Some {T} t.

#[refine] Instance : Monad (Maybe) :=
{
  ret T a := Some a;
  bind T U m f :=
    match m with
        None => None
      | Some a => f a
    end;
  left_identity_prf := _;
  right_identity_prf := _;
  associativity_prf := _
}.
Proof.
  - (* Left identity proof *)
    intros.
    reflexivity.
  - (* Right identity proof *)
    intros.
    destruct m.
    + reflexivity.
    + reflexivity.
  - (* Associativity proof. *)
    intros.
    destruct m.
    + reflexivity.
    + reflexivity.
Defined.

(** ** State/Action Monad *)

Require Import List.
Import ListNotations.

Definition Action (St Result : Type) : Type := St -> (Result * St).

Definition bind' {St U V : Type}
  (aU : Action St U) (f : U -> Action St V) : Action St V.
Proof.
unfold Action in *.
intro st0.
pose proof (aU st0) as (u, st1).
pose proof (f u) as aV.
pose proof (aV st1) as (v, st2).
exact (v, st2).
Defined.

#[refine] Instance ActionMonad (St : Type) : Monad (Action St) := {
  ret := fun (U : Type) (u : U) => fun s => (u, s);
  bind (U V : Type) (aU : Action St U) (f : U -> Action St V) :=
      (fun (st0 : St) => let (u, st1) := aU st0 in 
                           let aV := f u in
                             aV st1) (* which gives (v, st2) *)
}.
Proof.
- (* Left Identity *)
  intros.
  simpl. intros. apply functional_extensionality. intros.
  destruct (f a x). reflexivity.
- (* Right Identity *)
  intros.
  simpl. unfold Action in m.
  apply functional_extensionality.
  intros.
  destruct (m x).
  reflexivity.
- (* Associativity *)
  do 3 intro. intros aT g h.
  simpl. apply functional_extensionality. intro s.
  destruct (aT s) as [t st0].
  destruct (g t st0) as [u st1]. (* Note: aU := g t *)
  destruct (h u st1) as [v st2]. (* Note: aV := h u *)
  reflexivity.
Defined.

Notation "a >>=' b" := (bind' a b) (at level 58, left associativity).

Lemma bindSanityCheck : forall (St U V : Type)
  (aU : Action St U) (f : U -> Action St V),
    bind' aU f = bind aU f.
Proof.
  intros.
  unfold ">>='". simpl. apply functional_extensionality.
  intros. destruct (aU x). destruct (f u s). reflexivity.
Qed.

(** ** Do Notation *)

Notation "a1 ;; a2" := (a1 >>= (fun _ => a2))
  (at level 61, right associativity).
Notation "x <- a1 ;; a2" := (a1 >>= (fun x => a2))
  (at level 61, a1 at next level, right associativity).
Notation "' pat <- a1 ;; a2" :=
  (a1 >>= (fun x => match x with pat => a2 end))
  (at level 61, pat pattern, a1 at next level, right associativity).

Definition minusOne (x : nat) : Maybe nat := 
  match x with
  | O => None
  | S x' => Some x'
end.

Definition add3 (t : nat * nat * nat) : Maybe nat :=
  match t with (a, b, c) =>
    Some (a + b + c)
  end.

Definition triple (x y z: nat) : Maybe (nat * nat * nat) := 
  Some (x, y, z).

Eval compute in
  x <- Some 4 ;;
  y <- minusOne x;; (* y = 3 *)
  z <- minusOne y;; (* z = 2 *)
  t <- triple x y z ;; (* t = (4, 3, 2)*)
  add3 t.

Eval compute in
  Some 4 >>= (fun x =>
    minusOne x >>= (fun y =>
      minusOne y >>= (fun z =>
        triple x y z >>= (fun t => 
          add3 t)))).

(** ** State/Action Monad with Stack *)

Definition Stack := list nat.

Definition pop : Stack -> (nat * Stack) :=
  fun (s : Stack) =>
    match s with
        [] => (0, [])
      | (x :: xs) => (x, xs)
    end.

Definition popTypeExample : Action Stack nat := pop.

Definition push (n : nat) : Action Stack unit :=
  fun (s : Stack) => (tt, n :: s).
Definition pushTypeExample : nat -> Stack -> (unit * Stack) := push.

Definition stackManipulation1 : Action Stack unit :=
  pop >>= push.

Definition stackManipulation1' : Action Stack unit :=
  x <- pop ;; push x.

Require Import Nat.

Definition stackManipulation2 : Action Stack nat :=
  push 4;;
  stackManipulation1;;
  push 5;;
  pop.

Eval compute in stackManipulation2 [1;2;3].

(** ** MonadState Typeclass *)

Class MonadState (T : Type) (m : Type -> Type) : Type := {
  get : m T;
  put : T -> m unit
}.

Instance MonadState_Action (St : Type) : MonadState St (Action St) := {
  get := (fun s => (s, s));
  put (newState : St) := (fun _ => (tt, newState))
}.

(** ** State/Action Transformer Monad *)

Section ActionTransformerMonad.

Variable M : Type -> Type.
Variable M_prf : Monad M.

Definition ActionT `{Monad M} (St : Type) (A : Type) := St -> M (A * St).

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.

Generalizable All Variables.
    
Instance pointwise_eq_ext {A B : Type} `(sb : subrelation B RB eq)
      : subrelation (pointwise_relation A RB) eq.
Proof. intros f g Hfg. apply functional_extensionality. intro x; apply sb, (Hfg x). Qed.
(* Based on https://stackoverflow.com/questions/43849824/coq-rewriting-using-lambda-arguments 
Thanks Matthieu Sozeau and Anton Trunov *)

#[refine] Instance Monad_ActionT (St : Type) : Monad (ActionT St) := {
  ret (U : Type) (a : U) (s : St) := ret (a, s);
  bind (U V : Type) (aU : ActionT St U) (f : U -> ActionT St V) := 
    (fun s => 
      ' (u, s') <- aU s ;;
      f u s'
    )
}.
Proof.
- (* Left identity *)
  intros.
  apply functional_extensionality.
  intros.
  setoid_rewrite left_identity_prf.
  reflexivity.
- (* Right identity *)
  intros T aT.
  apply functional_extensionality.
  intros.
  assert (forall x0 : T * St, (let (a, s') := x0 in ret (a, s')) = ret x0).
  { 
    intros.
    destruct x0.
    reflexivity.
  }
  setoid_rewrite H.
  apply right_identity_prf.
- (* Associativity *)
  intros.
  apply functional_extensionality.
  intros.
  rewrite associativity_prf.
  assert(forall x0 : T * St,
     x1 <- (let (a, s') := x0 in g a s');;
     (let (a, s') := (x1 : U * St) in h a s')
     =
     (let (a, s') := x0 in x1 <- g a s';;
     (let (a0, s'0) := (x1 : U * St) in h a0 s'0))).
    {
      intros.
      destruct x0.
      reflexivity.
    }
  setoid_rewrite H.
  reflexivity.
Defined.

Instance MonadState_ActionT (St : Type) : MonadState St (ActionT St) := {
  get := (fun s => ret (s, s));
  put (newState : St) := (fun _ => ret (tt, newState))
}.

End ActionTransformerMonad.

(** ** Action Transformer Monad with Maybe and Stack *)

Definition maybeActionT (St : Type) := ActionT Maybe St.

Instance Monad_MaybeActionT (St : Type) : Monad (maybeActionT St) :=
  Monad_ActionT Maybe _ St.

Instance MonadState_MaybeActionT (St : Type) : MonadState St (maybeActionT St) :=
  MonadState_ActionT Maybe _ St.

Definition pop' : Stack -> Maybe (nat * Stack) :=
    fun (s : Stack) =>
      match s with
          [] => None
        | (x :: xs) => Some (x, xs)
      end.

Definition pop'TypeExample : ActionT Maybe Stack nat := pop'.

Definition push' (n : nat) : ActionT Maybe Stack unit :=
    fun (s : Stack) => Some (tt, n :: s).
Definition push'TypeExample : nat -> Stack -> Maybe (unit * Stack) := push'.

Definition plusStack : maybeActionT Stack nat :=
  a <- pop' ;;
  b <- pop' ;;
  ret (a + b).

Eval compute in plusStack [1;5;3]. (* .all *)

Definition plus3Stack : maybeActionT Stack nat :=
  a <- pop' ;;
  b <- pop' ;;
  c <- pop' ;;
  ret (a + b + c).

Definition plus3Stack' : maybeActionT Stack nat :=
  r <- plusStack ;;
  push' r ;;
  r2 <- plusStack ;;
  ret r2.

(** Since we are using a proof assistant such as Coq, we can prove that these two definitions are the same (under the assumption of functional extensionality). These two functions are not equal without the functional extensionality axiom because they are intensionally different. *)

Lemma plus3Equivalence : plus3Stack = plus3Stack'.
Proof.
  apply functional_extensionality.
  intros.
  unfold plus3Stack, plus3Stack', plusStack.
  destruct x.
  - simpl. reflexivity.
  - destruct x.
  + simpl. reflexivity.
  + destruct x.
  * simpl. reflexivity.
  * simpl. reflexivity.
Qed.

(** ** Action Transformer Monad with Maybe and Contract Storage *)

Definition ethereum_address := nat.

Record tenancy_contract_storage_type := {
  Contract_landlord : ethereum_address;
  Contract_tenant   : ethereum_address
}.

Definition update_Contract_tenant new_tenant r := {|
  Contract_landlord := Contract_landlord r;
  Contract_tenant := new_tenant
|}.

Definition update_Contract_landlord landlord r := {|
  Contract_landlord := landlord;
  Contract_tenant := Contract_tenant r
|}.

Definition wei := nat.
Record machine_environment := {
  caller : ethereum_address;
  callvalue : wei
}.

Definition init_tenancy_contract_storage : tenancy_contract_storage_type := {|
  Contract_landlord := 4632783269828394728397482347237428347892;
  Contract_tenant :=   8472218372847328472389723847238472389473
|}.

Definition DS := ActionT Maybe tenancy_contract_storage_type.

Definition gets {A : Type} f : DS A :=
  a <- get ;;
  ret (f a).

Definition puts f : DS unit :=
  a <- get ;;
  put (f a).

Definition fail {A : Type} : DS A :=
  fun (s : tenancy_contract_storage_type) => None.

Definition Contract_setTenant (newTenant : ethereum_address) (me : machine_environment) : DS unit :=
  landlord <- gets Contract_landlord;;
  if (landlord =? (caller me)) 
    then puts (update_Contract_tenant newTenant)
    else fail.

Definition Contract_getTenant (me : machine_environment) : DS ethereum_address :=
  tenant <- gets Contract_tenant;;
  ret tenant.

Definition Contract_getTenantTypeExample : 
  machine_environment -> tenancy_contract_storage_type 
  -> Maybe (ethereum_address * tenancy_contract_storage_type)
  := Contract_getTenant.

Definition Contract_changeLandlord (new_landlord : ethereum_address) (me : machine_environment)
 : DS unit :=
    landlord <- gets Contract_landlord;;
    if (landlord =? (caller me)) 
      then 
        puts (update_Contract_landlord new_landlord)
      else fail.

(** ** Proofs About the Tenancy Contract *)

Lemma Contract_changeLandlord_onlyLandlord :
  forall new_landlord me st,
     (exists r st', Contract_changeLandlord new_landlord me st = Some (r, st'))
  -> (caller me) = Contract_landlord st.
Proof.
  intros.
  destruct H as [r]. destruct H as [st']. unfold Contract_changeLandlord in H. (* H *)
  simpl in H. (* H *)
  destruct (Contract_landlord st =? caller me) eqn:Case.
    + (* Case H *)
    apply EqNat.beq_nat_true in Case. (* Case H *)
    auto.
    + (* Case H *)
    unfold fail in H. (* H *)
    discriminate.
Qed.

Lemma Contract_changeLandlord_onlyLandlord_converse :
  forall new_landlord me st,
  (caller me) = Contract_landlord st   
  -> (exists r st', Contract_changeLandlord new_landlord me st = Some (r, st'))
  .
Proof.
  intros.
  unfold Contract_changeLandlord.
  simpl. rewrite H.
  rewrite PeanoNat.Nat.eqb_refl.
  exists tt. exists (update_Contract_landlord new_landlord st).
  unfold puts. simpl.
  reflexivity.
Qed.

Lemma Contract_setTenant_onlyLandlord_converse :
  forall new_tenant me st,
  (caller me) = Contract_landlord st   
  -> (exists r st', Contract_setTenant new_tenant me st = Some (r, st'))
  .
Proof.
  intros.
  unfold Contract_setTenant.
  simpl. rewrite H.
  rewrite PeanoNat.Nat.eqb_refl.
  exists tt. exists (update_Contract_tenant new_tenant st).
  unfold puts. simpl.
  reflexivity.
Qed.

Lemma Contract_changeTenant_landlordSet :
  forall new_tenant me st,
    (caller me) = Contract_landlord st ->
    match Contract_setTenant new_tenant me st with
    | Some (r, st') => Contract_tenant st' = new_tenant
    | None => False
    end.
Proof.
  intros.
  pose proof (Contract_setTenant_onlyLandlord_converse new_tenant me st H).
  destruct H0 as [r]. destruct H0 as [st'].
  rewrite H0. (* H0 *)
  unfold Contract_setTenant in H0.
  simpl in H0.
  destruct (Contract_landlord st =? caller me) eqn:Case.
    - unfold puts in H0. simpl in H0.
    inversion H0. (* H2 H3 *)
    simpl. reflexivity.
    -  (* H0 *)
    unfold fail in H0. (* H0 *)
discriminate.
Qed.

End Monad.