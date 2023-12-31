(* WARNING: This file is generated by Edsger, the DeepSEA compiler.
            All modification will be lost when regenerating. *)
(* Module fpblind.RefineBLINDAUCTION for fpblind.ds *)
Require Import BinPos.
Require Import DeepSpec.Runtime.
Require Import DeepSpec.Linking.
Require Import fpblind.EdsgerIdents.
Require Import fpblind.DataTypes.
Require Import fpblind.DataTypeOps.
Require Import fpblind.DataTypeProofs.
Require Import layerlib.LayerCalculusLemma.
Require Import layerlib.RefinementTactic.
Require Import layerlib.RefinementTacticAux.
Require Import liblayers.compcertx.MakeProgram.
Require Import liblayers.compcertx.MemWithData.

Require Import fpblind.LayerBLINDAUCTION.
Require Import fpblind.LSimEVMOPCODE.

Section EdsgerGen.


Context {mem}`{Hmem: Mem.MemoryModel mem}.
Context`{Hmwd: UseMemWithData mem}.
Context`{make_program_ops: !MakeProgramOps Clight.function Ctypes.type Clight.fundef Ctypes.type}.
Context`{Hmake_program: !MakeProgram Clight.function Ctypes.type Clight.fundef Ctypes.type}.
Instance GlobalLayerSpec : LayerSpecClass := {
  make_program_ops := make_program_ops;
  Hmake_program := Hmake_program;
  GetHighData := global_abstract_data_type
}.
Context`{global_abdata : !GlobalAbData init_global_abstract_data global_low_level_invariant}.
Context`{CTXT_prf : !Layer_BLINDAUCTION_Context_prf}.
Context`{EVMOPCODE_pres_inv : !EVMOPCODE_preserves_invariants}.
Context`{BLINDAUCTION_pres_inv : !BLINDAUCTION_preserves_invariants}.

Existing Instances BLINDAUCTION_overlay_spec BLINDAUCTION_underlay_spec.

Record relate_RData (j : meminj) (habd : GetHighData) (labd : GetLowData) : Prop
    := mkrelate_RData {
  (* EVMOpcode *)
  _events_re : (_events habd) = (_events labd)
}.

Record match_RData (habd : GetHighData) (m : mem) (j : meminj) : Prop
    := MATCH_RDATA {
  _beneficiary_ma : variable_match BlindAuction__beneficiary_var habd m;
  _biddingEnd_ma : variable_match BlindAuction__biddingEnd_var habd m;
  _revealEnd_ma : variable_match BlindAuction__revealEnd_var habd m;
  _ended_ma : variable_match BlindAuction__ended_var habd m;
  _bids_ma : variable_match BlindAuction__bids_var habd m;
  _highestBidder_ma : variable_match BlindAuction__highestBidder_var habd m;
  _highestBid_ma : variable_match BlindAuction__highestBid_var habd m;
  _pendingReturns_ma : variable_match BlindAuction__pendingReturns_var habd m;
  _trueBids_ma : variable_match BlindAuction__trueBids_var habd m;
  _secrets_ma : variable_match BlindAuction__secrets_var habd m
}.

Local Hint Resolve MATCH_RDATA.

Global Instance rel_ops: CompatRelOps GetHighDataX GetLowDataX :=
{
  relate_AbData f d1 d2 := relate_RData f d1 d2;
  match_AbData d1 m f := match_RData d1 m f;
  new_glbl := var_BlindAuction__beneficiary_ident :: var_BlindAuction__biddingEnd_ident :: var_BlindAuction__revealEnd_ident :: var_BlindAuction__ended_ident :: var_BlindAuction__bids_ident :: var_BlindAuction__highestBidder_ident :: var_BlindAuction__highestBid_ident :: var_BlindAuction__pendingReturns_ident :: var_BlindAuction__trueBids_ident :: var_BlindAuction__secrets_ident :: nil
}.

Global Instance BlindAuction__beneficiary_hyper_ltype_static :
    HyperLTypeStatic BlindAuction__beneficiary_var new_glbl.
Proof.
  split; try solve
    [ Decision.decision
    | simpl; auto
    | simpl BlindAuction__beneficiary_var.(ltype_offset);
      rewrite Int256.unsigned_zero; apply Z.divide_0_r ].
Qed.

Global Instance BlindAuction__biddingEnd_hyper_ltype_static :
    HyperLTypeStatic BlindAuction__biddingEnd_var new_glbl.
Proof.
  split; try solve
    [ Decision.decision
    | simpl; auto
    | simpl BlindAuction__biddingEnd_var.(ltype_offset);
      rewrite Int256.unsigned_zero; apply Z.divide_0_r ].
Qed.

Global Instance BlindAuction__revealEnd_hyper_ltype_static :
    HyperLTypeStatic BlindAuction__revealEnd_var new_glbl.
Proof.
  split; try solve
    [ Decision.decision
    | simpl; auto
    | simpl BlindAuction__revealEnd_var.(ltype_offset);
      rewrite Int256.unsigned_zero; apply Z.divide_0_r ].
Qed.

Global Instance BlindAuction__ended_hyper_ltype_static :
    HyperLTypeStatic BlindAuction__ended_var new_glbl.
Proof.
  split; try solve
    [ Decision.decision
    | simpl; auto
    | simpl BlindAuction__ended_var.(ltype_offset);
      rewrite Int256.unsigned_zero; apply Z.divide_0_r ].
Qed.

Global Instance BlindAuction__bids_hyper_ltype_static :
    HyperLTypeStatic BlindAuction__bids_var new_glbl.
Proof.
  split; try solve
    [ Decision.decision
    | simpl; auto
    | simpl BlindAuction__bids_var.(ltype_offset);
      rewrite Int256.unsigned_zero; apply Z.divide_0_r ].
Qed.

Global Instance BlindAuction__highestBidder_hyper_ltype_static :
    HyperLTypeStatic BlindAuction__highestBidder_var new_glbl.
Proof.
  split; try solve
    [ Decision.decision
    | simpl; auto
    | simpl BlindAuction__highestBidder_var.(ltype_offset);
      rewrite Int256.unsigned_zero; apply Z.divide_0_r ].
Qed.

Global Instance BlindAuction__highestBid_hyper_ltype_static :
    HyperLTypeStatic BlindAuction__highestBid_var new_glbl.
Proof.
  split; try solve
    [ Decision.decision
    | simpl; auto
    | simpl BlindAuction__highestBid_var.(ltype_offset);
      rewrite Int256.unsigned_zero; apply Z.divide_0_r ].
Qed.

Global Instance BlindAuction__pendingReturns_hyper_ltype_static :
    HyperLTypeStatic BlindAuction__pendingReturns_var new_glbl.
Proof.
  split; try solve
    [ Decision.decision
    | simpl; auto
    | simpl BlindAuction__pendingReturns_var.(ltype_offset);
      rewrite Int256.unsigned_zero; apply Z.divide_0_r ].
Qed.

Global Instance BlindAuction__trueBids_hyper_ltype_static :
    HyperLTypeStatic BlindAuction__trueBids_var new_glbl.
Proof.
  split; try solve
    [ Decision.decision
    | simpl; auto
    | simpl BlindAuction__trueBids_var.(ltype_offset);
      rewrite Int256.unsigned_zero; apply Z.divide_0_r ].
Qed.

Global Instance BlindAuction__secrets_hyper_ltype_static :
    HyperLTypeStatic BlindAuction__secrets_var new_glbl.
Proof.
  split; try solve
    [ Decision.decision
    | simpl; auto
    | simpl BlindAuction__secrets_var.(ltype_offset);
      rewrite Int256.unsigned_zero; apply Z.divide_0_r ].
Qed.

Lemma relate_incr:
  forall abd abd' f f',
    relate_RData f abd abd' ->
    inject_incr f f' ->
    relate_RData f' abd abd'.
Proof.
  inversion 1; subst; intros; simpl in *.
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  end.
  repeat (constructor; simpl; eauto).
Qed.
Global Instance rel_prf: CompatRel GetHighDataX GetLowDataX.
Proof.
  constructor; [ destruct 1 .. |]; intros.
  - constructor; eapply inject_match_correct; eauto with typeclass_instances.
  - constructor; eapply store_match_correct; eauto with typeclass_instances.
  - constructor; eapply alloc_match_correct; eauto with typeclass_instances.
  - constructor; eapply free_match_correct; eauto with typeclass_instances.
  - constructor; eapply storebytes_match_correct; eauto with typeclass_instances.
  - eapply relate_incr; eauto.
Qed.

(*
Local Instance: ExternalCallsOps (mwd GetLowDataX) := CompatExternalCalls.compatlayer_extcall_ops EVMOPCODE_Layer.
Local Instance: CompilerConfigOps _ := CompatExternalCalls.compatlayer_compiler_config_ops EVMOPCODE_Layer.
*)

Instance BLINDAUCTION_hypermem : MemoryModel.HyperMem
  := { Hcompatrel := {| crel_prf := rel_prf |} }.

Class BLINDAUCTION_Underlay_preserves_invariants := {
  BLINDAUCTION_Underlay_EVMOpcode_transfer_preserves_invariants :>
    CompatGenSem.PreservesInvariants (HD := cdataLow) EVMOpcode_transfer_spec | 5
}.
Instance BLINDAUCTION'EVMOPCODE_preserves_invariants : BLINDAUCTION_Underlay_preserves_invariants.
Proof. esplit; apply EVMOPCODE_pres_inv. Defined.

(*
Lemma passthrough_correct:
  sim (crel (CompatRel0 := rel_prf) _ _) BLINDAUCTION_Layer_passthrough EVMOPCODE_Layer.
Proof.
  Local Opaque simRR mapsto layer_mapsto_primitive.
  unfold GlobalLayerSpec, MemoryModel.GetHighDataX.
  simpl.

  sim_oplus; simpl.

  Local Transparent simRR mapsto layer_mapsto_primitive.
Qed.*)
End EdsgerGen.
