(* Skeleton by Edgser for Crowdfunding.ds *)
Require Import BinPos.
Require Import DeepSpec.Runtime.
Require Import Crowdfunding.EdsgerIdents.
Require Import Crowdfunding.DataTypes.
Require Import Crowdfunding.DataTypeOps.
Require Import Crowdfunding.DataTypeProofs.
Require Import Crowdfunding.LayerCONTRACT.

Section EdsgerGen.

Existing Instance GlobalLayerSpec.
Existing Instances CONTRACT_overlay_spec.

Context {memModelOps : MemoryModelOps mem}.

Lemma Crowdfunding_constructor_vc me d :
    high_level_invariant d ->
    synth_func_cond Crowdfunding_constructor Crowdfunding_constructor_wf
                    me d.
Proof.
Admitted.

Lemma Crowdfunding_constructor_oblg me d :
    high_level_invariant d ->
    synth_func_obligation Crowdfunding_constructor Crowdfunding_constructor_wf
                          me d.
Proof.
Admitted.

Lemma Crowdfunding_donate_vc me d :
    high_level_invariant d ->
    synth_func_cond Crowdfunding_donate Crowdfunding_donate_wf
                    me d.
Proof.
Admitted.

Lemma Crowdfunding_donate_oblg me d :
    high_level_invariant d ->
    synth_func_obligation Crowdfunding_donate Crowdfunding_donate_wf
                          me d.
Proof.
Admitted.

Lemma Crowdfunding_getFunds_vc me d :
    high_level_invariant d ->
    synth_func_cond Crowdfunding_getFunds Crowdfunding_getFunds_wf
                    me d.
Proof.
Admitted.

Lemma Crowdfunding_getFunds_oblg me d :
    high_level_invariant d ->
    synth_func_obligation Crowdfunding_getFunds Crowdfunding_getFunds_wf
                          me d.
Proof.
Admitted.

Lemma Crowdfunding_claim_vc me d :
    high_level_invariant d ->
    synth_func_cond Crowdfunding_claim Crowdfunding_claim_wf
                    me d.
Proof.
Admitted.

Lemma Crowdfunding_claim_oblg me d :
    high_level_invariant d ->
    synth_func_obligation Crowdfunding_claim Crowdfunding_claim_wf
                          me d.
Proof.
Admitted.

End EdsgerGen.
