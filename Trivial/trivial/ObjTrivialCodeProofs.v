(* Skeleton by Edgser for trivial.ds *)
Require Import BinPos.
Require Import DeepSpec.Runtime.
Require Import trivial.EdsgerIdents.
Require Import trivial.DataTypes.
Require Import trivial.DataTypeOps.
Require Import trivial.DataTypeProofs.
Require Import trivial.LayerCONTRACT.

Section EdsgerGen.

Existing Instance GlobalLayerSpec.
Existing Instances CONTRACT_overlay_spec.

Context {memModelOps : MemoryModelOps mem}.

Lemma Trivial_constructor_vc me d :
    high_level_invariant d ->
    synth_func_cond Trivial_constructor Trivial_constructor_wf
                    me d.
Proof.
Admitted.

Lemma Trivial_constructor_oblg me d :
    high_level_invariant d ->
    synth_func_obligation Trivial_constructor Trivial_constructor_wf
                          me d.
Proof.
Admitted.

Lemma Trivial_boolToInt_vc a0 me d :
    ht_ft_cond a0 -> ht_valid_ft_cond a0 ->
    high_level_invariant d ->
    synth_func_cond Trivial_boolToInt Trivial_boolToInt_wf
                    a0 me d.
Proof.
Admitted.

Lemma Trivial_boolToInt_oblg a0 me d :
    ht_ft_cond a0 -> ht_valid_ft_cond a0 ->
    high_level_invariant d ->
    synth_func_obligation Trivial_boolToInt Trivial_boolToInt_wf
                          a0 me d.
Proof.
Admitted.

Lemma Trivial_boolToIntTracker_vc a0 me d :
    ht_ft_cond a0 -> ht_valid_ft_cond a0 ->
    high_level_invariant d ->
    synth_func_cond Trivial_boolToIntTracker Trivial_boolToIntTracker_wf
                    a0 me d.
Proof.
Admitted.

Lemma Trivial_boolToIntTracker_oblg a0 me d :
    ht_ft_cond a0 -> ht_valid_ft_cond a0 ->
    high_level_invariant d ->
    synth_func_obligation Trivial_boolToIntTracker Trivial_boolToIntTracker_wf
                          a0 me d.
Proof.
Admitted.

End EdsgerGen.
