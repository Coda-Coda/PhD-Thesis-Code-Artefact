(* Skeleton by Edgser for ERC20WrappedEth.ds *)
Require Import BinPos.
Require Import DeepSpec.Runtime.
Require Import ERC20WrappedEth.EdsgerIdents.
Require Import ERC20WrappedEth.DataTypes.
Require Import ERC20WrappedEth.DataTypeOps.
Require Import ERC20WrappedEth.DataTypeProofs.
Require Import ERC20WrappedEth.LayerCONTRACT.

Section EdsgerGen.

Existing Instance GlobalLayerSpec.
Existing Instances CONTRACT_overlay_spec.

Context {memModelOps : MemoryModelOps mem}.

Lemma ERC20WrappedEth_constructor_vc me d :
    high_level_invariant d ->
    synth_func_cond ERC20WrappedEth_constructor ERC20WrappedEth_constructor_wf
                    me d.
Proof.
Admitted.

Lemma ERC20WrappedEth_constructor_oblg me d :
    high_level_invariant d ->
    synth_func_obligation ERC20WrappedEth_constructor ERC20WrappedEth_constructor_wf
                          me d.
Proof.
Admitted.

Lemma ERC20WrappedEth_totalSupply_vc me d :
    high_level_invariant d ->
    synth_func_cond ERC20WrappedEth_totalSupply ERC20WrappedEth_totalSupply_wf
                    me d.
Proof.
Admitted.

Lemma ERC20WrappedEth_totalSupply_oblg me d :
    high_level_invariant d ->
    synth_func_obligation ERC20WrappedEth_totalSupply ERC20WrappedEth_totalSupply_wf
                          me d.
Proof.
Admitted.

Lemma ERC20WrappedEth_balanceOf_vc a0 me d :
    ht_ft_cond a0 -> ht_valid_ft_cond a0 ->
    high_level_invariant d ->
    synth_func_cond ERC20WrappedEth_balanceOf ERC20WrappedEth_balanceOf_wf
                    a0 me d.
Proof.
Admitted.

Lemma ERC20WrappedEth_balanceOf_oblg a0 me d :
    ht_ft_cond a0 -> ht_valid_ft_cond a0 ->
    high_level_invariant d ->
    synth_func_obligation ERC20WrappedEth_balanceOf ERC20WrappedEth_balanceOf_wf
                          a0 me d.
Proof.
Admitted.

Lemma ERC20WrappedEth_transfer_vc a0 a1 me d :
    ht_ft_cond a0 -> ht_valid_ft_cond a0 ->
    ht_ft_cond a1 -> ht_valid_ft_cond a1 ->
    high_level_invariant d ->
    synth_func_cond ERC20WrappedEth_transfer ERC20WrappedEth_transfer_wf
                    a0 a1 me d.
Proof.
Admitted.

Lemma ERC20WrappedEth_transfer_oblg a0 a1 me d :
    ht_ft_cond a0 -> ht_valid_ft_cond a0 ->
    ht_ft_cond a1 -> ht_valid_ft_cond a1 ->
    high_level_invariant d ->
    synth_func_obligation ERC20WrappedEth_transfer ERC20WrappedEth_transfer_wf
                          a0 a1 me d.
Proof.
Admitted.

Lemma ERC20WrappedEth_transferFrom_vc a0 a1 a2 me d :
    ht_ft_cond a0 -> ht_valid_ft_cond a0 ->
    ht_ft_cond a1 -> ht_valid_ft_cond a1 ->
    ht_ft_cond a2 -> ht_valid_ft_cond a2 ->
    high_level_invariant d ->
    synth_func_cond ERC20WrappedEth_transferFrom ERC20WrappedEth_transferFrom_wf
                    a0 a1 a2 me d.
Proof.
Admitted.

Lemma ERC20WrappedEth_transferFrom_oblg a0 a1 a2 me d :
    ht_ft_cond a0 -> ht_valid_ft_cond a0 ->
    ht_ft_cond a1 -> ht_valid_ft_cond a1 ->
    ht_ft_cond a2 -> ht_valid_ft_cond a2 ->
    high_level_invariant d ->
    synth_func_obligation ERC20WrappedEth_transferFrom ERC20WrappedEth_transferFrom_wf
                          a0 a1 a2 me d.
Proof.
Admitted.

Lemma ERC20WrappedEth_allowance_vc a0 a1 me d :
    ht_ft_cond a0 -> ht_valid_ft_cond a0 ->
    ht_ft_cond a1 -> ht_valid_ft_cond a1 ->
    high_level_invariant d ->
    synth_func_cond ERC20WrappedEth_allowance ERC20WrappedEth_allowance_wf
                    a0 a1 me d.
Proof.
Admitted.

Lemma ERC20WrappedEth_allowance_oblg a0 a1 me d :
    ht_ft_cond a0 -> ht_valid_ft_cond a0 ->
    ht_ft_cond a1 -> ht_valid_ft_cond a1 ->
    high_level_invariant d ->
    synth_func_obligation ERC20WrappedEth_allowance ERC20WrappedEth_allowance_wf
                          a0 a1 me d.
Proof.
Admitted.

Lemma ERC20WrappedEth_approve_vc a0 a1 me d :
    ht_ft_cond a0 -> ht_valid_ft_cond a0 ->
    ht_ft_cond a1 -> ht_valid_ft_cond a1 ->
    high_level_invariant d ->
    synth_func_cond ERC20WrappedEth_approve ERC20WrappedEth_approve_wf
                    a0 a1 me d.
Proof.
Admitted.

Lemma ERC20WrappedEth_approve_oblg a0 a1 me d :
    ht_ft_cond a0 -> ht_valid_ft_cond a0 ->
    ht_ft_cond a1 -> ht_valid_ft_cond a1 ->
    high_level_invariant d ->
    synth_func_obligation ERC20WrappedEth_approve ERC20WrappedEth_approve_wf
                          a0 a1 me d.
Proof.
Admitted.

Lemma ERC20WrappedEth_approveSafely_vc a0 a1 a2 me d :
    ht_ft_cond a0 -> ht_valid_ft_cond a0 ->
    ht_ft_cond a1 -> ht_valid_ft_cond a1 ->
    ht_ft_cond a2 -> ht_valid_ft_cond a2 ->
    high_level_invariant d ->
    synth_func_cond ERC20WrappedEth_approveSafely ERC20WrappedEth_approveSafely_wf
                    a0 a1 a2 me d.
Proof.
Admitted.

Lemma ERC20WrappedEth_approveSafely_oblg a0 a1 a2 me d :
    ht_ft_cond a0 -> ht_valid_ft_cond a0 ->
    ht_ft_cond a1 -> ht_valid_ft_cond a1 ->
    ht_ft_cond a2 -> ht_valid_ft_cond a2 ->
    high_level_invariant d ->
    synth_func_obligation ERC20WrappedEth_approveSafely ERC20WrappedEth_approveSafely_wf
                          a0 a1 a2 me d.
Proof.
Admitted.

Lemma ERC20WrappedEth_mint_vc me d :
    high_level_invariant d ->
    synth_func_cond ERC20WrappedEth_mint ERC20WrappedEth_mint_wf
                    me d.
Proof.
Admitted.

Lemma ERC20WrappedEth_mint_oblg me d :
    high_level_invariant d ->
    synth_func_obligation ERC20WrappedEth_mint ERC20WrappedEth_mint_wf
                          me d.
Proof.
Admitted.

Lemma ERC20WrappedEth_burn_vc a0 me d :
    ht_ft_cond a0 -> ht_valid_ft_cond a0 ->
    high_level_invariant d ->
    synth_func_cond ERC20WrappedEth_burn ERC20WrappedEth_burn_wf
                    a0 me d.
Proof.
Admitted.

Lemma ERC20WrappedEth_burn_oblg a0 me d :
    ht_ft_cond a0 -> ht_valid_ft_cond a0 ->
    high_level_invariant d ->
    synth_func_obligation ERC20WrappedEth_burn ERC20WrappedEth_burn_wf
                          a0 me d.
Proof.
Admitted.

End EdsgerGen.
