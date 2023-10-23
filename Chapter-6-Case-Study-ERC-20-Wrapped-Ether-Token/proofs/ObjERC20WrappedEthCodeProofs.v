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


Ltac code_proofs_auto :=
    intros;
    unfold synth_func_obligation;
    repeat (split; auto).

Lemma ERC20WrappedEth_constructor_vc me d :
    high_level_invariant d ->
    synth_func_cond ERC20WrappedEth_constructor ERC20WrappedEth_constructor_wf
                    me d.
Proof.
code_proofs_auto.
Qed.

Lemma ERC20WrappedEth_constructor_oblg me d :
    high_level_invariant d ->
    synth_func_obligation ERC20WrappedEth_constructor ERC20WrappedEth_constructor_wf
                          me d.
Proof.
code_proofs_auto.
Qed.

Lemma ERC20WrappedEth_totalSupply_vc me d :
    high_level_invariant d ->
    synth_func_cond ERC20WrappedEth_totalSupply ERC20WrappedEth_totalSupply_wf
                    me d.
Proof.
code_proofs_auto.
Qed.

Lemma ERC20WrappedEth_totalSupply_oblg me d :
    high_level_invariant d ->
    synth_func_obligation ERC20WrappedEth_totalSupply ERC20WrappedEth_totalSupply_wf
                          me d.
Proof.
code_proofs_auto.
Qed.

Lemma ERC20WrappedEth_balanceOf_vc a0 me d :
    ht_ft_cond a0 -> ht_valid_ft_cond a0 ->
    high_level_invariant d ->
    synth_func_cond ERC20WrappedEth_balanceOf ERC20WrappedEth_balanceOf_wf
                    a0 me d.
Proof.
code_proofs_auto.
Qed.

Lemma ERC20WrappedEth_balanceOf_oblg a0 me d :
    ht_ft_cond a0 -> ht_valid_ft_cond a0 ->
    high_level_invariant d ->
    synth_func_obligation ERC20WrappedEth_balanceOf ERC20WrappedEth_balanceOf_wf
                          a0 me d.
Proof.
code_proofs_auto.
Qed.

Lemma ERC20WrappedEth_allowance_vc a0 a1 me d :
    ht_ft_cond a0 -> ht_valid_ft_cond a0 ->
    ht_ft_cond a1 -> ht_valid_ft_cond a1 ->
    high_level_invariant d ->
    synth_func_cond ERC20WrappedEth_allowance ERC20WrappedEth_allowance_wf
                    a0 a1 me d.
Proof.
code_proofs_auto.
Qed.

Lemma ERC20WrappedEth_allowance_oblg a0 a1 me d :
    ht_ft_cond a0 -> ht_valid_ft_cond a0 ->
    ht_ft_cond a1 -> ht_valid_ft_cond a1 ->
    high_level_invariant d ->
    synth_func_obligation ERC20WrappedEth_allowance ERC20WrappedEth_allowance_wf
                          a0 a1 me d.
Proof.
code_proofs_auto.
Qed.

Lemma ERC20WrappedEth_approve_vc a0 a1 me d :
    ht_ft_cond a0 -> ht_valid_ft_cond a0 ->
    ht_ft_cond a1 -> ht_valid_ft_cond a1 ->
    high_level_invariant d ->
    synth_func_cond ERC20WrappedEth_approve ERC20WrappedEth_approve_wf
                    a0 a1 me d.
Proof.
code_proofs_auto.
Qed.

Lemma ERC20WrappedEth_approve_oblg a0 a1 me d :
    ht_ft_cond a0 -> ht_valid_ft_cond a0 ->
    ht_ft_cond a1 -> ht_valid_ft_cond a1 ->
    high_level_invariant d ->
    synth_func_obligation ERC20WrappedEth_approve ERC20WrappedEth_approve_wf
                          a0 a1 me d.
Proof.
code_proofs_auto.
Qed.

Lemma ERC20WrappedEth_approveSafely_vc a0 a1 a2 me d :
    ht_ft_cond a0 -> ht_valid_ft_cond a0 ->
    ht_ft_cond a1 -> ht_valid_ft_cond a1 ->
    ht_ft_cond a2 -> ht_valid_ft_cond a2 ->
    high_level_invariant d ->
    synth_func_cond ERC20WrappedEth_approveSafely ERC20WrappedEth_approveSafely_wf
                    a0 a1 a2 me d.
Proof.
code_proofs_auto.
Qed.

Lemma ERC20WrappedEth_approveSafely_oblg a0 a1 a2 me d :
    ht_ft_cond a0 -> ht_valid_ft_cond a0 ->
    ht_ft_cond a1 -> ht_valid_ft_cond a1 ->
    ht_ft_cond a2 -> ht_valid_ft_cond a2 ->
    high_level_invariant d ->
    synth_func_obligation ERC20WrappedEth_approveSafely ERC20WrappedEth_approveSafely_wf
                          a0 a1 a2 me d.
Proof.
code_proofs_auto.
Qed.

Lemma ERC20WrappedEth_transfer_vc a0 a1 me d :
    ht_ft_cond a0 -> ht_valid_ft_cond a0 ->
    ht_ft_cond a1 -> ht_valid_ft_cond a1 ->
    high_level_invariant d ->
    synth_func_cond ERC20WrappedEth_transfer ERC20WrappedEth_transfer_wf
                    a0 a1 me d.
Proof.
intros.
remember a0 as _to. remember a1 as _value. 
clear a0 a1 Heq_to Heq_value.
unfold Z32 in _value. 
simpl in *. (* _to _value H1 *)
unfold synth_func_cond.
simpl.
repeat split.
- subst.
  simpl in *.
  inversion H9.
  shelve.
  - remember ((@SpecTree.get
  (param_env
     (@cons hyper_type_pair int_U_pair
        (@cons hyper_type_pair int_Z32_pair (@nil hyper_type_pair)))
     (@FC_param_ident_start (@GlobalLayerSpec memModelOps)
        (@ERC20WrappedEth_transfer memModelOps)))
  (xO (xO (xI xH)))
  (@SpecTree.set
     (@AList.set hyper_type_pair
        (@FC_param_ident_start (@GlobalLayerSpec memModelOps)
           (@ERC20WrappedEth_transfer memModelOps)) int_U_pair
        (@AList.empty TypePairProjection.A))
     (Pos.succ
        (@FC_param_ident_start (@GlobalLayerSpec memModelOps)
           (@ERC20WrappedEth_transfer memModelOps))) int_Z32_pair
     _value
     (@SpecTree.set (@AList.empty TypePairProjection.A)
        (@FC_param_ident_start (@GlobalLayerSpec memModelOps)
           (@ERC20WrappedEth_transfer memModelOps)) int_U_pair _to
        SpecTree.empty)))) as STORED_VALUE. (* H10 *)
  destruct (v >=? STORED_VALUE) eqn:Case; [|inversion H10]. simpl in *. (* H10 Case *)
  apply Z.geb_le in Case. (* Case *)
  lia.
Abort.

Lemma ERC20WrappedEth_transfer_oblg a0 a1 me d :
    ht_ft_cond a0 -> ht_valid_ft_cond a0 ->
    ht_ft_cond a1 -> ht_valid_ft_cond a1 ->
    high_level_invariant d ->
    synth_func_obligation ERC20WrappedEth_transfer ERC20WrappedEth_transfer_wf
                          a0 a1 me d.
Proof.
code_proofs_auto.
Qed.

Lemma ERC20WrappedEth_transferFrom_vc a0 a1 a2 me d :
    ht_ft_cond a0 -> ht_valid_ft_cond a0 ->
    ht_ft_cond a1 -> ht_valid_ft_cond a1 ->
    ht_ft_cond a2 -> ht_valid_ft_cond a2 ->
    high_level_invariant d ->
    synth_func_cond ERC20WrappedEth_transferFrom ERC20WrappedEth_transferFrom_wf
                    a0 a1 a2 me d.
Proof.
intros.
unfold synth_func_cond.
simpl.
repeat split.
- remember ((@SpecTree.get
(param_env
   (@cons hyper_type_pair int_U_pair
      (@cons hyper_type_pair int_U_pair
         (@cons hyper_type_pair int_Z32_pair
            (@nil hyper_type_pair))))
   (@FC_param_ident_start (@GlobalLayerSpec memModelOps)
      (@ERC20WrappedEth_transferFrom memModelOps)))
(xI (xO (xI xH)))
(@SpecTree.set
   (@AList.set hyper_type_pair
      (Pos.succ
         (@FC_param_ident_start (@GlobalLayerSpec memModelOps)
            (@ERC20WrappedEth_transferFrom memModelOps)))
      int_U_pair
      (@AList.set hyper_type_pair
         (@FC_param_ident_start (@GlobalLayerSpec memModelOps)
            (@ERC20WrappedEth_transferFrom memModelOps))
         int_U_pair (@AList.empty TypePairProjection.A)))
   (Pos.succ
      (Pos.succ
         (@FC_param_ident_start (@GlobalLayerSpec memModelOps)
            (@ERC20WrappedEth_transferFrom memModelOps))))
   int_Z32_pair a2
   (@SpecTree.set
      (@AList.set hyper_type_pair
         (@FC_param_ident_start (@GlobalLayerSpec memModelOps)
            (@ERC20WrappedEth_transferFrom memModelOps))
         int_U_pair (@AList.empty TypePairProjection.A))
      (Pos.succ
         (@FC_param_ident_start (@GlobalLayerSpec memModelOps)
            (@ERC20WrappedEth_transferFrom memModelOps)))
      int_U_pair a1
      (@SpecTree.set (@AList.empty TypePairProjection.A)
         (@FC_param_ident_start (@GlobalLayerSpec memModelOps)
            (@ERC20WrappedEth_transferFrom memModelOps))
         int_U_pair a0 SpecTree.empty))))) as STORED_VALUE. (* H11 *)
  destruct(v >=? STORED_VALUE) eqn:Case; [|inversion H11].
  apply Z.geb_le in Case. (* Case *)
lia.
- 
simpl in H15.
subst. simpl.
unfold ht_ft_cond in H3.
simpl in H3.
inversion H14.
clear -H3.
simpl in *. unfold Z32 in a2. (* H3 *)
shelve.
- 
remember ( (@SpecTree.get
(param_env
   (@cons hyper_type_pair int_U_pair
      (@cons hyper_type_pair int_U_pair
         (@cons hyper_type_pair int_Z32_pair
            (@nil hyper_type_pair))))
   (@FC_param_ident_start (@GlobalLayerSpec memModelOps)
      (@ERC20WrappedEth_transferFrom memModelOps)))
(xI (xO (xI xH)))
(@SpecTree.set
   (@AList.set hyper_type_pair
      (Pos.succ
         (@FC_param_ident_start (@GlobalLayerSpec memModelOps)
            (@ERC20WrappedEth_transferFrom memModelOps)))
      int_U_pair
      (@AList.set hyper_type_pair
         (@FC_param_ident_start (@GlobalLayerSpec memModelOps)
            (@ERC20WrappedEth_transferFrom memModelOps))
         int_U_pair (@AList.empty TypePairProjection.A)))
   (Pos.succ
      (Pos.succ
         (@FC_param_ident_start (@GlobalLayerSpec memModelOps)
            (@ERC20WrappedEth_transferFrom memModelOps))))
   int_Z32_pair a2
   (@SpecTree.set
      (@AList.set hyper_type_pair
         (@FC_param_ident_start (@GlobalLayerSpec memModelOps)
            (@ERC20WrappedEth_transferFrom memModelOps))
         int_U_pair (@AList.empty TypePairProjection.A))
      (Pos.succ
         (@FC_param_ident_start (@GlobalLayerSpec memModelOps)
            (@ERC20WrappedEth_transferFrom memModelOps)))
      int_U_pair a1
      (@SpecTree.set (@AList.empty TypePairProjection.A)
         (@FC_param_ident_start (@GlobalLayerSpec memModelOps)
            (@ERC20WrappedEth_transferFrom memModelOps))
         int_U_pair a0 SpecTree.empty))))) as STORED_VALUE.
destruct(v0 >=? STORED_VALUE) eqn:Case; [|inversion H15].
inversion H13.
rewrite Z.geb_le in Case.
rewrite <- H18 in Case.
rewrite <- H19.
clear -Case. (* Case *)
lia.
Abort.

Lemma ERC20WrappedEth_transferFrom_oblg a0 a1 a2 me d :
    ht_ft_cond a0 -> ht_valid_ft_cond a0 ->
    ht_ft_cond a1 -> ht_valid_ft_cond a1 ->
    ht_ft_cond a2 -> ht_valid_ft_cond a2 ->
    high_level_invariant d ->
    synth_func_obligation ERC20WrappedEth_transferFrom ERC20WrappedEth_transferFrom_wf
                          a0 a1 a2 me d.
Proof.
code_proofs_auto.
Qed.

Lemma ERC20WrappedEth_mint_vc me d :
    high_level_invariant d ->
    synth_func_cond ERC20WrappedEth_mint ERC20WrappedEth_mint_wf
                    me d.
Proof.
intros.
unfold synth_func_cond.
simpl.
repeat split.
- (* wrapped[msg_sender] := wrapped_amount + msg_value; *) 
inversion H2.
shelve.
- 
inversion H4.
shelve.
Abort.

Lemma ERC20WrappedEth_mint_oblg me d :
    high_level_invariant d ->
    synth_func_obligation ERC20WrappedEth_mint ERC20WrappedEth_mint_wf
                          me d.
Proof.
code_proofs_auto.
Qed.

Lemma ERC20WrappedEth_burn_vc a0 me d :
    ht_ft_cond a0 -> ht_valid_ft_cond a0 ->
    high_level_invariant d ->
    synth_func_cond ERC20WrappedEth_burn ERC20WrappedEth_burn_wf
                    a0 me d.
Proof.
intros.
unfold synth_func_cond.
simpl in *.
repeat split.
- remember ((@SpecTree.get
(param_env
   (@cons hyper_type_pair int_Z32_pair (@nil hyper_type_pair))
   (@FC_param_ident_start (@GlobalLayerSpec memModelOps)
      (@ERC20WrappedEth_burn memModelOps))) 
(xI (xI (xO xH)))
(@SpecTree.set (@AList.empty TypePairProjection.A)
   (@FC_param_ident_start (@GlobalLayerSpec memModelOps)
      (@ERC20WrappedEth_burn memModelOps)) int_Z32_pair a0
   SpecTree.empty))) as STORED_VALUE.
destruct (v >=? STORED_VALUE) eqn:Case; [|inversion H6].
rewrite Z.geb_le in Case. (* Case *)
clear -Case.
lia.
- simpl in *. inversion H8.
destruct(v >=? a0) eqn:Case; simpl in *; [|discriminate].
rewrite Z.geb_le in Case.
inversion H5. subst.
clear -Case.
remember ((@Int256Tree.get_default
(@Z_bounded Int256.modulus modulus_bound) Z0
(@MachineModel.me_caller global_abstract_data_type me)
(ERC20WrappedEth_wrapped m3))) as wrapped_amount.
assert(ERC20WrappedEth__totalSupply m6 >= wrapped_amount). (* .out -.g#* .g#1 -* Heqwrapped_amount *)
shelve. (* Heqwrapped_amount Case H  *)
clear -Case H.
lia.
Abort.

Lemma ERC20WrappedEth_burn_oblg a0 me d :
    ht_ft_cond a0 -> ht_valid_ft_cond a0 ->
    high_level_invariant d ->
    synth_func_obligation ERC20WrappedEth_burn ERC20WrappedEth_burn_wf
                          a0 me d.
Proof.
code_proofs_auto.
Qed.


End EdsgerGen.