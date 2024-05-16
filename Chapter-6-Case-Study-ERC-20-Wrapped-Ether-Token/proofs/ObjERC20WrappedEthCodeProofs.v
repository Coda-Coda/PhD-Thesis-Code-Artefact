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
Context (HCompatDataOps : CompatDataOps global_abstract_data_type).


Ltac code_proofs_auto :=
    intros;
    unfold synth_func_obligation;
    repeat (split; auto).

Definition toZ : unpair_ft (tint_Z_bounded Int256.modulus) -> Z := id.
Definition etherToWei (ether : Z) : Z := ether * (10 ^ 18).
Definition unattainableWeiAmount := etherToWei (10 ^ 20).

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
    (forall a,
      Int256Tree.get_default 0 a (ERC20WrappedEth_wrapped d)
        < unattainableWeiAmount) ->
    (toZ a1 < unattainableWeiAmount) ->
    ht_ft_cond a0 -> ht_valid_ft_cond a0 ->
    ht_ft_cond a1 -> ht_valid_ft_cond a1 ->
    high_level_invariant d ->
    synth_func_cond ERC20WrappedEth_transfer ERC20WrappedEth_transfer_wf
                    a0 a1 me d.
Proof.
intros Hextra1 Hextra2.
intros.
unfold _tp_type_pair in *.
unfold unpair_ft in *.
unfold _tp_type_pair in *.
simpl in *.
unfold Z32 in a1.
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
  inversion H8.
  destruct(MachineModel.me_callvalue me =? 0) eqn:Case; [|simpl in H7; inversion H7].
  simpl in H7. inversion H7.
  destruct(Int256.eq (MachineModel.me_caller me) _to) eqn:SCase;
    [simpl in H6; inversion H6|].
  simpl in H6. inversion H6.
  destruct(Int256.eq (MachineModel.me_caller me)
  (MachineModel.me_address me)) eqn:SSCase; [simpl in H5; inversion H5|].
  simpl in H5. inversion H5.
  destruct(_value >=? 0) eqn:SSSCase; [|simpl in H4; inversion H4].
  simpl in H4. inversion H4.
  subst.
  pose proof (Hextra1 _to). subst.
  unfold Int256.modulus, two_power_nat. simpl.
  unfold toZ, id in Hextra2.
  clear -Hextra2 H11.
  unfold Z_bounded in *.
  remember (@Int256Tree.get_default Z Z0 _to (ERC20WrappedEth_wrapped m5)) as y.
  unfold unattainableWeiAmount, etherToWei in *.
  lia.
  -
  remember ((@SpecTree.get
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
Qed.

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
    (forall a,
      Int256Tree.get_default 0 a (ERC20WrappedEth_wrapped d)
        < unattainableWeiAmount) ->
    (toZ a2 < unattainableWeiAmount) ->
    ht_ft_cond a0 -> ht_valid_ft_cond a0 ->
    ht_ft_cond a1 -> ht_valid_ft_cond a1 ->
    ht_ft_cond a2 -> ht_valid_ft_cond a2 ->
    high_level_invariant d ->
    synth_func_cond ERC20WrappedEth_transferFrom ERC20WrappedEth_transferFrom_wf
                    a0 a1 a2 me d.
Proof.
intros Hextra1 Hextra2.
intros.
unfold synth_func_cond.
simpl.
repeat split.
- 
remember ((@SpecTree.get
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
simpl in *. unfold Z32 in a2.
inversion H13.
inversion H12.
destruct(v >=? a2) eqn:SSSCase; [|simpl in H11; inversion H11].
inversion H11.
inversion H10.
destruct(MachineModel.me_callvalue me =? 0) eqn:Case; [|simpl in H9; inversion H9].
inversion H9.
destruct(a2 >=? 0) eqn:SCase; [|simpl in H6; inversion H6].
inversion H6.
destruct(Int256.eq a0 a1) eqn:SSCase; [simpl in H8; inversion H8|].
inversion H8.
destruct(Int256.eq a0 (MachineModel.me_address me)) eqn:SSSSCase;
  [simpl in H7; inversion H7|].
inversion H7.
subst.
destruct m5. simpl in *.
clear -Hextra2 Hextra1.
unfold toZ, id in Hextra2.
pose proof (Hextra1 a1) as H. (* Hextra1 Hextra2 H *)
unfold Int256.modulus, two_power_nat. simpl.
unfold Z_bounded in *.
unfold unattainableWeiAmount, etherToWei in *.
lia.
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
Qed.

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
    (forall a,
      Int256Tree.get_default 0 a (ERC20WrappedEth_wrapped d)
        < unattainableWeiAmount) ->
    (MachineModel.me_callvalue me < unattainableWeiAmount) ->
    (ERC20WrappedEth__totalSupply d < unattainableWeiAmount) ->
    high_level_invariant d ->
    synth_func_cond ERC20WrappedEth_mint ERC20WrappedEth_mint_wf
                    me d.
Proof.
intros Hextra1 Hextra2 Hextra3.
intros.
unfold synth_func_cond.
simpl.
repeat split.
-
inversion H2.
destruct (Int256.eq
(@MachineModel.me_caller
   global_abstract_data_type
   me)
(@MachineModel.me_address
   global_abstract_data_type
   me)) eqn:Case; [simpl in H0; inversion H0|].
inversion H0.
destruct(Z.gtb
(@MachineModel.me_callvalue
   global_abstract_data_type
   me) Z0); [|simpl in H1; inversion H1].
inversion H1.
subst.
pose proof (Hextra1 (MachineModel.me_caller me)) as H3. (* Hextra1 Hextra2 H3 *)
unfold Int256.modulus, two_power_nat. simpl.
clear -Hextra1 Hextra2.
pose proof (Hextra1 (MachineModel.me_caller me)).
unfold Z_bounded in *. simpl in *.
unfold unattainableWeiAmount, etherToWei in *.
lia.
- 
inversion H4.
inversion H3.
inversion H2.
destruct(Z.gtb
(@MachineModel.me_callvalue
   global_abstract_data_type
   me) Z0); [|simpl in H1; inversion H1].
inversion H1.
destruct (Int256.eq
(@MachineModel.me_caller
   global_abstract_data_type
   me)
(@MachineModel.me_address
   global_abstract_data_type
   me)) eqn:Case; [simpl in H0; inversion H0|].
inversion H0.
subst.
destruct m2. simpl in *.
clear -Hextra2 Hextra3. (* Hextra2 Hextra3 *)
unfold Int256.modulus, two_power_nat. simpl.
unfold unattainableWeiAmount, etherToWei in *.
lia.
Qed.

Lemma ERC20WrappedEth_mint_oblg me d :
    high_level_invariant d ->
    synth_func_obligation ERC20WrappedEth_mint ERC20WrappedEth_mint_wf
                          me d.
Proof.
code_proofs_auto.
Qed.

Lemma ERC20WrappedEth_burn_vc a0 me d :
   (forall (a:Int256Tree.elt),
      ERC20WrappedEth__totalSupply d
      >=
      Int256Tree.get_default 0 a (ERC20WrappedEth_wrapped d))
   ->
    ht_ft_cond a0 -> ht_valid_ft_cond a0 ->
    high_level_invariant d ->
    synth_func_cond ERC20WrappedEth_burn ERC20WrappedEth_burn_wf
                    a0 me d.
Proof.
intros Hextra1.
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
remember ((@Int256Tree.get_default
(@Z_bounded Int256.modulus modulus_bound) Z0
(@MachineModel.me_caller global_abstract_data_type me)
(ERC20WrappedEth_wrapped m3))) as wrapped_amount.
inversion H7.
inversion H6.
destruct(Z.eqb
(@MachineModel.me_callvalue
   global_abstract_data_type
   me) Z0); [|simpl in H4; inversion H4].
inversion H4.
destruct (Int256.eq
(@MachineModel.me_caller
   global_abstract_data_type
   me)
(@MachineModel.me_address
   global_abstract_data_type
   me)) eqn:SCase; [simpl in H3; inversion H3|].
inversion H3.
destruct (a0 >=? 0); [|simpl in H2; inversion H2].
inversion H2.
subst.
clear -Hextra1 Case.
destruct m4. simpl in *.
pose proof (Hextra1 (MachineModel.me_caller me)) as H.
unfold Z_bounded in *. simpl in *. (* Hextra1 Case H *)
lia.
Qed.

Lemma ERC20WrappedEth_burn_oblg a0 me d :
    ht_ft_cond a0 -> ht_valid_ft_cond a0 ->
    high_level_invariant d ->
    synth_func_obligation ERC20WrappedEth_burn ERC20WrappedEth_burn_wf
                          a0 me d.
Proof.
code_proofs_auto.
Qed.


End EdsgerGen.