(*WARNING: This file is generated by Edsger, the DeepSEA compiler.
          All modification will be lost when regenerating.

This file defines a function `contract_model` that can be used to build machine environments. *)

Require Import Crowdfunding.DataTypes.
Require Import Crowdfunding.DataTypeOps.
Require Import lib.Monad.StateMonadOption.
Require Import cclib.Maps.
Require Import cclib.Integers.
Require Import ZArith.
Require Import core.HyperTypeInst.
Require Import backend.MachineModel.
Require Import core.MemoryModel.
Require Import DeepSpec.lib.Monad.RunStateTInv.
Require Import Lia.
Require Import Coq.Bool.Bool.
Require Import Crowdfunding.LayerCONTRACT.

Module ContractModel.



Definition wei := Z.
Definition addr := int256.

Section Contract_Call_Context.
Context (contract_address : addr).
Record BlockchainState := mkBlockchainState {
  timestamp : int256;
  block_number : int256;
  balance : addr -> wei;
  blockhash : int256 -> int256;
  contract_state : global_abstract_data_type
}.
Record CallContext := mkCallContext
  {
    origin : addr;
    caller : addr;
    callvalue : wei;
    coinbase : int256;
    chainid : int256
  }.
(* 'Forall function calls: '*)
Context (blockchain_state : BlockchainState).
Context (call_context : CallContext).
Context
  (address_accepts_funds : option global_abstract_data_type -> addr -> addr -> wei -> bool).
Context (callvalue_bounded_prf : (0 <= callvalue call_context < Int256.modulus)%Z).
Context (balances_bounded_prf : forall a, (0 <= (balance blockchain_state) a < Int256.modulus)%Z).
Open Scope Z.
Definition noOverflowOrUnderflowInTransfer (sender recipient : addr) (amount : wei) (balances : addr -> wei) : bool := 
  (0 <=? amount)
  && (amount <? Int256.modulus)
  && ((balances sender) - amount >=? 0)
  && ((balances recipient) + amount <? Int256.modulus).
Close Scope Z.
Context (callvalue_transfer_condition_prf : noOverflowOrUnderflowInTransfer (caller call_context) contract_address (callvalue call_context) (balance blockchain_state) = true).

  Context {HmemOps: MemoryModelOps mem}.
  Context {memModelOps : MemoryModelOps mem}.

Delimit Scope int256_scope with int256.
Infix "+" := Int256.add : int256_scope.
Infix "-" := Int256.sub : int256_scope.
Infix "=?" := Int256.eq (at level 70, no associativity) : int256_scope.

Open Scope int256.
Definition update_balances sender recipient amount balances : (addr -> wei) :=
  (* Here the balances are updated without checking for overflows. Overflow checks must be done elsewhere. *)
  fun a => 
  if sender =? recipient then balances a else
    if a =? sender then ((balances sender) - amount)%Z else
     if a =? recipient then ((balances recipient) + amount)%Z
      else balances a.
Close Scope int256.

Local Obligation Tactic := idtac.
Program Definition make_machine_env : machine_env global_abstract_data_type
  := 
     let balances_during_call := (update_balances (caller call_context) contract_address (callvalue call_context) (balance blockchain_state)) in
     {| me_address := contract_address;
        me_origin := (origin call_context);
        me_caller := (caller call_context);
        me_callvalue := (callvalue call_context);
        me_coinbase := (coinbase call_context); 
        me_timestamp := (timestamp blockchain_state);
        me_number := (block_number blockchain_state);
        (* For me_balance, the assumption here is that the Checks-Effects-Interaction pattern is followed, so there are no balance reads after a transfer has occured. *)
        me_balance := balances_during_call;
        me_blockhash := (blockhash blockchain_state);
        me_transfer recipient amount d := 
          if (noOverflowOrUnderflowInTransfer contract_address recipient amount balances_during_call)
             && (address_accepts_funds (Some d) contract_address recipient amount)
          then (Int256.one, update_Outgoing_transfer_recipient_and_amount (Some (recipient, amount)) d)
          else (Int256.zero, d);
        me_callmethod _ _ _ _ _ _ _ _ _ _ := False;
        me_log _ _ d := d; (* TODO-Daniel what is the purpose of me_log? Is this a sufficient definition for now? *)
        me_chainid := (chainid call_context);
        me_valid := _
      |}.
Next Obligation.
split.
 - assumption.
 - unfold update_balances.
   intros.
   unfold noOverflowOrUnderflowInTransfer in *.
   destruct ((caller call_context =? contract_address)%int256).
   apply balances_bounded_prf.
   destruct (a =? caller call_context)%int256.
   split.
   apply andb_prop in callvalue_transfer_condition_prf.
   destruct callvalue_transfer_condition_prf.
   apply andb_prop in H. destruct H.
   apply andb_prop in H. destruct H.
   apply Z.geb_le in H1. lia.
   pose proof (balances_bounded_prf (caller call_context)). lia.

   destruct (a =? contract_address)%int256.
   apply andb_prop in callvalue_transfer_condition_prf.
   destruct callvalue_transfer_condition_prf.
   split.
   pose proof (balances_bounded_prf contract_address). lia.
   apply Z.ltb_lt in H0. lia.

   apply balances_bounded_prf.
Defined.


End Contract_Call_Context.

  

End ContractModel.