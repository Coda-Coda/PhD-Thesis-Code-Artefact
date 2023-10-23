(* WARNING: This file is generated by Edsger, the DeepSEA compiler.
            All modification will be lost when regenerating. *)
(* Module spblind.Symbols for spblind.ds *)
Require Import BinPos.
Require Import DeepSpec.Runtime.
Require Import spblind.EdsgerIdents.
Require Import String.
Require Import List.
Require Import compcert.common.AST.
Section EdsgerGen.


Open Scope string_scope.

Definition symbols: list (ident * string) :=
  (ident_EVMOpcode_transfer, "EVMOpcode_transfer")::
  (ident_BlindAuction_initialize, "BlindAuction_initialize")::
  (ident_BlindAuction_transferb, "BlindAuction_transferb")::
  (ident_BlindAuction_reveal, "BlindAuction_reveal")::
  (ident_BlindAuction_bid, "BlindAuction_bid")::
  (ident_BlindAuction_withdraw, "BlindAuction_withdraw")::
  (ident_BlindAuction_auctionEnd, "BlindAuction_auctionEnd")::
  (var_BlindAuction__beneficiary_ident, "BlindAuction__beneficiary")::
  (var_BlindAuction__biddingEnd_ident, "BlindAuction__biddingEnd")::
  (var_BlindAuction__revealEnd_ident, "BlindAuction__revealEnd")::
  (var_BlindAuction__ended_ident, "BlindAuction__ended")::
  (var_BlindAuction__bids_ident, "BlindAuction__bids")::
  (var_BlindAuction__highestBidder_ident, "BlindAuction__highestBidder")::
  (var_BlindAuction__highestBid_ident, "BlindAuction__highestBid")::
  (var_BlindAuction__secondBid_ident, "BlindAuction__secondBid")::
  (var_BlindAuction__revealed_ident, "BlindAuction__revealed")::
  (var_BlindAuction__amountOf_ident, "BlindAuction__amountOf")::
  nil.

End EdsgerGen.
