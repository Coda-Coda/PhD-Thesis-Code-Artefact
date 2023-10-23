(* WARNING: This file is generated by Edsger, the DeepSEA compiler.
            All modification will be lost when regenerating. *)
(* Module fpblind.LSrcEVMOPCODE for fpblind.ds *)
Require Import BinPos.
Require Import DeepSpec.Runtime.
Require Import fpblind.EdsgerIdents.
Require Import fpblind.DataTypes.
Require Import fpblind.DataTypeOps.
Require Import fpblind.DataTypeProofs.


Require Import fpblind.LayerEVMOPCODE.

Require Import cclib.Integers.
Require Import cclib.Coqlib.
Require Import cclib.Maps.

Require Import backend.Options.
Require Import backend.AST.
Require Import backend.phase.Clike.Language.
Require Import backend.phase.MiniC.Language.
Require Import backend.Cop.
Require Import backend.Ctypes.
Require Import backend.Compiled.
Require Import backend.Compiled.
Require Import backend.Globalenvs.
Require Import backend.Glue.


Section EdsgerGen.

Definition ge : genv := new_genv (nil)
	nil
	(nil)
	None.


End EdsgerGen.

(*change into extract directory*)
Cd "/Users/sxysun/Desktop/CertiK/DeepSEA/contracts/fpblind/fpblind/extraction".

(* Avoid name clashes *)
Extraction Blacklist List String Int.

Separate Extraction
    positive global_abstract_data_type  (* This line forces Coq to generate some files even if they are not used, to make the makefile work correctly. *)
    Glue.full_compile_genv
    ge.
