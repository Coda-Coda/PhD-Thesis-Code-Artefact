# Getting Started
## Codespaces + VSCoq (web)

*Note: Codespaces have free quotas but are not free in general, for more information see [here](https://docs.github.com/en/billing/managing-billing-for-github-codespaces/about-billing-for-github-codespaces).*

1. [![Open in GitHub Codespaces](https://github.com/codespaces/badge.svg)](https://codespaces.new/Coda-Coda/PhD-Thesis-Code-Artefact) Or [resume your existing Codespace](https://codespaces.new/Coda-Coda/PhD-Thesis-Code-Artefact?quickstart=1). It should take less than 5 minutes to create a new Codespace.
2. Open a `.v` file and use the keyboard shortcuts Alt+UpArrow and Alt+DownArrow to step forward and back through the proofs, and Alt+RightArrow to step forward up to the cursor. On macOS use Control+Option instead of Alt.
3. Delete the Codespace once you are finished, to avoid being charged for storage costs.

## Linux/macOS + CoqIDE via Nix (local)
1. Install Nix from https://nixos.org/download.
2. After cloning this repository, run `nix-shell` from inside the cloned folder. This should take less than 10 minutes the first time `nix-shell` is run and near-instant after that.
3. Run `make` from inside the cloned repository. On macOS, it may be necessary to first run `make` from inside the `DeepSEA` folder.
4. Run `coqide` and then open any of the `.v` files in CoqIDE to step through them interactively.

## Extra Steps to Rebuild Smart Contracts

The above steps only require Coq v8.14.1 but do not rebuild the smart contracts from the `.ds` source files.

To start a shell with a more complete set of dependencies (may take some time the first time it is run):

- Run `nix-shell contracts-full-shell.nix`.

To rebuild the smart contracts from source:

- Run `make contracts-full`.

To experiment with the `dsc` (the DeepSEA Compiler):

- Run `make dsc`.
- Run `dsc -h` to see usage. E.g. `dsc Crowdfunding.ds bytecode` (in the Chapter 5 folder).

## Windows/macOS/Linux Other Options (local)
1. Obtain Coq v8.14.1 and optionally CoqIDE from a package manager or through [opam](https://opam.ocaml.org/).
2. Clone this repository.
3. Run `make` from inside the cloned repository.
4. Run `coqide` and then open any of the `.v` files in CoqIDE to step through them interactively. Alternatively, install the [VSCoq Legacy](https://marketplace.visualstudio.com/items?itemName=coq-community.vscoq1) Visual Studio Code extension and step through the proofs interactively in [Visual Studio Code](https://code.visualstudio.com/).

-------

Note: At some points during the proofs, the comments, e.g. `(* H1 *)`, contain the names of hypotheses of particular interest at that point in the proof.

-------

# Relevant Links for Chapter 4
## Section 4.1 "Coping with Reentrancy"

- [DeepSEA/core/Syntax.v (starting line 560)](https://github.com/Coda-Coda/PhD-Thesis-Code-Artefact/tree/main/DeepSEA/core/Syntax.v#L560) has the definition of the inductive proposition that defines the notion of a command following the *Checks-Effects-Interactions Pattern*.

- [DeepSEA/Runtime.v (starting line 895)](https://github.com/Coda-Coda/PhD-Thesis-Code-Artefact/tree/main/DeepSEA/Runtime.v#L895) has the definitions of the tactics used to automatically prove that a command follows the *Checks-Effects-Interactions Pattern*.

- [DeepSEA/Edsger/coqgen.ml (starting line 2591)](https://github.com/Coda-Coda/PhD-Thesis-Code-Artefact/tree/main/DeepSEA/Edsger/coqgen.ml#L2591) has the OCaml code which generates the proof obligations related to following the *Checks-Effects-Interactions Pattern* for each command. Obligations relating to calls to other functions within a smart contract (`CCcall`) are also facilitated by this `coqgen.ml` code.

- [Chapter-5-Case-Study-Crowdfunding/Crowdfunding/LayerCONTRACT.v (starting line 371)](https://github.com/Coda-Coda/PhD-Thesis-Code-Artefact/blob/main/Chapter-5-Case-Study-Crowdfunding/Crowdfunding/LayerCONTRACT.v#L371) has a concrete example of a generated proof obligation with its proof, relating to the `donate` function in the Crowdfunding smart contract following the *Checks-Effects-Interaction pattern*.

## Section 4.2 "Modelling a Blockchain"
The following links are to line numbers within [Crowdfunding.v](https://github.com/Coda-Coda/PhD-Thesis-Code-Artefact/blob/main/Chapter-5-Case-Study-Crowdfunding/proofs/Crowdfunding.v).

 - Statement of the _donation preserved_ lemma
   - [`since_as_long`, `donation_recorded`, `no_claims_from` (starting line 593)](https://github.com/Coda-Coda/PhD-Thesis-Code-Artefact/blob/main/Chapter-5-Case-Study-Crowdfunding/proofs/Crowdfunding.v#L593).
   - [`donation_preserved` (starting line 672)](https://github.com/Coda-Coda/PhD-Thesis-Code-Artefact/blob/main/Chapter-5-Case-Study-Crowdfunding/proofs/Crowdfunding.v#L672).
- [Section variables for the model (starting line 280)](https://github.com/Coda-Coda/PhD-Thesis-Code-Artefact/blob/main/Chapter-5-Case-Study-Crowdfunding/proofs/Crowdfunding.v#L280).
- [Example of an assumption (starting line 294)](https://github.com/Coda-Coda/PhD-Thesis-Code-Artefact/blob/main/Chapter-5-Case-Study-Crowdfunding/proofs/Crowdfunding.v#L294).
- [Initial state of the model (starting line 336)](https://github.com/Coda-Coda/PhD-Thesis-Code-Artefact/blob/main/Chapter-5-Case-Study-Crowdfunding/proofs/Crowdfunding.v#L336).
- [Action dependent on the current blockchain state (starting line 446)](https://github.com/Coda-Coda/PhD-Thesis-Code-Artefact/blob/main/Chapter-5-Case-Study-Crowdfunding/proofs/Crowdfunding.v#L446).
- [Step function (starting line 484)](https://github.com/Coda-Coda/PhD-Thesis-Code-Artefact/blob/main/Chapter-5-Case-Study-Crowdfunding/proofs/Crowdfunding.v#L484).


--------

Please be aware of the licenses which apply to this repository. See [LICENSE](./LICENSE).

The DeepSEA compiler is partly based upon the CompCert verified compiler developed as a part of the INRIA CompCert research project. Please see https://compcert.org/ for more information about CompCert.

Please also note that the files in the subfolder [DeepSEA](./DeepSEA/) in particular are the combined work of all those involved in the development of DeepSEA. Those involved with the development of DeepSEA (targeting the EVM) include at least Vilhelm Sjöberg, Kinnari Dave, Daniel Britten, Maria A Schett, Xinyuan Sun, Qinshi Wang, Sean Noble Anderson, Steve Reeves, and Zhong Shao. These are the authors of the paper "*Foundational Verification of Smart Contracts through Verified Compilation*" available on arXiv at https://arxiv.org/abs/2405.08348. Please see this paper for a discussion of DeepSEA's verified compilation.

The remaining files, excluding those generated by `dsc`, are primarily my (Daniel Britten's) work.
The files generated by `dsc` are:
- The files in the folder: [Chapter-5-Case-Study-Crowdfunding/Crowdfunding](./Chapter-5-Case-Study-Crowdfunding/Crowdfunding/).
- The files in the folder: [Chapter-6-Case-Study-ERC-20-Wrapped-Ether-Token/ERC20WrappedEth](./Chapter-6-Case-Study-ERC-20-Wrapped-Ether-Token/ERC20WrappedEth/).
- The proof goals for the side-conditions proved in [Chapter-5-Case-Study-Crowdfunding/proofs/ObjCrowdfundingCodeProofs.v](./Chapter-5-Case-Study-Crowdfunding/proofs/ObjCrowdfundingCodeProofs.v). See [Chapter-5-Case-Study-Crowdfunding/Crowdfunding/ObjCrowdfundingCodeProofs.v](./Chapter-5-Case-Study-Crowdfunding/Crowdfunding/ObjCrowdfundingCodeProofs.v) for the original file generated by `dsc`.
- The proof goals for the side-conditions proved in [Chapter-6-Case-Study-ERC-20-Wrapped-Ether-Token/proofs/ObjERC20WrappedEthCodeProofs.v](./Chapter-6-Case-Study-ERC-20-Wrapped-Ether-Token/proofs/ObjERC20WrappedEthCodeProofs.v). See [Chapter-6-Case-Study-ERC-20-Wrapped-Ether-Token/ERC20WrappedEth/ObjERC20WrappedEthCodeProofs.v](./Chapter-6-Case-Study-ERC-20-Wrapped-Ether-Token/ERC20WrappedEth/ObjERC20WrappedEthCodeProofs.v) for the original file generated by `dsc`. The original file does not include some additional assumptions made, relating to very high amounts of wrapped ether being unattainable, as well as making the information from the lemma `total_supply_correct` from [Chapter-6-Case-Study-ERC-20-Wrapped-Ether-Token/proofs/ERC20WrappedEth.v](./Chapter-6-Case-Study-ERC-20-Wrapped-Ether-Token/proofs/ERC20WrappedEth.v) available for the proof of the `burn` verification condition.