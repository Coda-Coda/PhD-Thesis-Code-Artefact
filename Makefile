all: deepsea crowdfunding erc20WrappedEther
	echo Done compiling Coq files.

deepsea:
	cd DeepSEA; make

crowdfunding: deepsea
	cd Chapter-5-Case-Study-Crowdfunding/Crowdfunding; make -f core.make

erc20WrappedEther: deepsea
	cd Chapter-6-Case-Study-ERC-20-Wrapped-Ether-Token/ERC20WrappedEth; make -f core.make

dsc: deepsea
	nix-shell contracts-full-shell.nix --command "cd DeepSEA; make edsger"

trivial-full: dsc
	nix-shell contracts-full-shell.nix --command "cd Trivial; rm -rf trivial; dsc trivial.ds coq; cd trivial; coqdep -f _CoqProject > .coqdeps.d; coq_makefile -arg '-quiet' -f _CoqProject -o core.make"
	cd Trivial/trivial; make -f core.make

crowdfunding-full: dsc
	nix-shell contracts-full-shell.nix --command "cd Chapter-5-Case-Study-Crowdfunding; rm -rf Crowdfunding; dsc Crowdfunding.ds coq; cd Crowdfunding; coqdep -f _CoqProject > .coqdeps.d; coq_makefile -arg '-quiet' -f _CoqProject -o core.make"
	cd Chapter-5-Case-Study-Crowdfunding/Crowdfunding; make -f core.make

erc20WrappedEther-full: dsc
	nix-shell contracts-full-shell.nix --command "cd Chapter-6-Case-Study-ERC-20-Wrapped-Ether-Token; rm -rf ERC20WrappedEth; dsc ERC20WrappedEth.ds coq; cd ERC20WrappedEth; coqdep -f _CoqProject > .coqdeps.d; coq_makefile -arg '-quiet' -f _CoqProject -o core.make"
	cd Chapter-6-Case-Study-ERC-20-Wrapped-Ether-Token/ERC20WrappedEth; make -f core.make

contracts-full: crowdfunding-full erc20WrappedEther-full
	echo "Done rebuilding and compiling contracts."