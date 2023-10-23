# The DeepSEA Language

This folder is essentially a fork of the [Shentu Chain DeepSEA repository](https://github.com/shentufoundation/deepsea).

The codebase in this folder **may only be used for educational, research or evaluation purposes, and not for commercial use**.
This is because the DeepSEA compiler includes files taken and modified from CompCert, so it is developed pursuant to the CompCert licence. Please see the [CompCert licence](./CompCert-LICENSE.txt) for the full details. You may also wish to look at the [INRIA CompCert research project website](https://compcert.org) or the [CompCert GitHub repository](https://github.com/AbsInt/CompCert).  

[The Shentu Chain webpage](https://www.shentu.technology/technology#deepsea)
has more information about the DeepSEA project, and there are blog posts [An Introduction to DeepSEA](https://www.certik.com/resources/blog/an-introduction-to-deepsea) and [How DeepSEA Works](https://www.certik.com/resources/blog/how-deepsea-works-with-an-example-token-contact).

-----

This directory contains the OCaml parts of the DeepSEA compiler. For the time being, we do not include the sources for the parts that are written in Coq, but we ship the OCaml files which were compiled from them.

In order to build it, use opam or Nix to install the prerequisites, and then run make:

```
opam install .
make edsger
mv _build/default/Edsger/edsger.bc dsc
```

OR

```
nix-shell
make edsger
mv _build/default/Edsger/edsger.bc dsc
```

To install the dependencies using Nix, run `nix-shell` from the root of this folder to install most dependencies without `opam` (install `npm` packages separately). Nix is a package manager available on Linux, macOS, and (via WSL) Windows. You can [get Nix here](https://nixos.org/guides/install-nix.html).