# Solving Side Conditions

DeepSEA generates side conditions such as those relating to ensuring no overflow/underflow occurs. These appear in the `Obj_____CodeProofs.v` file. When solving the side-conditions is really trivial, the following tactic will probably work.

```
Ltac code_proofs_auto :=
    intros;
    unfold synth_func_obligation;
    repeat (split; auto)
.
```