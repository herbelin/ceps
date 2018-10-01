- Title: A light tactic-language type system for binders
- Driver: Hugo
- Status: Draft

## Summary and motivation

This ceps investigates the feasability of a type system for tracking
the scope of term-level bindings within Ltac1 and virtually Ltac2
functions. This would allow to track early ill-scoped code and to
enforce stronger invariants at runtime.

## Context

Ltac consider names occurring in term-level binders as binding names,
with a proper scope (though with some fragility, see below). It also
accepts to pass names of term-level binders as a variable (up to
suffix-based alpha-renaming).

On its side, Ltac2 consider names occurring in term-level binders as
pure identifiers without a notion of scope attached to them. 

## Examples currently supported

Examples supported by the Ltac approach:
- Build a term using a particular name
```coq
Ltac pick_in x H := destruct H as (x,H).
Lemma L (H : exists x, x = S x) : False.
pick_in witness H.

```

- Propagating a name from a statement to the other
```
Ltac sig_to_ex :=
 match	goal with
 |- exists x, ?P =>
   let H := fresh "H" in
   enough {x | P} as (y,H) by (econstructor; exact H)
 end.

Lemma L : exists some_integer, some_integer = 0.
sig_to_ex.
(* {some_integer : nat | some_integer = 0} *)
```

## Examples working badly

Also, the following currently fails

```coq
Ltac pick x := eexists ?[x].
Goal exists y, y = 0.
pick foo.
[foo]:exact 0.
auto.
Qed.
```
See however PR coq/coq#7309.

## Proposal

## Related issues

