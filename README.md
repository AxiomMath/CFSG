# Classification of Finite Simple Groups in Lean
* [Website](https://cfsg.axiommath.ai/)

A sorry-free Lean4 (v4.35.0-rc3) proof of the Classification of Finite Simple Groups (CFSG), built on Mathlib and TauCeti, using the standard axioms `Classical.choice`, `propext`, and `Quot.sound` (no `native_decide`). We primarily follow the first generation proof of CFSG.

We use the [statement of CFSG from the TauCeti project](https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/GroupTheory/SpecificGroups/CFSG/Classification.lean#L52-L56)

```lean4
/-- **Classification of finite simple groups, statement only.** Every finite simple group is
isomorphic to one of the explicitly constructed groups on the classification list. -/
def ClassificationStatement : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] [IsSimpleGroup G],
    ∃ i : CFSGIndex, Nonempty (G ≃* i.Group)
```

## Checking the proof

`lake build` builds the entire project. We used a few open changes to Lake and some optimizations we plan to upstream soon to get this project's build time under 24 hours.

# License

APACHE-2.0
