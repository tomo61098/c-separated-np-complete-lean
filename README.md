# C-separated NP-complete relaxation

This repository is translating the accompanying Rocq development to Lean 4.
The completed Lean results are:

- `CSeparatedNPComplete.c_separates_zero`, the zero-selector lemma from `sepsolve.v`.
- `CSeparatedNPComplete.Karamata_inequality`, Karamata's inequality from `Karamata.v`
  for every finite dimension and every convex function on a convex domain.

Here `majorized u v` means **u majorizes v**: both vectors are descending,
every prefix sum of `u` is at least that of `v`, and their total sums agree.
Karamata concludes that the sum of `f` over `u` is at least its sum over `v`.
No continuity, differentiability, or strict convexity is assumed.

The proof follows the source's secant-slope argument using mathlib's
`ConvexOn.secant_mono`, `AntitoneOn.exists_antitone_extension`, and
`Finset.sum_range_by_parts`. The extension handles equal coordinate pairs
without deleting or reversing vectors. The library theorem
`CSeparatedNPComplete.majorized.sum_convex_le` accepts mathlib's `ConvexOn`
directly; the named Solution theorem retains the source's predicate notation.

The final `partition_gadget_schedule_partition_iff` theorem in `sepsolve.v`
has not yet been translated. Its Rocq proof uses a direct bound on
`1 / (1 + x)` and its equality case rather than invoking Karamata.
The reduction gadgets, schedule, and any NP-completeness conclusion remain
outside the completed Lean scope. The `.v` files are source material and
are not compiled by the Lean project.

## Build

```text
lake build
```

`Challenge.lean` independently states both results and their definitions,
importing only mathlib. Its two deliberate `sorry` placeholders are allowed
by the [Palomar submission guide](https://palomar-registry.org/how-to-submit).
`Solution.lean` imports the proved library, never `Challenge`; its theorems
have no `sorry` dependencies. `comparator.json` names both results and their
shared definitions. Local builds and axiom inspection are separate from a
full Comparator/Palomar verification, which has not been run.

This translation was developed with AI assistance and checked by Lean.
Independent human mathematical review is still pending. No submission has
been made from this local working tree.
