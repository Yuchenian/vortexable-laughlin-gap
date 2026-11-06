# Lean formalization of Laughlin gap transfer

The transfer theorem derives the loss-channel decomposition and both relative noise bounds from the fermionic CAR and the pair frame. The reference gap is an explicit parameter. The complete-plane examples can also use a checked upstream bound of 1/25. Results using 1/5 assume the reference inequality in the indicated sectors and geometry. On the sphere this condition applies at the stated flux.

## Read the proof

* [Finite-frame transfer](VortexGap/Transfer/FiniteFrame.lean) and [continuous-frame transfer](VortexGap/Transfer/HilbertContinuousFrame.lean)
* [Physical plane criterion](VortexGap/Physical/PlaneBandSpectrum.lean), [maximal coordinate domain](VortexGap/Physical/PlaneGramDomain.lean) and [full Fock space](VortexGap/Physical/OccupationSectorSum.lean)
* [Square-root stripe](VortexGap/Examples/WeakStripe.lean) with a closed gap above 0.037 for every nonzero wave number and every finite particle number
* [Projected sphere criterion](VortexGap/Physical/SphereProjectedGap.lean) and [sphere example with a node](VortexGap/Examples/SphereNodalCap.lean)
* [Author's handwritten verification notes (PDF)](../docs/verification/hand_written_note.pdf)

## Reproduce the checks

From the repository root, with elan and Python 3.12 or later available, run:

```sh
cd lean_formalization
python scripts/fetch_dependencies.py
lake build VortexGap
lake env lean VortexGap/Audit/Main.lean
lake env leanchecker --fresh VortexGap
```

The bootstrap downloads the pinned mathlib revision and its dependencies into the ignored local vendor directory. Allow several hours for a clean build and kernel replay. The [audit entry point](VortexGap/Audit/Main.lean) prints the theorem types and their axiom dependencies. The accepted run on Lean 4.34.1 checked 2,673 project theorems and 483 additional constructions. Its whitelist contains only `propext`, `Classical.choice` and `Quot.sound`. See the [run record](verification/acceptance-run.log), [kernel replay](verification/fresh-replay.log) and [source hashes](verification/sources.sha256).

The [vendored reference sources](vendor/upstream_audit/lean) come from [OpenAI's math repository at the audited revision](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae) and retain their [Apache 2.0 license](vendor/upstream_audit/LICENSE).
