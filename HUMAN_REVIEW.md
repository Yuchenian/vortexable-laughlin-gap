# Review status — 2026-10-24

On 24 October 2026, Yuchen Liu reported that he had personally examined the main conclusions and calculations and found no obvious errors. This is his personal scientific judgment. It is not a claim of external peer review or exhaustive line-by-line formal verification.

The author takes responsibility for the scientific content and its verification. OpenAI's Codex was used extensively for the analytical derivations, verification programs, computational cross-checks, and writing. Internal analytic passes and separately written implementations are reproducibility checks within this project.

The follow-up [recheck](RECHECK_20261024.md) found no issue requiring a change to the main inequalities or displayed numerical lower bounds. It records the distinction between the actual channel loss and a conservative loss bound, a fresh run of all six Julia suites (1830 passing checks), and a successful rerun of the hash-pinned upstream exact verifier.

| Evidence | Status |
|---|---|
| Author's examination | Main conclusions and calculations personally checked; no obvious error found in the author's judgment |
| Transfer proof and physical comparison | Analytic derivations available; follow-up internal recheck recorded |
| Computational checks | Six Julia suites passed again; exact rational values independently recomputed with Python |
| External reference | Version, normalization, and plane/sphere scope checked; upstream exact verifier rerun successfully |
| External peer review / formal verification | Not claimed |

The mathematical results are statements for the explicit parent interactions and geometric hypotheses in the technical documents. A positive computed lower bound certifies a gap above the full kernel under those hypotheses. Material-specific interactions, finite-torus reference gaps, and topological stability require their own inputs.

The initial 16 October release correctly stated that human checking was incomplete at that time. Historical snapshots retain that dated status. This page records the subsequent author examination without assigning a checklist of specific actions to the author that he has not separately described. Corrections and counterexamples are welcome.
