# Vortexable Laughlin gap: transfer bounds and examples

> **AI-assisted research draft. Human verification and independent peer review are incomplete.**
> The new proofs and constants in this repository are provisional claims. Passing checks is not a proof of a thermodynamic gap.
>
> **人工逐项检查与独立同行评审尚未完成。** 本项目公开推导、检查程序和失败证据，供研究者审查；请勿将其表述为已获独立验证的定理。

[中文科普文章（无代码）](ZHIHU_ARTICLE.md) · [Review status](HUMAN_REVIEW.md) · [Revised proof](TRANSFER_THEOREM_REVISED.md) · [Examples](EXAMPLES_AND_BOUNDS.md)

This project studies how a reference fermionic Laughlin V1 spectral inequality can be transferred to genuinely changed vortexable one-particle subspaces. It uses a vacuum-loss channel and bounds its variance relative to the filtered parent Hamiltonian, avoiding an exponentially growing many-body condition number.

The reference input is Gao's [arXiv:2610.12700v1](https://arxiv.org/abs/2610.12700v1), with conservative gap 1/5 in pair-projector units. The planar statement concerns the complete, untruncated plane and every finite particle sector; the spherical statement requires sufficiently large flux with a threshold independent of particle number. **No finite-torus reference theorem is assumed.** We reran the author's exact certificate verifier; we did not independently formalize or reprove the external paper.

## Main draft claims

For a bounded invertible one-particle filter, the channel estimate is

$$
H_M^2\geq[\gamma_0-C\delta-\beta\delta^2]H_M.
$$

Here delta measures filter loss, beta is the two-body frame bound, and C controls integrated local pair overlap. For the normalized plane and sphere V1 frames the draft derives C ≤ 8√3 < 14 and beta=1. For scalar deformations with a positive Gram lower bound, a weighted pair-frame lower bound kappa then gives

$$
\Delta_f\geq\frac{\kappa}{g_-^2}
\left[\frac15-14\delta-\delta^2\right],
\qquad \delta=1-\frac{g_-}{g_+}.
$$

These bounds concern the entire zero-mode space and a specified derivative-contact parent interaction. All entries below are subject to the pending proof review.

| Example | Draft positive lower bound | Scope |
|---|---:|---|
| Weak first-harmonic scalar deformation | 0.139077… | Complete plane |
| Stronger second-harmonic scalar deformation | 0.043092… | Complete plane |
| Smooth spherical deformation with amplitude ≤0.001 | 0.172024… | Sufficiently large flux |
| Smooth signed multiplier with nodal lines | >0.1763 | Complete plane; no pointwise positive lower bound |
| Finite-amplitude, area-preserving periodic shear | ≥0.2 | Complete plane; changed vortex coordinate |

No experimental Coulomb gap, universal C=1 theorem, finite-torus degeneracy, or topological phase stability is established. AC bands, chiral twisted bilayer graphene and twisted TMDs motivate the broader question; the positive bounds above concern the explicitly specified parent models.

## Read the work

| File | Purpose |
|---|---|
| [ZHIHU_ARTICLE.md](ZHIHU_ARTICLE.md) | Chinese explanation, including AC bands, chiral TBG, TMD motivation, and references |
| [AUDIT_REPORT.md](AUDIT_REPORT.md) | Claims, checks, corrections, and limitations |
| [TRANSFER_THEOREM_REVISED.md](TRANSFER_THEOREM_REVISED.md) | Hypotheses, channel proof, normalization, constants, and domains |
| [PHYSICAL_EXTENSIONS.md](PHYSICAL_EXTENSIONS.md) | Actual contact interaction, nodal weights, orbital embeddings, and geometry |
| [EXAMPLES_AND_BOUNDS.md](EXAMPLES_AND_BOUNDS.md) | Models and exact numerical lower bounds |
| [GENERALIZATION_MAP.md](GENERALIZATION_MAP.md) | Covered classes and unresolved extensions |
| [LITERATURE_AUDIT.md](LITERATURE_AUDIT.md) | External theorem versions, scope, and verifier provenance |
| [ANALYTIC_AUDIT.md](ANALYTIC_AUDIT.md), [NUMERICAL_AUDIT.md](NUMERICAL_AUDIT.md) | Separate analytic and implementation checks |
| [FINAL_STATUS.md](FINAL_STATUS.md) | Research-stage summary; read alongside the public review status |

The original candidate is retained in [PROOF_DRAFT.md](PROOF_DRAFT.md) and [audit_20261016/originals](audit_20261016/originals). It uses older constants. Failed implementations and negative examples remain in the audit record.

## Reproduce

Install Julia 1.12 (tested with 1.12.7). All local checks use Julia standard libraries; no solver, package installation, or external download is needed.

~~~sh
julia --startup-file=no --history-file=no --project=. run_checks.jl
~~~

Each script runs in a separate process. The runner writes a new directory under results, records source hashes and stops on failure. Archived research checks: 102 original channel, 53 original analytic, 469 independent implementation, 156 overlap, 1013 analytic extension and 37 exact bound checks.

To fetch the external reference certificate and verifier at the pinned version, verify their SHA-256 hashes, and optionally rerun them:

~~~sh
python scripts/fetch_reference.py
python scripts/fetch_reference.py --verify
~~~

Python uses only its standard library. The verifier is the upstream author's implementation. Files are downloaded into an ignored third_party directory; papers and third-party source caches are not redistributed here. See [THIRD_PARTY.md](THIRD_PARTY.md).

Windows convenience wrapper:

~~~powershell
powershell -NoProfile -File .\run_full_audit.ps1 -SkipReferenceCertificate
~~~

Omit that switch to also download, hash-check, and run the reference verifier. The cross-platform Julia command is the primary entry point.

## Public edition and license

The public edition removes local machine paths, adds review warnings, and provides portable runners. Numerical implementations are copied byte for byte. [PUBLICATION_PROVENANCE.json](PUBLICATION_PROVENANCE.json) maps original and published hashes; [PUBLICATION_NOTES.md](PUBLICATION_NOTES.md) explains the archive.

Original repository material is released under the [MIT License](LICENSE). External papers, data and software retain their own rights and licenses. If citing this work, include the commit and its **AI-assisted, human-verification-incomplete** status. Corrections and counterexamples are welcome through GitHub issues.
