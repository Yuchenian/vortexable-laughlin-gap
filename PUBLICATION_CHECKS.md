# Publication checks — 2026-10-16

**Historical release record.** Human verification was incomplete on 2026-10-16. For the current status, see [HUMAN_REVIEW.md](HUMAN_REVIEW.md); for the new execution results, see [RECHECK_20261024.md](RECHECK_20261024.md).

The six public research scripts were rerun from the assembled public directory using Julia 1.12.7 on Windows:

| Script | Passed checks |
|---|---:|
| channel_transfer_checks.jl | 102 |
| analytic_bound_checks.jl | 53 |
| independent_channel_audit.jl | 469 |
| nuclear_overlap_checks.jl | 156 |
| analytic_extension_checks.jl | 1013 |
| extension_bound_checks.jl | 37 |
| Total | 1830 |

The portable reference downloader fetched both pinned arXiv files, confirmed their SHA-256 values, and reran the upstream verifier successfully with exit code zero. The resulting exact gamma agrees with the archived research run.

Local relative document links, source-copy hashes, review notices, article math delimiters and absence of code blocks in the Chinese article were checked. The publication selection excludes local credentials, private account details, downloaded papers and unrelated projects.

Finite tests and packaging validation do not establish the draft's general analytic claims.
