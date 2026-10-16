> **Historical candidate snapshot; human review incomplete.** Consult the current root documents for revised claims. Local machine paths have been redacted in this public copy.

# Vortexable Laughlin gap project

Goal: transfer the full-Fock-space planar/spherical V1 gap certificate to a genuinely changed vortexable one-particle subspace. Do not substitute fixed-band interaction modulation for band deformation.

Rules:
- Keep rigorous algebra, published input theorems, floating-point sanity tests, and unproved extensions explicitly separated.
- A finite-N spectrum is NOT a thermodynamic gap certificate.
- Never use an extensive absolute error as a uniform gap bound.
- All new work stays in this directory. Existing SDP projects are read-only references.
- Scripts print results to stdout; archive selected outputs with explicit file writes.
- Initial environment: system Python 3.14 lacks numpy/scipy/cvxpy; Julia 1.12.7 and its standard libraries are available. Use standard-library Julia for small independent checks first.

Current candidate: fermionic vacuum-loss channel, applied to an already certified full-Fock inequality H0^2 >= gamma0 H0. Bound channel variance relative to the filtered parent Hamiltonian using a localized decomposable-pair frame. Check all normalization factors and channel identities before claiming a theorem.
