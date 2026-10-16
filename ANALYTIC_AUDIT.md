> **AI-assisted research draft — human verification and independent peer review are incomplete.** New proof claims remain provisional. See [HUMAN_REVIEW.md](HUMAN_REVIEW.md).

# Analytic audit of the loss-channel argument

Audit date: 2026-10-16. Scope: independent algebraic review of the candidate transfer proof, its normalization/domain issues, and operational frame extensions. Existing originals were left unchanged; the complete revised proof is in TRANSFER_THEOREM_REVISED.md. External literature and numerical spectrum checks are handled in their own audit files. Numerical values of gamma0 in applications must follow the reference theorem's verified geometry and sector range.

## 1. Main finding and earliest possible failure points

I found no counterexample to the original loss-channel theorem under its actual hypotheses: a bounded pair projection with a localized decomposable frame, a reference full-Fock inequality, and a positive one-particle contraction. The direction of the CP argument and the two relative-noise estimates are correct. The old plane C=20 and sphere C=28 bounds are conservative but valid.

The original text had incomplete justifications at three places, rather than an identified false main inequality:

1. Checking finitely many angular-momentum blocks was not an all-K proof of the plane frame normalization. The full binomial-moment identity now supplies that proof.
2. The phrase “finite linear combinations of frame labels” is not an adequate dense-core statement for a continuous L² label space. Bounded sectorwise pair forms, measurable exhaustion, and bounded synthesis now supply the closure argument.
3. Merely writing `zf phi=fz phi` on a dense set would not establish invariance on the maximal unbounded multiplication domain for a nodal multiplier. A bounded-commutator/Neumann-series argument now proves the exact maximal-domain equality on the plane.

The theorem would fail to be justified at an earlier step if the quoted reference gap only held at fixed target N: the dilation uses all reference sectors from 0 to N. That external condition is kept explicit and must be checked separately. No amount of finite-N channel tests repairs a missing reference-sector input.

## 2. Claim-by-claim findings

| Candidate claim | Audit result | Reason or repair |
|---|---|---|
| Phi_M(H0)=H_M | Supported | Environment annihilators kill the vacuum in the normally ordered pair interaction. |
| Phi_M(H0²)=H_M²+X1†X1+X2†X2 | Supported | H0(b) acting on vacuum creates at most two environment particles; different environment sectors are orthogonal. |
| Use of CP/Kadison | Correct when variance is retained | CP transfers the reference inequality. Kadison alone points the unhelpful way and is not used to infer a gap. |
| Complex coefficients | Supported | B(p) is antilinear in p; the creation/synthesis column is linear in p. These conjugations cancel appropriately in B†B. |
| Graded signs | Supported with explicit convention | In environment-first tensor order, system creation is environment parity times c†. The one-environment column is Eu tensor c†(Mv) minus Ev tensor c†(Mu). |
| Two-environment coefficient | Supported | Normalized wedges give no extra 2. `\|\|wedge²E\|\|²<=delta²`. |
| Nonprojection Q | Supported extension | Replace the second-noise coefficient 1 by beta=||Q||. |
| One-environment bound | Supported and strengthened | An SVD of two-frame overlap gives nuclear norm in place of the entrywise sum. |
| Plane frame normalization | Supported for all K | Binomial variance gives exactly unit norm in every K>=1 block. |
| Sphere frame normalization | Supported for all Q>=1 | Haar average in pair spin Q-1, dimension 2Q-1; Q=1 is a legitimate one-dimensional pair space. |
| Infinite h and all N | Supported after domain proof | All operations are bounded on total-particle sectors <=N; constants then pass to the direct sum unchanged. |
| Same kernel under an invertible filter | Supported | Exact intertwining with wedge^N M; no estimate of its exponentially growing inverse norm is used. |
| Scalar contact weight | Supported | Derivative-of-f terms multiply the identical-point field square, which vanishes; the remaining weight is |f|⁴. |
| Gap comparison via H_f>=lambda H_M | Supported with common kernel | Two-sided form comparison supplies equal kernels; compare on their common orthogonal complement, never square an operator inequality. |
| Nodal smooth scalar f | Supported under Gram and pair coercivity | Inverse multiplication by f is unnecessary. A new Fourier-checkable example has zeros and still has both coercivities. |
| All vortexable bands | Unsupported | No representation/coverage theorem supplies the required quantitative Gram and pair-frame data. |
| Finite torus gap from plane | Unsupported inference | The algebra transfers a separately proved torus input; the plane input alone does not supply it. |

## 3. Grading, conjugation, and CP in full detail

Use complex inner products antilinear in the first argument. In `p=sum p_ij e_i wedge e_j`, pair annihilation is `B(p)=sum conjugate(p_ij)c_j c_i`. For a positive Hermitian M, `c(M e_i)=sum_j M_ij c_j`, because annihilation is antilinear and `conjugate(M_ji)=M_ij`. This is why a matrix row in a finite implementation can correctly represent the filtered annihilator; using the same expression for a general non-Hermitian M without checking conventions would be unsafe.

In `F_env tensor F_sys`, let system odd operators carry `(-1)^N_env`. Then

`b(v)=(-1)^N_env tensor c(Mv)+d(Ev) tensor I`.

The one-particle block matrix with columns `(E,M)` and `(M,-E)` is unitary because E and M commute and `E²+M²=I`. Its ordinary fermionic second quantization implements the dilation also in infinite one-particle dimension; there is no particle/antiparticle Bogoliubov transformation or extra implementability hypothesis. It preserves total particle number.

For one normalized decomposable p=u wedge v, the two annihilations on environment vacuum leave `B(Mu wedge Mv)psi`. Applying the two creations yields environment amplitudes

`vacuum: c†(Mu)c†(Mv)`,
`one: Eu tensor c†(Mv)-Ev tensor c†(Mu)`,
`two: Eu wedge Ev`.

For a finite Slater sum, creation coefficients are the original lambda while B contains conjugate(lambda). This proves the three components and the variance identity independently of real-basis conventions. Reversing tensor order introduces a harmless parity unitary in the one-environment term, not a change in its squared norm.

Vacuum compression of the unitary-conjugated reference operator is CP. On total-particle sectors up to N, the conjugated reference H0 acts on a subsystem with anywhere from 0 to N particles and spectators elsewhere. Reference positivity in these sectors therefore transfers. H0² is not replaced by H_M²: the difference is precisely the two positive noise terms.

## 4. The improved one-environment estimate

For a two-frame U=[u,v], let `R_U=u tensor c†(Mv)-v tensor c†(Mu)`. A 2-by-2 unitary change of frame A gives `R_(UA)=det(A)R_U`. This holds even when M is nonlocal and has arbitrary matrix elements; M is linear and need not commute with A.

Take an SVD of U_x†U_y by independent changes of the two frames. Up to an irrelevant phase, its Gram operator becomes the sum of two products of fermionic operators with coefficients equal to the two singular values. Each product has norm <=1 because M is a contraction. Thus

`||R_x†R_y||<=||U_x†U_y||_1`.

This improves the original four-entry triangle bound without changing the loss-channel construction or introducing an N-dependent estimate. The operator-valued Schur test applies after first taking the full environment factor E outside the synthesis operator; it never assumes E preserves spatial localization.

For the plane, with t=|alpha-beta|²,

`||U_alpha†U_beta||_1=exp(-t/2)sqrt(t²+4)`.

Its Schur integral is bounded by Cauchy--Schwarz as `C_plane<=8sqrt(3)<14`. The exact integral is about 12.310898279, but the theorem uses the analytic upper bound, not that floating value.

For flux Q on the sphere, with s=sin²(theta/2), the corresponding trace norm is

`(1-s)^((Q-2)/2)sqrt[4(1-s)+(Q-1)²s²]`.

Weighted Cauchy--Schwarz gives

`C_Q<=[2(2Q-1)/Q]sqrt[(12Q²+8)/((Q+2)(Q+4))]<8sqrt(3)<14`.

This includes Q=1: the apparent endpoint singularity is removable, the two-frame overlap is unitary, its trace norm is 2, and C_1=2. For Q=2, C_2=9/2. There is no small-Q exception to the transfer estimate; only the external reference-gap theorem may have its own minimum flux.

## 5. Why there is no hidden N, volume, or cutoff factor

* `||c(v)||=||v||` is the full fermionic Fock norm; no bosonic sqrt(N) bound is being inserted.
* S has norm sqrt(beta), determined by the two-particle frame operator, rather than by the number or area of frame labels.
* The R bound is a local overlap integral. The reference plane Gaussian integral and sphere estimate are uniform in area/flux.
* On each total-particle sector, `L2(Q)` is bounded by `beta binomial(N,2)`. This N-dependent bound only justifies definitions and limits. It is not the final noise bound: both noises are bounded by constants times H_M itself.
* The dilation preserves total N, so the sectorwise bounded calculations are exact. Taking their direct sum gives the same positive gap constant; no cutoff-continuity conjecture enters.
* The inverse exterior power is used solely to identify zero modes. Its condition number never appears in an energy comparison.

For continuous frames, one should truncate by finite-measure label sets with bounded columns, not use frame-label delta functions as an alleged L² core. Strong convergence of positive pair operators and the bounded maps A_M, S, R supply the closure. The revised theorem includes this argument.

## 6. All-K normalization, rather than a finite check

In the plane block K=i+j the proposed normalized vector has squared norm

`[(K-1)!/2^(K-1)]sum_(i<K/2)(K-2i)²/[i!(K-i)!]`.

Using `sum_(i=0)^K (K-2i)²binomial(K,i)=K2^K`, equal paired terms on either side of K/2, and the vanishing central term, this equals exactly 1 for every K>=1. The coherent center factor then identifies the projector range as all relative-angular-momentum-one states. The factor two in `dnu=2d²alpha/pi` is essential and was present in the candidate.

On the sphere, u wedge v is the highest pair state with total spin Q-1. Its normalized coherent Haar average is the identity on that irreducible sector divided by its dimension 2Q-1. The candidate measure `(2Q-1)dg` is therefore correct.

## 7. Physical checks and the new coercivity route

The fixed physical isotropic derivative contact in plane pair-projector units has coefficient `4pi ell^4` in front of `integral sum_(j=x,y)(Psi partial_j Psi)†(Psi partial_j Psi)d²r`. At the origin, `Psi partial_x Psi=-(2sqrt(2)pi ell³)^(-1)c_1c_0`, and the y amplitude is i times it. This gives exactly `d²R/(pi ell²)` times the normalized pair projector. I checked this coefficient independently.

The sphere finite-Q coefficient is different: on radius R it is `c_Q=8pi R^4(2Q-1)/[Q(Q+1)²]` for the sum over two orthonormal tangent derivatives. At the north pole the pair amplitude in either tangent direction has modulus `sqrt(Q)(Q+1)/(8pi R³)`, so the squared sum is `Q(Q+1)²/(32pi²R^6)`; multiplication by c_Q gives the frame density `(2Q-1)/(4pi R²)`. In particular c_1=2pi R^4. With `ell²=2R²/Q` the coefficient tends to `4pi ell^4`, but this limit is not the finite-Q normalization. The revised theorem now states this distinction explicitly.

The scalar pullback by `U=fG^(-1/2)` multiplies the pair amplitude by f², hence the energy by |f|⁴. A positive pointwise lower bound is sufficient but not necessary. On the pair projector's range, a positive weighted-frame lower bound `Q_|f|⁴>=kappa Q` provides the needed energy comparison directly.

The pair center coherent coordinate is `(R_x+iR_y)/ell`, so its anti-Wick Fourier attenuation is `exp(-q²ell²/8)`, whereas the one-particle Gram attenuation is `exp(-q²ell²/4)`. For `f=2cos(kx)cos(ky)`, `k=sqrt(2pi)/ell`, this yields

`||G-I||<=2e^(-2pi)+e^(-4pi)`,
`kappa>=9/2-[3/2+2e^(-pi)+(1/2)e^(-4pi)]²`.

The rational replacements r<=1/500 and t<=1/23 used in the examples are in the conservative direction. Thus this smooth nodal f genuinely escapes the old strictly positive scalar class while retaining a usable Gram inverse and common zero space. It should not be replaced by |f|, which would sacrifice smoothness at nodes, nor described using a globally smooth nonsingular logarithmic Kähler potential.

The additional geometric calculation in PHYSICAL_EXTENSIONS.md was also checked: for `U_F phi=sqrt(J)phi(F(r))`, ordinary isotropic derivative contact pulls back to pair weight `J||DF||_F²/2`. There are two powers of J from the two projected fields and one inverse J from the measure; the remaining factor 1/2 compares the two equal LLL derivative channels. The stated area-preserving shear has weight `1+(a_s²/2)cos²(ky)`. This check is separate from the loss-channel theorem.

## 8. Maximal vortex-coordinate domain for nodal multipliers

The identity zf=fz is not by itself sufficient if f has zeros and z is unbounded. The following closes that issue for the plane class used here.

The LLL kernel gives a bounded commutator `[z,P0]`: its absolute integral kernel is `|z-w|(2pi ell²)^(-1)exp(-|z-w|²/(4ell²))`, with Schur integral `2sqrt(pi)ell`. Thus P0 preserves the maximal ambient multiplication domain D(z).

For any bounded scalar f, G=P0|f|²P0 preserves `D0=h0 intersect D(z)` and `[z,G]` is bounded there. If `g_-I<=G<=g_+I`, choose c>=g_+ and T=I-G/c. Since ||T||=r<1, the n-th commutator is bounded by `n r^(n-1)||[z,T]||`. The inverse Neumann series therefore converges in the graph norm of z, showing that G^-1 preserves D0.

If `psi=f phi in h_f intersect D(z)`, then `G phi=P0 conjugate(f)psi` lies in D0; applying G^-1 yields phi in D0. Hence

`h_f intersect D(z)=f D0`.

Therefore z leaves h_f invariant on its entire maximal multiplication domain. Neither a pointwise inverse f nor a finite Fourier assumption is needed for this domain statement. Smoothness is a separate assumption when defining the physical derivative-contact fields. This result is not automatically a statement about a global stereographic coordinate on a fixed-flux sphere.

## 9. Genuine abstract extensions and an open reference problem

The revised theorem allows beta!=1, multiple contact channels, nonorthogonal decomposable presentations, and finite Slater rank. Its hypothesis is an explicit one-particle overlap kernel or a finite near-region interval bound plus a controlled integrable tail. It does not postulate the desired relative-noise estimate.

There are two instructive nondecomposable examples:

* Disjoint four-mode cells with `p_j=(e_j1 wedge e_j2+e_j3 wedge e_j4)/sqrt(2)` have a fully proved reference gap 1/2, beta=1, and C=2, for any number of cells. Local spectra are 0,1/2,1; the exact rational matrix polynomial `H(H-I/2)(H-I)=0` independently checks this. Bounded positive cell weights give a genuine nonprojection extension. This is an abstract algebraic validation family, not a fermionic 1/3-Laughlin model.
* A same-LLL translated rank-two pair `(D|0> wedge D|1>+D|2> wedge D|3>)/sqrt(2)` has `beta=(7+2sqrt(11))/16` and an explicit C<=336, calculated from Gaussian/Laguerre overlap tails. Its reference Hamiltonian includes relative channels 1,3,5 with off-diagonal mixing. Its full-Fock gap is not established here. The stronger frame theorem is applicable only conditionally, and comparison with V1 alone does not close the problem because the kernels differ.

These examples separate an actual proved extension of the algebra from an unproved new physical gap claim. Multiple channels or finite Slater rank by themselves do not ensure small C, a positive gamma0, a Laughlin kernel, or the desired filling.

## 10. New computations, failure evidence, and reproduction

New source: analytic_extension_checks.jl. It uses Julia 1.12.7 standard libraries only, has no random inputs, and prints to stdout. Run from this project with

`& 'julia' --startup-file=no .\analytic_extension_checks.jl`

Final raw output is `audit_20261016/analytic_extension_checks_output.txt`. It reports 1013 passing assertions, mostly explicit sphere-bound substitutions for Q=1..1000; the all-Q proof is the algebra above, not that finite list. The plane numerical integral is diagnostic. The Slater overlap upper bound is rational arithmetic, and the four-mode spectral polynomial is checked exactly.

The first script run had two implementation/check-writing errors: Simpson quadrature at n=2 attempted an empty sum without an initial value, and an unreliably guessed expected loose Slater bound 1968 disagreed with the exact computed sum 336. The original failed source and raw log were preserved as `audit_20261016/analytic_extension_checks_initial_failed.jl` and `audit_20261016/analytic_extension_initial_failure.txt`. The fixes supply the empty-sum initializer and use the exact analytic sum 336. Neither failure was a counterexample to the transfer theorem, and neither is concealed as a successful test. The final script also adds the exact four-mode certificate.

No SDP optimization, new global environment, background long run, or edit outside the specified project was needed for this analytic subtask. This is an independent subagent implementation/review within the same research session, not independent external peer review or formal verification.
