> **AI-assisted research draft — human verification and independent peer review are incomplete.** New proof claims remain provisional. See [HUMAN_REVIEW.md](HUMAN_REVIEW.md).

# A revised loss-channel transfer theorem

Research derivation and audit, 2026-10-16. This document supplies the algebraic proof independently of any numerical value assigned to the reference gap. The literature audit and original-certificate replay are separate evidence for applying the theorem to planar/spherical V1. The theorem is not a claim about every vortexable band, a finite torus without its own reference input, or a specified topological phase.

## 1. Conventions and hypotheses

Let h be a separable complex one-particle Hilbert space. Inner products are antilinear in their first argument. Fermionic annihilation c(v) is antilinear in v, creation c†(v) is linear, and `{c(v),c†(w)}=<v,w>`. The normalized exterior product satisfies `||u wedge v||=1` for orthonormal u,v. Write

`B(p)=sum_(i<j) conjugate(p_ij)c(e_j)c(e_i)`

for `p=sum_(i<j)p_ij e_i wedge e_j`. For a bounded positive two-particle operator Q, `L2(Q)|N=sum_(i<j)Q_ij`, with coefficient one per unordered particle pair; thus `||L2(Q)|N||<=binomial(N,2)||Q||`.

Let (X,nu) be sigma-finite, p_x a strongly measurable pair frame, and assume its synthesis operator

`S a=integral p_x a(x)dnu(x)`, `Q=SS†`, `0<=Q<=beta I`

is bounded. An orthogonal projection Q is allowed but is not required. Suppose each p_x has a specified finite decomposable expansion

`p_x=sum_a lambda_(x,a) u_(x,a) wedge v_(x,a)`,

where u_(x,a),v_(x,a) are orthonormal within each pair. Different pairs in this sum need not be mutually orthogonal. Let U_(x,a):C²->h have these two columns, and define the nonnegative symmetric kernel

`k(x,y)=sum_(a,b)|lambda_(x,a)||lambda_(y,b)| ||U_(x,a)†U_(y,b)||_1`.

The norm on the right is the trace/nuclear norm of a 2-by-2 matrix. Assume a positive measurable weight w satisfies

`integral k(x,y) w(y)dnu(y) <= C w(x)` almost everywhere.

Symmetry supplies the other weighted Schur condition. Taking w=1 gives the usual uniform row-integral condition. These are conditions on one-particle overlaps; the desired many-body noise bound is not assumed.

Finally require a reference inequality in **every finite-particle sector**,

`H0=L2(Q)`, `H0²>=gamma0 H0`, with `gamma0>0` independent of N.

For a theorem restricted to an input N, reference inequalities in sectors 0 through N suffice. A gap statement only at the target filling does not suffice for this proof.

## 2. Statement

For a positive one-particle contraction M, put

`E=(I-M²)^(1/2)`, `delta=||I-M²||`,
`B_x^M=B((wedge² M)p_x)`,
`H_M=integral (B_x^M)†B_x^M dnu=L2[(wedge² M)Q(wedge² M)]`.

Then, on every finite-particle sector,

`H_M² >= [gamma0-C delta-beta delta²] H_M`.                         (1)

Consequently a positive bracket is a lower bound on the entire positive spectrum, above the full kernel, uniformly in particle number and one-particle dimension. If M has a bounded inverse, then

`ker(H_M|N)=(wedge^N M^(-1))ker(H0|N)`.                           (2)

Invertibility is needed for (2), not for the noise inequality. None of the estimates uses the norm of `wedge^N M^(-1)`.

For normalized decomposable plane and sphere V1 frames one can take

`beta=1`, `C=8sqrt(3)<14`.

Thus the convenient single rational choice **C=14 is valid in both geometries**. The old C=20 and C=28 remain valid, weaker constants.

## 3. Exact fermionic loss-channel calculation

Use the environment-first identification `F(h_env direct-sum h_sys)=F(h_env) tensor F(h_sys)`. On this ordinary tensor product,

`d_env(v)=d(v) tensor I`, `c_sys(v)=(-1)^N_env tensor c(v)`.

This implements the graded anticommutation explicitly. Set

`b(v)=c_sys(Mv)+d_env(Ev)`.

The map `J:v -> (Ev,Mv)` is an isometry since `E²+M²=I`, so b satisfies the reference CAR. Its CAR representation is unitarily equivalent to the reference Fock representation on Jh tensored with spectator modes on `(Jh)^perp`. Compressing to the environment vacuum is a unital completely positive map Phi_M. Sectorwise boundedness and the full-sector input justify

`Phi_M(H0²)>=gamma0 Phi_M(H0)`.

Normal ordering gives `Phi_M(H0)=H_M`. The needed second-moment identity is more informative than Kadison's inequality. Let

`(A_M psi)(x)=B_x^M psi`, so `||A_M psi||²=<psi,H_M psi>`.

For an elementary p=u wedge v, acting H0(b) on an environment vacuum first annihilates two system particles. Expanding `b†(u)b†(v)` afterwards gives:

* environment number zero: `c†(Mu)c†(Mv)B_x^M psi`;
* environment number one: `[Eu tensor c†(Mv)-Ev tensor c†(Mu)]B_x^M psi`;
* environment number two: `(Eu wedge Ev) tensor B_x^M psi`.

The minus sign in the middle line follows from the environment parity in `c_sys†`. It is valid for complex vectors. For general p_x, multiply each creation expression by lambda_(x,a), whereas B_x^M contains its conjugate. This is the required conjugation pattern.

Define R_M as the synthesis operator with column

`R_M(x)=sum_a lambda_(x,a)[u_(x,a) tensor c†(Mv_(x,a))-v_(x,a) tensor c†(Mu_(x,a))]`.

Orthogonality of the environment particle sectors yields the exact formulas

`H0(b)(|0> tensor psi)=|0> tensor H_M psi+X1 psi+X2 psi`,
`X1=(E tensor I)R_M A_M`,
`X2=[(wedge²E)S tensor I]A_M`,
`Phi_M(H0²)=H_M²+X1†X1+X2†X2`.                                (3)

A system-first tensor convention changes the one-environment expression by a sector parity unitary; (3) is unchanged. No missing factor two arises in X2: `d†(Eu)d†(Ev)|0>=Eu wedge Ev` in the normalized exterior-product convention.

## 4. The two relative noise bounds

The second environment sector obeys

`||X2 psi||² <= ||wedge²E||² ||S||² ||A_M psi||²`
`              <= beta delta² <psi,H_M psi>`.                    (4)

Here `||wedge²E||<=||E||²=delta`. A general frame operator changes the coefficient from 1 to beta and requires no other change.

For the first sector, first prove a sharper elementary Gram bound. For any orthonormal two-frames U=[u,v] and V=[s,t], write

`R_U=u tensor c†(Mv)-v tensor c†(Mu)`.

Changing the basis of U by a 2-by-2 unitary A gives `R_(UA)=det(A)R_U`, by bilinearity. This identity uses only linearity of `c†(M .)`; M need not commute with the basis change. Independently change U and V so that `U†V` is diagonal with singular values sigma1,sigma2. The Gram expression then contains only

`sigma1 c(Mv)c†(Mt)+sigma2 c(Mu)c†(Ms)`.

Each product has norm at most 1 because `||c(a)||=||a||` on the full fermionic Fock space and M is a contraction. Basis changes only multiply the Gram operator by a phase. Therefore

`||R_U†R_V|| <= sigma1+sigma2 = ||U†V||_1`.                     (5)

For the finite decomposable sums, the triangle inequality gives `||R_M(x)†R_M(y)||<=k(x,y)`. The operator-valued Schur test, applied to `||F(x)||`, implies

`||R_M||²<=C`, `X1†X1<=C delta H_M`.                            (6)

For completeness, the weighted test follows by applying `2ab<=a²+b²` to `a=||F(x)||sqrt(w(y)/w(x))` and `b=||F(y)||sqrt(w(x)/w(y))`, then using symmetry and the assumed row bound. Thus it has no hidden Hilbert-space dimension or particle-number factor.

Combining (3)--(6) with positivity of Phi_M proves (1). Kadison alone has the reverse useful direction, `Phi_M(H0²)>=H_M²`, and does not prove (1).

To prove (2), for positive invertible M use

`B(p)(wedge^N M)=(wedge^(N-2)M)B((wedge²M)p)`.

The zero-energy condition is `B_x^M psi=0` for almost every x. Invertibility on each fixed sector gives exactly (2).

## 5. Infinite-dimensional definition and closure

The proof is first made on `direct-sum_(n=0)^N wedge^n h`, where every bounded two-particle form Q gives a bounded H0 with norm at most `beta binomial(N,2)`. The same bound holds in the doubled one-particle space because `J wedge J` is an isometry. The reference representation on Jh sees particle numbers 0 through N, which is the precise reason those reference sectors are required.

The analysis map A_M is bounded into `L²(X;F_(<=N-2))` by the bounded pair quadratic form. S tensor I is bounded with norm sqrt(beta); the Schur proof makes R_M bounded. These facts supply a rigorous meaning to all syntheses, even when individual columns are not globally integrable.

One may exhaust X by finite-measure sets on which the finite decomposable coefficients and vectors are bounded. The truncated positive frame operators converge strongly to Q and are bounded above by Q. Their lifts converge strongly on each fixed total-particle sector. The corresponding X1 and X2 converge by bounded synthesis applied to truncated A_M. This proves (3) without formal interchange of unbounded operators. Delta functions at frame labels are not claimed to be L² vectors or a dense core.

Finally take the self-adjoint direct sum over finite N. Inequality (1) is a sectorwise spectral statement and a quadratic-form inequality on D(H_M), the form domain of H_M². Its operator formulation holds on D(H_M²), and its positive spectral lower bound is uniform. No angular-momentum cutoff or thermodynamic continuity assertion is used.

## 6. Complete plane normalization and improved Schur constant

Let `u_alpha=D(alpha)|0>`, `v_alpha=D(alpha)|1>`, `p_alpha=u_alpha wedge v_alpha`, with `alpha=(R_x+iR_y)/(sqrt(2)ell)` and `dnu=2d²alpha/pi=d²R/(pi ell²)`.

The pair coefficient in `|i wedge j>`, i<j, is

`exp(-|alpha|²)(j-i)alpha^(i+j-1)/sqrt(i!j!)`.

Angular integration separates K=i+j. Radial integration gives the rank-one block vector

`q_K(i,K-i)=(K-2i)sqrt[(K-1)!/(2^(K-1)i!(K-i)!)]`, `i<K/2`.

For every integer K>=1, the full binomial sum satisfies

`sum_(i=0)^K (K-2i)² binomial(K,i)=K 2^K`,

by the first two binomial moments. Terms i and K-i are equal, and the middle term is zero when present. Therefore

`||q_K||²=[1/(K 2^(K-1))]*(K 2^(K-1))=1`.

This proves all K, not just finitely many tested values. In center/relative oscillator coordinates, p_alpha is relative angular momentum one tensored with the center coherent state of amplitude `sqrt(2)alpha`. The vectors q_K exhaust that sector. Hence `Q=P_rel,1` and beta=1.

For `t=|alpha-beta|²`, the two-frame overlap has

`||U_alpha†U_beta||_HS²=exp(-t)(t²+2)`,
`|det(U_alpha†U_beta)|=exp(-t)`.

The 2-by-2 identity `||A||_1²=||A||_HS²+2|det A|` gives the exact scalar majorant

`k(t)=exp(-t/2)sqrt(t²+4)`.

Consequently

`C_plane=2 integral_0^infinity exp(-t/2)sqrt(t²+4)dt`
`       <=2sqrt[(integral exp(-t/2)dt)(integral exp(-t/2)(t²+4)dt)]`
`       =2sqrt(2*24)=8sqrt(3)<14`.

Its floating diagnostic value is about 12.310898279; this number is not used as a certified bound. The old entrywise majorant gave `4sqrt(2pi)+16exp(-1/2)<20`, which was valid but wasteful.

## 7. Sphere normalization, including Q=1

For integer magnetic flux Q>=1, h is spin Q/2. Let u_g,v_g be common rotations of highest and next-highest weight states. The normalized wedge is the highest-weight coherent state of pair spin Q-1. Its irreducible space has dimension 2Q-1. Schur's lemma, or a trace calculation of the invariant Haar average, gives

`(2Q-1)integral |p_g><p_g|dg=P_pair-spin-(Q-1)`, `integral dg=1`.

Thus beta=1. Q=0 has no two-particle antisymmetric sector and is excluded as vacuous. For Q=1 the pair representation has spin zero and the same identity holds with dimension one.

With `s=sin²(theta/2)`, the normalized azimuth-integrated measure is ds. The two-frame overlap satisfies

`|det A|=(1-s)^(Q-1)`,
`||A||_HS²=(1-s)^(Q-2)[2-2s+(Q-1)²s²]`.

It follows that

`C_Q=(2Q-1)integral_0^1 (1-s)^((Q-2)/2)sqrt[4(1-s)+(Q-1)²s²]ds`.

The expression at Q=1,s=1 is interpreted by its continuous limit. In fact the overlap is a 2-by-2 unitary for Q=1, so its trace norm is constantly 2 and C_1=2. At Q=2 the kernel is 2-s and C_2=9/2.

For all Q>=1, weighted Cauchy--Schwarz with weight `(1-s)^((Q-2)/2)` gives

`C_Q <= [2(2Q-1)/Q] sqrt[(12Q²+8)/((Q+2)(Q+4))] <8sqrt(3)<14`.

Here the weight integral is 2/Q, its normalized first moment of 1-s is Q/(Q+2), and its second moment of s is `8/((Q+2)(Q+4))`. The final inequality follows from `2(2Q-1)/Q<4` and `12Q²+8<12(Q+2)(Q+4)`. Thus no flux dependence is hidden in C.

For the physical isotropic contact on a sphere of radius R, pair-projector normalization requires the coefficient

`c_Q=8pi R^4(2Q-1)/[Q(Q+1)²]`

in front of `integral dA sum_(j=1,2)(Psi nabla_j Psi)†(Psi nabla_j Psi)`, where j labels orthonormal tangent directions. Indeed at the north pole, normalized monopole orbitals in `zeta=(X+iY)/(2R)` are `phi_n=sqrt[(Q+1)binomial(Q,n)/(4pi R²)]zeta^n/(1+|zeta|²)^(Q/2)`. The squared sum of the two pair amplitudes is `Q(Q+1)²/(32pi²R^6)`, so multiplication by c_Q yields `(2Q-1)/(4pi R²)` as required by the coherent frame. Connection terms multiply the field square and vanish. For `ell²=2R²/Q`, the ratio `c_Q/(4pi ell^4)=Q(2Q-1)/[2(Q+1)²]` tends to 1. The finite-Q coefficient should not simply be replaced by its plane limit.

## 8. Operational extensions beyond one decomposable contact channel

**Nonprojection frame operators.** Only `||Q||<=beta` is used in (4). For a positive weight a with `a_-<=a(x)<=a_+`, the new columns `sqrt(a(x))p_x` have `beta_new<=a_+ beta` and `C_new<=a_+ C`. If Q was the original frame, two-sided positive comparison gives the weighted reference model the same kernel and a full-Fock gap at least a_- gamma0. A separate filter then satisfies (1) with these explicit constants.

**Nonorthogonal elementary pairs.** A wedge of nonorthogonal vectors can be normalized by Gram--Schmidt and its norm placed into lambda. It is often better to avoid division by a small wedge norm: directly expand R for raw a_x,b_x and use bounds such as `|<a_x,a_y>| ||b_x||||b_y||` for its four Gram terms. Uniform raw-vector norm bounds and localized raw overlaps suffice. Orthogonality of the original spanning vectors is not essential.

**Several contact channels.** Replace X by the disjoint union of channel label spaces, and apply exactly the stated theorem to all columns. Cross-channel overlaps must be included. If each channel block has both row and column Schur bounds C_ab=C_ba, the norm of the finite symmetric nonnegative matrix (C_ab) bounds C. A crude row-sum bound exposes any channel-count factor. Positive local channel matrices can be factored first and their columns treated in this way; an unbounded number of equally strong channels is not automatically dimension independent.

**Finite Slater rank.** The stated kernel k already proves this case. For uniform `sum_a |lambda_(x,a)|<=L` and component overlaps bounded by `A(1+r)^s exp(-a r²)`, the entrywise estimate `||U†V||_1<=sum_ij |(U†V)_ij|` gives a scalar majorant `4AL²(1+r)^s exp(-a r²)`. A two-dimensional measure density at most rho yields

`C<=8pi rho A L² integral_0^infinity r(1+r)^s exp(-a r²)dr`.

This is finite and independent of total area. A finite near-region interval bound may replace the near part; the remaining integral is a rigorous tail bound. Merely sampling a finite matrix or truncating overlap tails supplies no such certificate.

**A completely checked nondecomposable family.** Let h be any number of disjoint four-mode cells and

`p_j=(e_(j,1) wedge e_(j,2)+e_(j,3) wedge e_(j,4))/sqrt(2)`.

The p_j are orthonormal, have Slater rank two, and beta=1. All cross-cell one-particle overlaps vanish; within a cell the kernel k is 2, so C=2. For `B_j=(c_(j,2)c_(j,1)+c_(j,4)c_(j,3))/sqrt(2)`, the cell Hamiltonian B_j†B_j is zero in sectors 0 and 1, has eigenvalues 0 and 1 in sector 2, is `(1/2)I` in sector 3, and equals 1 in sector 4. Even cell Hamiltonians commute on disjoint modes. Hence gamma0=1/2 uniformly in the number of cells and

`gap(H_M)>=1/2-2delta-delta²` whenever positive.

Weights `a_-<=a_j<=a_+` give the nonprojection variant `gamma0=a_-/2`, `beta=a_+`, `C=2a_+`. The exact local polynomial `H(H-I/2)(H-I)=0` is independently checked with rational matrices in analytic_extension_checks.jl. This validates the abstract extension on a concrete infinite-size family; it is expressly not a new Laughlin/FCI model.

**A same-LLL finite-rank frame, with an unresolved reference gap.** Let

`p_alpha=(D(alpha)|0> wedge D(alpha)|1>+D(alpha)|2> wedge D(alpha)|3>)/sqrt(2)`.

The center/relative oscillator expansion is

`|2 wedge 3>=sqrt(1/8)|4_CM,1_rel>-(1/2)|2_CM,3_rel>+sqrt(5/8)|0_CM,5_rel>`.

Weyl averaging over `2d²alpha/pi` gives `Q=I_CM tensor K`, where K on relative indices 1,3,5 is

`K=[[9/16,0,sqrt(10)/8],[0,1/8,0],[sqrt(10)/8,0,5/16]]`.

Its largest eigenvalue is `(7+2sqrt(11))/16<1`. All component overlaps are Gaussian times Laguerre polynomials. Replacing their coefficients by absolute values, factorial square-root ratios by 1, and odd half-powers by AM--GM yields the explicit rational C<=336, checked by exact integral sums in the script. Thus this is a concrete nonprojection, Slater-rank-two frame with operational bounds. Its full-Fock reference gap is not established here; the transfer theorem for it remains conditional on that additional input. Positivity relative to V1 alone would not close this gap because the kernels differ.

## 9. Physical scalar pullback and coercivity instead of a pointwise bound

For a bounded smooth scalar f, possibly complex or zero at some points, let `G=P0|f|²P0` and suppose `g_-I<=G<=g_+I` with g_->0. Then multiplication by f has closed range on h0 and `U=fG^(-1/2)` is unitary from h0 to that range. The ordinary positive derivative contact on the projected field gives, by `chi(r)²=0`,

`(f chi)partial_j(f chi)=f² chi partial_j chi`.

Thus its pullback is the weighted pair form with `w=|f|⁴`; no inverse interaction weight has been inserted. In plane pair-projector units the physical contact is `4pi ell^4 integral sum_(j=x,y)(Psi partial_j Psi)†(Psi partial_j Psi)d²r`.

**Maximal multiplication domain on the plane, including nodal f.** The domain issue for the unbounded vortex coordinate z can also be closed. Let `D(z)={psi in L²: z psi in L²}`. The LLL projection has kernel modulus `(2pi ell²)^(-1)exp(-|z-w|²/(4ell²))`. Therefore the kernel `(z-w)P0(z,w)` obeys the Schur bound `2sqrt(pi)ell`, proving that `[z,P0]` is bounded and P0 preserves D(z). On `D0=h0 intersect D(z)`, z leaves h0 invariant and

`[z,G]=[z,P0]|f|²|h0`

is bounded; only boundedness of the scalar f is used here. Choose c>=g_+, set `T=I-G/c`, and write `r=||T||<1`. For phi in D0,

`||z T^n phi||<=r^n||z phi||+n r^(n-1)||[z,T]||||phi||`.

The Neumann series `G^(-1)=c^(-1)sum_(n>=0)T^n` consequently converges in the graph norm of z on D0. Thus G^(-1) preserves D0. If `psi=f phi` belongs to `h_f intersect D(z)`, then `P0 conjugate(f) psi=G phi` lies in D0, and applying G^(-1) proves phi belongs to D0. The reverse inclusion is immediate because f is bounded. Hence

`h_f intersect D(z)=f D0`, `z(f phi)=f(z phi) in h_f`.

This proves `(1-P_f)z psi=0` on the entire maximal multiplication domain inside h_f, rather than just on a chosen dense core. It needs no inverse multiplication by f and remains valid at nodal lines. The argument is specifically for the plane LLL projection; it is not an unexamined assertion about global stereographic multiplication on a fixed-flux sphere.

Define `Q_w=integral w(x)|p_x><p_x|dnu`. If directly verifiable two-body inequalities

`kappa Q<=Q_w<=KQ`, `kappa>0`, `K<infinity`

hold, set `M=sqrt(g_-)G^(-1/2)` and `delta=1-g_-/g_+`. Then

`(kappa/g_-²)H_M<=H_f<=(K/g_-²)H_M`,
`gap(H_f)>=(kappa/g_-²)[gamma0-Cdelta-beta delta²]`.             (7)

Two-sided comparison proves equality of kernels; one never squares the positive-operator comparison. The physical kernel is `(product_i f(r_i))ker(H0|N)`. The old pointwise assumption `|f|²>=m>0` is the special case kappa=m². Zeros of f are compatible with (7).

On the plane, the pair center coherent coordinate is `(R_x+iR_y)/ell`. For an absolutely summable Fourier series of w,

`Q_w|Ran Q=sum_q w_q exp(-|q|²ell²/8) W_CM(q)`,

where W_CM(q) is unitary. Hence the explicit sufficient coercivity bound is

`kappa=w_0-sum_(q!=0)|w_q|exp(-|q|²ell²/8)>0`.

The analogous single-particle Gram attenuation is `exp(-|q|²ell²/4)`. For the smooth nodal example `f=2cos(kx)cos(ky)`, `k=sqrt(2pi)/ell`, let `r=e^(-2pi)<1/500` and `t=e^(-pi)<1/23`. One obtains

`||G-I||<=2r+r²<=1001/250000`,
`kappa>=9/2-[3/2+2/23+1/(2*23^4)]²>0`.

The first bound comes from `|f|²=(1+cos(2kx))(1+cos(2ky))`; the second comes from `|f|⁴=(3/2+2cos(2kx)+(1/2)cos(4kx))` times the same y factor. These are finite Fourier sums with no tail. Using gamma0=1/5 where the audited reference theorem applies and C=14 yields a strict lower bound greater than 0.176 in pair-projector units. The exact rational value and external-input scope are recorded in EXAMPLES_AND_BOUNDS.md and the literature audit. This is a true enlargement beyond a positive pointwise multiplier; it does not supply a finite-torus reference theorem.

## 10. Dependency boundary

CAR, the dilation identity, and (4) use no LLL geometry. The one-environment estimate needs localized pair structure and Schur integrability. The external gap needs every loss-accessible particle sector. LLL/coherent-state geometry supplies normalized frames and explicit overlap constants, while bounded Gram geometry supplies a usable M. The physical derivative-contact calculation and any coordinate/orbital interpretation are additional independent steps. Neither vortexability alone, Chern number alone, nor existence of zero modes supplies these quantitative inputs.
