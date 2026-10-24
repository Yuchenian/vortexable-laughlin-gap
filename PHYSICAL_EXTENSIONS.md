> **Review status updated 2026-10-24.** The author reports personally checking the main conclusions and calculations. See [HUMAN_REVIEW.md](HUMAN_REVIEW.md) and the [follow-up audit](RECHECK_20261024.md).

# Physical projection, zeros, orbital embeddings, and vortex coordinates

Research audit, 2026-10-16. These are deductions made in this audit, not claims that an external Laughlin gap theorem has been verified. Every use of a reference gap below means the explicit input `H0^2 >= gamma0 H0` in every finite-particle sector of the stated geometry. No finite-torus input is inferred from a plane input.

## 1. Fixing the actual interaction and its units

On the plane take `phi_n(z)=(2 pi ell^2 n!)^(-1/2) (z/(sqrt(2)ell))^n exp(-|z|^2/(4ell^2))` and an orthonormal projected field `Psi`. The physical, positive derivative-contact quadratic form used throughout is

`H_contact = 4 pi ell^4 integral d^2r sum_(j=x,y) [Psi(r) partial_j Psi(r)]^* [Psi(r) partial_j Psi(r)]`.

It is the fermionic V1 interaction after LLL projection, with coefficient one for each unordered pair projector. To check the coefficient, at the origin `Psi partial_x Psi = -(2 sqrt(2) pi ell^3)^(-1) c_1 c_0` and `Psi partial_y Psi=i Psi partial_x Psi`; translating by a magnetic displacement gives the normalized pair `p_R=D(alpha)|0> wedge D(alpha)|1>`, `alpha=(R_x+i R_y)/(sqrt(2)ell)`. Thus the displayed form equals `integral B(p_R)^*B(p_R) d^2R/(pi ell^2)`. Gauge-potential terms do not change it since they multiply `Psi^2=0`. The form, rather than an unregularized product of distributions, specifies the interaction on the projected space.

For a smooth bounded scalar multiplier f, which may be complex or have zeros, let `G=P0 |f|^2 P0`, and require `0<g_- I<=G<=g_+ I`. Multiplication by f is then bounded below **on h0**, has closed range, and `U=fG^(-1/2)` is a unitary map from h0 onto that range. No bounded inverse multiplication on ambient L2 is required.

Writing `chi(r)=sum_n [G^(-1/2)phi_n](r)c_n` with the equivalent consistent basis convention, the physical field is `Psi=f chi`. Pointwise CAR gives

`Psi partial_j Psi=f^2 chi partial_j chi + f(partial_j f)chi^2=f^2 chi partial_j chi`.

Consequently the pullback is exactly

`H_f=integral |f(R)|^4 B_R(G^(-1/2))^* B_R(G^(-1/2)) dnu(R)`.

This comes from a fixed derivative-contact interaction. Its coefficient was not chosen to cancel f. On each finite N sector boundedness follows whenever the weighted two-body frame below is bounded. Evaluation and derivative fields in the LLL are bounded fermionic operators at fixed r; integration is defined by the resulting positive two-body form.

**Sphere coefficient in the same projector units.** On a sphere of radius R with Q>=1 flux quanta, use an orthonormal tangential frame and covariant derivatives. The physical normalized contact form is

`H_Q=c_Q integral_(S²) dA sum_(j=1,2) [Psi nabla_j Psi]^*[Psi nabla_j Psi]`,
`c_Q=8pi R^4(2Q-1)/[Q(Q+1)^2]`.

Indeed at the north pole in local coordinate `zeta=(X+iY)/(2R)`, normalized sections have `phi_0=sqrt((Q+1)/(4pi R²))` and `partial_X phi_1=phi_0 sqrt(Q)/(2R)`; the Y derivative is i times it. The squared pair amplitude summed over the two tangents is `Q(Q+1)²/(32pi²R^6) B^*B`. Multiplication by c_Q gives precisely `(2Q-1)/(4pi R²) B^*B`, the coherent pair measure per unit area. Rotation gives the identity globally; gauge-connection terms vanish by the same field-square identity. The same f pullback therefore gives |f|^4 with this fixed coefficient. With `ell²=2R²/Q`, `c_Q/(4pi ell^4)=Q(2Q-1)/(2(Q+1)²)->1`; using the planar coefficient unchanged at finite Q would be a normalization error. This spherical contact statement uses sections of the magnetic line bundle and does not posit a globally defined stereographic multiplication preserving fixed flux.

## 2. Replacing a pointwise lower bound by pair-frame coercivity

Let `Q=integral |p_x><p_x|dnu`, and `Q_w=integral w(x)|p_x><p_x|dnu`, where `w=|f|^4`. The sufficient, directly two-body condition is

`kappa Q <= Q_w <= K Q`, with `0<kappa<=K<infinity`.

For `M=sqrt(g_-)G^(-1/2)` and `delta=1-g_-/g_+`, second quantization of two-body positive forms gives

`(kappa/g_-^2) H_M <= H_f <= (K/g_-^2) H_M`.

The two kernels agree and therefore the audited loss-channel theorem, when its frame hypotheses hold, yields

`gap(H_f) >= (kappa/g_-^2)[gamma0-C delta-beta delta^2]`.

Here `beta=||Q||`. This is an operational extension, not an assumption of the desired many-body noise bound. A Fourier criterion establishing kappa for a concrete family follows. Also, it is unnecessary to use a condition number for `wedge^N G`: the only many-body comparison is a positive two-body form inequality with common kernel.

For each finite N the zero space is exactly `(product_i f(r_i)) ker(H0|N)`. This follows by the invertible map `wedge^N M` in the pair-annihilator equations plus the two-sided comparison. The inverse is used for algebraic identification of a subspace, not for a uniform norm estimate.

**Unbounded vortex-coordinate domain.** The multiplication operator z on ambient L2 has domain `{psi:z psi in L2}`. In the standard planar LLL, P0 preserves this domain and `[z,P0]` extends boundedly (the Landau oscillator formula has only a lowest-to-first cyclotron off-diagonal block). Bounded multiplication by f and its conjugate commutes with z and preserves this domain. Thus G preserves `D(z|h0)` and `[z,G]` is bounded there. For `g_->0`, the convergent Neumann series for G^(-1), rescaled by g_+, has commutator terms bounded by a summable geometric series times n; hence G^(-1) also preserves that domain and has bounded commutator. Consequently `P_f=f P0 G^(-1) P0 conjugate(f)` preserves ambient D(z) and `[z,P_f]` is bounded. On the dense subspace `f D(z|h0)`, `(1-P_f)z` vanishes because `z f phi=f z phi`. Boundedness of `(1-P_f)[z,P_f]P_f` extends the zero identity to all `Ran(P_f) intersect D(z)`. This verifies maximal-domain vortexability, including the nodal example, rather than relying only on a formal wavefunction identity.

## 3. A computable family with genuine zeros

In the planar V1 frame the relative factor is fixed to relative angular momentum one, and the center-of-mass factor is a coherent state of magnetic length `ell/sqrt(2)`. Hence, for absolutely summable Fourier coefficients `w_q`,

`Q_w |Ran Q = sum_q w_q exp(-|q|^2 ell^2/8) exp(i q.R_CM)`.

The last factor is unitary, with the convention `[R_CM,x,R_CM,y]=-i ell^2/2`. The coherent-state resolution gives this identity; equivalently, its vacuum matrix element is the Gaussian integral `exp(-|q|^2 ell^2/4)`, the product of the displayed prefactor and the Weyl vacuum expectation. It follows rigorously that

`kappa = w_0 - sum_(q != 0) |w_q| exp(-|q|^2 ell^2/8)`

is a lower bound whenever positive. The same sum with a plus gives K. Similarly `G=P0 |f|^2P0` has attenuation `exp(-|q|^2ell^2/4)`. Fourier sums here are finite; there is no omitted tail or numerical quadrature.

Take `a=sqrt(2 pi)ell`, `k=2 pi/a=sqrt(2 pi)/ell`, and

`f(x,y)=2 cos(kx) cos(ky)`.

This is a smooth real multiplier with nodal lines. It is not in the old class of strictly positive multipliers. Its minimal positive period lattice has cell area `a^2/2`, while the square magnetic cell of side a has one flux quantum and gives the useful rank-one magnetic Bloch description. Translations by a/2 in a coordinate multiply f by -1; they preserve the subspace but do not supply a commuting one-flux pair. We use the one-flux square cell, without claiming a single ordinary band on a smaller half-flux cell.

With `q=2k`,

`|f|^2=(1+cos(qx))(1+cos(qy))`,
`|f|^4=(3/2+2cos(qx)+(1/2)cos(2qx))(3/2+2cos(qy)+(1/2)cos(2qy))`.

Set `r=exp(-2pi)<1/500`, `t=exp(-pi)<1/23`. Then

`||G-I|| <= 2r+r^2 <= alpha=1001/250000`,
`Q_w >= kappa Q`,
`kappa = 9/2-[3/2+2/23+1/(2*23^4)]^2 > 0`.

Indeed the total absolute weighted Fourier mass is `[3/2+2t+t^4/2]^2` and its constant part is 9/4. Set `g_-=1-alpha`, `g_+=1+alpha`, `delta=2alpha/(1+alpha)`. With the conditional input `gamma0=1/5`, `C=20`, `beta=1`, the resulting lower bound is strictly greater than 0.08 in the same pair-projector units. Exact rational verification is in `extension_bound_checks.jl` and its archived output. The proof of `exp(pi)>23` uses `pi>157/50` and a finite rational Taylor sum; no floating-point certificate is used.

The revised nuclear-overlap estimate in `ANALYTIC_AUDIT.md` permits C=14, improving this bound to `5992934159531101049706250000000/33988053096870625665692548678809 = 0.1763247262928069...` for gamma0=1/5.

The nodes are not repaired or removed: `G` remains invertible despite them, and pair-frame coercivity supplies the missing contact-energy lower bound. This is a complete conditional plane example, uniform in finite N, with the entire Laughlin/quasihole kernel multiplied by f. It proves neither a finite-torus gap nor a topological-order classification. The scalar being sign-changing is harmless for the physical derivative-contact form, and |f| need not be used in place of the smooth f.

## 4. Rank-one multi-orbital embeddings: what is and is not new

Let `t(r):C -> C^s` be a smooth column vector, and `h_t={t(r)phi(r):phi in h0}` with `G=P0 t^*t P0` uniformly invertible. Input fiber rank and magnetic Bloch rank are one; output orbital fiber rank is s. The fermions occupy the single embedded band, not s independent copies.

Use the physical orbital-symmetric interaction

`4 pi ell^4 integral sum_(a,b=1..s) sum_(j=x,y) [Psi_a partial_j Psi_b]^*[Psi_a partial_j Psi_b] d^2r`.

Since `Psi_a=t_a chi`, every derivative of t multiplies `chi^2=0`, and each channel reduces to `t_a t_b chi partial_j chi`. Summing gives precisely `w=(t^*t)^2` and the same G and coercivity criterion as above. Also every projected s-wave contact `Psi_a Psi_b` vanishes identically.

Where `t=f n`, `n^*n=1`, the model is exactly related by a position-dependent orbital isometry to the scalar f model for this interaction. Smooth textures n may alter the presentation of the band projector and its quantum geometry, but this calculation does **not** establish a new generic multiorbital FCI theorem. A simple concrete example is the nodal f above times `n=(cos theta, exp(i kx) sin theta)`, with fixed theta. Its gap bound and zero modes are exactly those of the scalar example. It is labelled an isometric extension, not independent evidence of wider phase stability.

For a fixed positive orbital-channel matrix K one instead obtains the local weight `(t tensor t)^* K (t tensor t)`; Fourier/coercivity bounds can still be used when verified. A semidefinite K can lose all interaction on some embeddings, so t^*t alone cannot guarantee a gap.

For input fiber rank greater than one, `Psi_a=sum_mu T_(a mu)chi_mu`, the term `sum_(mu,nu) T_(a mu)(partial_j T_(b nu))chi_mu chi_nu` need not vanish. For example `T=diag(1,exp(i kx))` produces `i k exp(i kx)chi_1 chi_2` in `Psi_1 partial_x Psi_2`. The scalar proof fails at this explicit step. Such systems need separately specified contact channels, filling, zero modes, and target order; they do not inherit fermionic one-component 1/3-Laughlin conclusions.

## 5. Nonstandard vortex coordinate with the Jacobian retained

Let `F:R^2 -> R^2` be an orientation-preserving smooth global diffeomorphism, `J=det DF>0`, and define the L2 unitary

`(U_F phi)(r)=sqrt(J(r)) phi(F(r))`.

The transformed subspace is vortexable with coordinate `zeta(r)=F_x(r)+iF_y(r)`: on the maximal multiplication domain, `U_F^* zeta U_F = z`. The invariant domain is `U_F D(z|h0)`. A global assertion about `(1-P)zeta P` is understood on this domain, never as an everywhere-defined bounded operator.

Keep the ordinary isotropic derivative contact in the physical r coordinates. If `chi` is the reference projected field, then

`Psi partial_(r_i) Psi = J sum_j (partial_(r_i) F_j) chi partial_(R_j) chi`.

The derivative of sqrt(J) disappears by CAR. In the LLL, `chi partial_Y chi=i chi partial_X chi`. Changing integration measure to `d^2R=J d^2r` gives the exact pulled-back pair weight

`w_F(R)=[J(r) ||DF(r)||_F^2/2]_(r=F^(-1)(R))`.

The factor J cannot be omitted. If `0<w_-<=w_F<=w_+<infinity`, the same kernel and positive comparison give `gap>=w_- gamma0`, directly, without the loss channel. This is a geometric equivalence plus a physical weighted-contact comparison, not a general theorem about arbitrary nonlinear coordinates.

A concrete arbitrarily strong example is the area-preserving periodic shear

`F(x,y)=(x+(a_s/k)sin(ky),y)`, with finite real shear amplitude `a_s`.

Here `J=1`, `w_F=1+(a_s^2/2)cos^2(ky)>=1`. Therefore the ordinary physical derivative contact on `U_F h0` has gap at least gamma0 and exactly the pulled-back Laughlin/quasihole zero space. The lower bound is uniform in N and a_s; derivatives and the upper bound are finite for each chosen a_s. The deformation is not small. This is outside scalar-multiplied standard LLL: the ratio of the transformed first two orbitals is proportional to `zeta`, which is not meromorphic in z when `a_s !=0`; in any scalar-multiplied LLL, ratios of nonzero orbitals are meromorphic. At generic points `partial_bar zeta !=0`, giving a local obstruction.

If `k=2pi/a` with one-flux square period a, F is equivariant under the period lattice and preserves area. The magnetic translation representation is carried through U_F, retaining rank one per magnetic cell and C=1. To express it in a fixed Landau gauge, note that `F^*(B X dY)=B x dy + d[-B a_s cos(ky)/k^2]`; a periodic gauge phase removes the exact term. Such a phase does not alter the contact form, again because derivative-of-phase terms multiply the field square. The reference filling is one electron per three flux quanta. These identifications concern the plane band and zero modes; a finite torus requires its own reference gap and compatible magnetic bundle construction.

## 6. Limits and counterexamples to overbroad inferences

* Uniform Gram invertibility is a sufficient condition, not a consequence of vortexability. `f(r)=exp(-s|r|^2/(4ell^2))`, s>0, maps the standard LLL to a narrower Gaussian LLL and is z-vortexable, yet in the angular basis `G_nn=(1+s)^(-(n+1)) ->0`. It has no uniform g_-. In fact this example is another uniformly magnetic LLL with a rescaled length and can be treated geometrically; failure of this particular representation's Gram bound is not proof of gaplessness.
* Vortexability alone does not fix an interaction energy scale. Uniform rescalings of space change the contact coefficient; a class allowing arbitrary such rescalings has no common positive bound in fixed physical units.
* A fixed-N reference inequality is insufficient for this loss-channel proof: the dilation sees all reference sectors up to N. Positivity cannot be invoked on unverified sectors.
* Small steps along a path spend the available reference gap. With step losses eta_j and comparison factors lambda_j, `gamma_(j+1)>=lambda_j(gamma_j-eta_j)`; each next step also needs its own valid frame/noise certificate. No unlimited path certification follows merely from making each step small.
* Rank-one orbital embeddings, smooth coordinate pullbacks, and the scalar/Gram class do not constitute a representation theorem for all C=1 vortexable bands. Global coordinate invertibility, bundle compatibility, bounded multiplication/Gram, and pair-frame estimates are additional inputs.

