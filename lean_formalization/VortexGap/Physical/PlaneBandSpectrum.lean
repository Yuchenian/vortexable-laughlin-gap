import VortexGap.Physical.PlaneBandCriterion
import VortexGap.Physical.KernelSpectrum
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped ComplexOrder BoundedContinuousFunction

/-- Physical scalar criterion in orthonormal coordinates of the actual closed
multiplied LLL range. The Hamiltonian represents the independently defined
band-field derivative contact. Gram invertibility is derived from g>0 and the
Gram lower bound. The only spectral input is the ORIGINAL reference sectors
0,...,N; no dilation/noise/enlarged-sector gap is assumed. The projected lower
coercivity permits nodal f. If the displayed lower bound is positive, this gives
a gap above the entire kernel, including possible continuous spectrum. -/
theorem physical_scalar_criterion (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hf : Differentiable ℝ f) (g u κ γ : ℝ) (hg : 0 < g) (hgu : g ≤ u) (hκ : 0 < κ)
    (hlo : g • (1 : CountableOrbital →L[ℂ] CountableOrbital) ≤ planeScalarGram ell hell f)
    (hhi : planeScalarGram ell hell f ≤ u • (1 : CountableOrbital →L[ℂ] CountableOrbital))
    (hw : (κ : ℂ) • planePairOperator ≤ planeWeightedPairOperator ell f)
    (N : ℕ) (hgap : ∀ k ≤ N,
      (countablePairLift k planePairOperator * countablePairLift k planePairOperator -
        (γ : ℂ) • countablePairLift k planePairOperator).IsPositive) :
    let hG : IsStrictlyPositive (planeScalarGram ell hell f) :=
      gramOperator_strict (planeScalarEmbedding ell hell f) g hg hlo
    ∀ t ∈ spectrum ℝ (planeBandContactOperator ell hell f hG hf N),
      t = 0 ∨ κ/g^2*(γ-14*(1-g/u)-(1-g/u)^2) ≤ t := by
  dsimp only
  have hG : IsStrictlyPositive (planeScalarGram ell hell f) :=
    gramOperator_strict (planeScalarEmbedding ell hell f) g hg hlo
  have hk := planeBandContact_kernel_gap ell hell f hG hf g u κ γ hg hgu hκ hlo hhi hw N hgap
  exact kernel_complement_gap_spectrum _
    (ContinuousLinearMap.nonneg_iff_isPositive.mpr (planeBandContactOperator_positive ell hell f hG hf N))
    _ hk.2

end VortexGap.Fermion
