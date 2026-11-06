import VortexGap.Reference.ReferenceLimit
import VortexGap.Examples.PlaneBandDistinct
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
/-- Assembly of the actual changed-band geometry and physical spectral conclusion.
The pinned upstream finite-degree inequality remains an explicit premise here. -/
theorem planeWeakCos_physical_of_upstream_finite
    (href : ∀ (L : ℕ) (z : OAI.Laughlin.Fock.Space L),
      OAI.Laughlin.Fock.DegreeAtMost L L z →
      (1/25 : ℝ) * OAI.Laughlin.Planar.pairEnergy L (OAI.Laughlin.Planar.planarPairMatrix L)
        ((OAI.Laughlin.Fock.occupationBasis L).repr z) ≤
      OAI.Laughlin.Planar.squareNorm L (OAI.Laughlin.Planar.planarHamiltonian L)
        ((OAI.Laughlin.Fock.occupationBasis L).repr z))
    (ell : ℝ) (hell : 0 < ell) (N : ℕ) :
    (planeScalarEmbedding ell hell planeWeakCos).toLinearMap.range ≠
        (planeLLLEmbedding ell hell).toLinearMap.range ∧
      ∀ t ∈ spectrum ℝ (planeWeakCosContactOperator ell hell N),
        t = 0 ∨ (3/100 : ℝ) ≤ t := by
  refine ⟨planeWeakCos_range_ne ell hell, planeWeakCos_conditional_gap ell hell N ?_⟩
  intro k _hk
  simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
    countablePlane_gap_of_upstream_finite (1/25) href k
end VortexGap.Fermion
