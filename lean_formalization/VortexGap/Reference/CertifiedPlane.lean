import VortexGap.Reference.PhysicalBridge
import OAI.Analysis.Laughlin.Planar.Forms
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion

/-- The pinned reference endpoint implies the weaker rational bound in the
normalization of the upstream finite-degree Hamiltonian. -/
theorem upstream_plane_old_bound (L : ℕ) (z : OAI.Laughlin.Fock.Space L)
    (hz : OAI.Laughlin.Fock.DegreeAtMost L L z) :
    (1/25 : ℝ) * OAI.Laughlin.Planar.pairEnergy L (OAI.Laughlin.Planar.planarPairMatrix L)
      ((OAI.Laughlin.Fock.occupationBasis L).repr z) ≤
    OAI.Laughlin.Planar.squareNorm L (OAI.Laughlin.Planar.planarHamiltonian L)
      ((OAI.Laughlin.Fock.occupationBasis L).repr z) := by
  refine le_trans (mul_le_mul_of_nonneg_right OAI.Laughlin.one_twenty_fifth_lt_gammaStar.le ?_)
    (OAI.Laughlin.Planar.finite_degree_endpoint L z hz)
  unfold OAI.Laughlin.Planar.pairEnergy
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem countablePlane_old_bound (N : ℕ) :
    (countablePairLift N planePairOperator * countablePairLift N planePairOperator -
      (1/25 : ℂ) • countablePairLift N planePairOperator).IsPositive := by
  simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
    countablePlane_gap_of_upstream_finite (1/25) upstream_plane_old_bound N

/-- A changed planar band with a positive lower bound above its entire kernel. -/
theorem planeWeakCos_certified_gap (ell : ℝ) (hell : 0 < ell) (N : ℕ) :
    (planeScalarEmbedding ell hell planeWeakCos).toLinearMap.range ≠
        (planeLLLEmbedding ell hell).toLinearMap.range ∧
      ∀ t ∈ spectrum ℝ (planeWeakCosContactOperator ell hell N),
        t = 0 ∨ (3/100 : ℝ) ≤ t :=
  planeWeakCos_physical_of_upstream_finite upstream_plane_old_bound ell hell N

end VortexGap.Fermion

