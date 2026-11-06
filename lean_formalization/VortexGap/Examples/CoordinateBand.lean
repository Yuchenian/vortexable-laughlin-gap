import VortexGap.Physical.CoordinateContact
import VortexGap.Geometry.CoordinateChange
import VortexGap.Reference.CertifiedPlane

noncomputable section

namespace VortexGap.Fermion
open MeasureTheory

def coordinateBandEmbedding (F : ℂ ≃ₜ ℂ) (hf : ContDiff ℝ 2 F) (hJ : ∀ z, 0 < coordinateJacobian F z)
    (ell : ℝ) (hell : 0 < ell) :=
  (coordinateUnitary F hf hJ).toLinearIsometry.comp (planeLLLEmbedding ell hell)

theorem coordinateBandEmbedding_coe (F : ℂ ≃ₜ ℂ) (hf : ContDiff ℝ 2 F)
    (hJ : ∀ z, 0 < coordinateJacobian F z) (ell : ℝ) (hell : 0 < ell) (v : CountableOrbital) :
    (coordinateBandEmbedding F hf hJ ell hell v : ℂ → ℂ) =ᵐ[volume] fun z =>
      ((Real.sqrt (coordinateJacobian F z) : ℝ) : ℂ) * inner ℂ (planeEvaluation ell (F z)) v := by
  have he := (coordinate_ae_iff F hf hJ _).mpr (planeLLLEmbedding_coe ell hell v)
  filter_upwards [coordinateUnitary_apply F hf hJ (planeLLLEmbedding ell hell v), he] with z hz hw
  exact hz.trans (congrArg (((Real.sqrt (coordinateJacobian F z) : ℝ) : ℂ) * ·) hw)

/-- A dilation checks both the two-field normalization and the nontrivial area factor. -/
def doubleCoordinate : ℂ ≃ₜ ℂ where
  toFun z := z+z
  invFun z := z/2
  left_inv z := by ring
  right_inv z := by ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem doubleCoordinate_smooth : ContDiff ℝ 2 doubleCoordinate := by
  change ContDiff ℝ 2 (fun z : ℂ => z+z); fun_prop

private theorem doubleDerivative (z c : ℂ) : fderiv ℝ (⇑doubleCoordinate) z c = c+c := by
  change fderiv ℝ (fun w : ℂ => w+w) z c = _
  change fderiv ℝ (id + id : ℂ → ℂ) z c = c+c
  rw [((hasFDerivAt_id (𝕜 := ℝ) z).add (hasFDerivAt_id z)).fderiv]
  rfl

theorem doubleCoordinate_jacobian (z : ℂ) : coordinateJacobian doubleCoordinate z = 4 := by
  rw [coordinateJacobian_axes, doubleDerivative,doubleDerivative]
  norm_num

theorem doubleCoordinate_weight (z : ℂ) : coordinateMetricWeight doubleCoordinate z = 16 := by
  dsimp only [coordinateMetricWeight]
  rw [doubleCoordinate_jacobian,doubleDerivative,doubleDerivative,Complex.sq_norm,Complex.sq_norm]
  norm_num [Complex.normSq_apply]

theorem doubleCoordinate_energy (ell : ℝ) (hell : 0 < ell) (N : ℕ) (x : countableSector N) :
    (∫ z, coordinateDensity doubleCoordinate ell z N x) =
      16 * (inner ℂ x (countablePairLift N planePairOperator x)).re := by
  rw [coordinateEnergy_reference doubleCoordinate doubleCoordinate_smooth (by simp [doubleCoordinate_jacobian]) ell hell]
  simp_rw [doubleCoordinate_weight]
  rw [integral_const_mul]
  congr 1
  simpa [planeScalarContactEnergy] using planeScalarContactEnergy_constant ell hell 1 N x

theorem doubleCoordinate_physical_old_gap (ell : ℝ) (hell : 0 < ell) (N : ℕ) :
    ∃ A : countableSector N →L[ℂ] countableSector N, A.IsPositive ∧
      (∀ x, (inner ℂ x (A x)).re = ∫ z, coordinateDensity doubleCoordinate ell z N x) ∧
      LinearMap.ker A.toLinearMap = LinearMap.ker (countablePairLift N planePairOperator).toLinearMap ∧
      ∀ s ∈ spectrum ℝ A, s = 0 ∨ 16/25 ≤ s := by
  simpa only [mul_one_div] using coordinatePhysical_kernel_gap doubleCoordinate doubleCoordinate_smooth
    (by simp [doubleCoordinate_jacobian]) 16 16 (by norm_num) (by simp [doubleCoordinate_weight]) ell hell N (1/25)
    (by simpa using countablePlane_old_bound N)

end VortexGap.Fermion
