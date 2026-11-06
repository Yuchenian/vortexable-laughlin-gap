import VortexGap.Physical.SphereContactGap
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory OAI.Laughlin.Rotation
open scoped InnerProduct ComplexOrder
theorem sphereReference_two (n K : ℕ) (hK : K ≤ 2) (y : Space (n+2)) (hy : InSector K y) :
    let H := pairLift (spherePairSector n).starProjection.toLinearMap
    1*(inner ℂ y (H y)).re ≤ (inner ℂ y ((H*H) y)).re := by
  let P := (spherePairSector n).starProjection
  have hid : pairLift P.toLinearMap (pairLift P.toLinearMap y) = pairLift P.toLinearMap y := by
    interval_cases K
    · rw [pairLift_sector_zero _ hy,map_zero]
    · rw [pairLift_sector_one _ hy,map_zero]
    · obtain ⟨p,rfl⟩ := (pairEmbed_range_iff y).mpr hy
      simp only [pairLift_pairEmbed,ContinuousLinearMap.coe_coe]
      rw [Submodule.starProjection_eq_self_iff.mpr ((spherePairSector n).starProjection_apply_mem p)]
  simpa only [one_mul,Module.End.mul_apply] using
    (congrArg (fun z => (inner ℂ y z).re) hid).symm.le

/-- A nonuniform axial sphere multiplier, invariant under a local change of spinor phase. -/
def sphereAxialMultiplier (g : SourceSU2) : ℂ := (Real.sqrt (1+‖g.val 0 0‖^2/1000) : ℂ)

theorem sphereAxialMultiplier_continuous : Continuous sphereAxialMultiplier := by
  apply Complex.continuous_ofReal.comp
  apply Real.continuous_sqrt.comp
  apply continuous_const.add
  apply Continuous.div_const
  have hc : Continuous (fun g : SourceSU2 => g.val 0 0) :=
    (continuous_apply 0).comp ((continuous_apply 0).comp continuous_subtype_val)
  exact hc.norm.pow 2

theorem sphereAxialMultiplier_weight (g : SourceSU2) :
    ‖sphereAxialMultiplier g‖^2 = 1+‖g.val 0 0‖^2/1000 := by
  simp [sphereAxialMultiplier,Complex.norm_real,Real.norm_eq_abs,sq_abs,Real.sq_sqrt (by positivity : 0 ≤ 1+‖g.val 0 0‖^2/1000)]

theorem sphereAxialMultiplier_not_constant : ¬ ∀ g, sphereAxialMultiplier g = sphereAxialMultiplier 1 := by
  intro hc
  have hnorm (g : SourceSU2) : ‖g.val 0 0‖^2 = 1 := by
    have h := congrArg (fun z : ℂ => ‖z‖^2) (hc g)
    change ‖sphereAxialMultiplier g‖^2 = ‖sphereAxialMultiplier 1‖^2 at h
    simp only [sphereAxialMultiplier_weight] at h
    have h1 : ‖(1 : SourceSU2).val 0 0‖ = 1 := by simp
    rw [h1] at h
    linarith
  have h := sphereHaar_radial_moment 1
  simp only [pow_one,hnorm,integral_const] at h
  norm_num at h
theorem sphereAxial_two_gap (n : ℕ) :
    ∀ t ∈ spectrum ℝ (sphereSectorHam n 2 (spherePhysicalPair n sphereAxialMultiplier sphereAxialMultiplier_continuous)),
      t = 0 ∨ (9860/10000:ℝ) ≤ t := by
  have hlo (g) : 1 ≤ ‖sphereAxialMultiplier g‖^2 := by rw [sphereAxialMultiplier_weight]; linarith [sq_nonneg (‖g.val 0 0‖)]
  have hhi (g) : ‖sphereAxialMultiplier g‖^2 ≤ (1001/1000:ℝ) := by
    rw [sphereAxialMultiplier_weight]
    have h := unitary_entry_norm_le_one g.val g.property.1 0 0
    nlinarith [sq_nonneg (1-‖g.val 0 0‖),mul_nonneg (sub_nonneg.mpr h) (add_nonneg (norm_nonneg (g.val 0 0)) zero_le_one)]
  intro t ht
  refine (spherePhysical_gap n 2 _ sphereAxialMultiplier_continuous _ _ zero_lt_one hlo hhi 1
    (sphereReference_two n) t ht).imp_right (le_trans ?_)
  norm_num

end VortexGap.Fermion
