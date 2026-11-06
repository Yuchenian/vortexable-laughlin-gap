import OAI.Analysis.Laughlin.Pair.Conjugation
import VortexGap.Geometry.PlaneBinomial
noncomputable section
namespace VortexGap.Fermion

theorem upstream_pair_coefficient (n i : ℕ) (hn : 0 < n) (hi : i ≤ n) :
    -(Real.sqrt 2) * OAI.Laughlin.pairLimitCoefficient (n-1) i (n-i) =
      planeBlockCoefficient n i := by
  rw [planeBlockCoefficient_factorial n hn i hi]
  unfold OAI.Laughlin.pairLimitCoefficient
  rw [if_pos (by omega : i + (n-i) = n-1+1)]
  rw [Nat.cast_sub hi]
  have hs : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  push_cast
  field_simp
  <;> ring

theorem upstream_ordered_coefficient (n i : ℕ) (hn : 0 < n) (hi : i ≤ n) :
    2 * (OAI.Laughlin.pairLimitCoefficient (n-1) i (n-i) / Real.sqrt 2) =
      -planeBlockCoefficient n i := by
  have h := upstream_pair_coefficient n i hn hi
  have hs : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hs2 : (Real.sqrt (2 : ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
  rw [← mul_div_assoc]
  apply (div_eq_iff hs).2
  calc
    _ = (Real.sqrt (2 : ℝ))^2 * OAI.Laughlin.pairLimitCoefficient (n-1) i (n-i) := by rw [hs2]
    _ = -(-Real.sqrt 2 * OAI.Laughlin.pairLimitCoefficient (n-1) i (n-i)) * Real.sqrt 2 := by ring
    _ = _ := by rw [h]

end VortexGap.Fermion
