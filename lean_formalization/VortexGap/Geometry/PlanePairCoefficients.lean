import VortexGap.Geometry.PlaneTwoFrame
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct

/-- The determinant formula includes z=0 and every natural pair of indices;
no division by z or nonzero-coordinate hypothesis is used. -/
theorem planeBargmann_jet_determinant (z : ℂ) (i j : ℕ) :
    planeBargmannCoeff z i * planeJetCoeff z j -
      planeJetCoeff z i * planeBargmannCoeff z j =
    ((j : ℂ)-(i : ℂ))*z^(i+j-1) /
      ((Real.sqrt (i.factorial : ℝ) : ℂ)*(Real.sqrt (j.factorial : ℝ) : ℂ)) := by
  cases i with
  | zero =>
    cases j with
    | zero => simp [planeBargmannCoeff, planeJetCoeff]
    | succ j => simp [planeBargmannCoeff, planeJetCoeff]
  | succ i =>
    cases j with
    | zero => simp [planeBargmannCoeff, planeJetCoeff]; ring
    | succ j =>
      have he : i+1+(j+1)-1 = i+j+1 := by omega
      simp only [planeBargmannCoeff, planeJetCoeff, he, Nat.cast_add, Nat.cast_one,
        pow_add, pow_one]
      ring

/-- The exact coherent-pair coefficient in every ordered occupation mode,
with the Gaussian and factorial normalization of the current supplement. -/
theorem planeTwoFramePair_coefficient (z : ℂ) (a : CountablePairIndex) :
    countableTwoFramePair (planeTwoFrame z) a =
      (Real.exp (-‖z‖^2) : ℂ) *
        ((a.val.2 : ℂ)-(a.val.1 : ℂ))*z^(a.val.1+a.val.2-1) /
          (Real.sqrt ((a.val.1.factorial : ℝ)*(a.val.2.factorial : ℝ)) : ℂ) := by
  rw [planeTwoFramePair_jet]
  change (Real.exp (-‖z‖^2) : ℂ) *
    countableWedge (planeBargmann z) (planeJet z) a = _
  rw [countableWedge_coordinate]
  change (Real.exp (-‖z‖^2) : ℂ) *
    (planeBargmannCoeff z a.val.1 * planeJetCoeff z a.val.2 -
      planeJetCoeff z a.val.1 * planeBargmannCoeff z a.val.2) = _
  rw [planeBargmann_jet_determinant, Real.sqrt_mul (by positivity), Complex.ofReal_mul]
  ring

/-- At the origin the actual coherent pair is exactly the normalized occupied
modes 0,1, fixing the orientation and excluding an extra factor of two. -/
theorem planeTwoFramePair_zero :
    countableTwoFramePair (planeTwoFrame 0) =
      (lp.single 2 (⟨(0,1), by decide⟩ : CountablePairIndex) 1 : CountablePairSpace) := by
  ext a
  by_cases ha : a = (⟨(0,1), by decide⟩ : CountablePairIndex)
  · subst a
    simp [planeTwoFramePair_coefficient, lp.single_apply]
  · have hn : a.val.1+a.val.2-1 ≠ 0 := by
      intro hn
      have hp := a.property
      have hi : a.val.1 = 0 := by omega
      have hj : a.val.2 = 1 := by omega
      apply ha
      apply Subtype.ext
      exact Prod.ext hi hj
    rw [planeTwoFramePair_coefficient]
    simp [zero_pow hn, lp.single_apply, ha]

end VortexGap.Fermion
