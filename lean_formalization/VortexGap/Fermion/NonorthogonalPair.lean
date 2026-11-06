import VortexGap.Frame.NonorthogonalPair
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open VortexGap.Frame

/-- The finite orbital CAR exterior product uses precisely the wedge norm as its coefficient. -/
theorem wedgePair_orthogonal_normalize {n : ℕ}
    (base : EuclideanSpace ℂ (Fin 2) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n))
    (u v : EuclideanSpace ℂ (Fin n)) :
    let T := orthogonalPairFrame base u v
    wedgePair u v = (‖wedgePair u v‖:ℂ) • wedgePair (T (PiLp.single 2 0 1)) (T (PiLp.single 2 1 1)) := by
  have hunit (T : EuclideanSpace ℂ (Fin 2) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) :
      ‖wedgePair (T (PiLp.single 2 0 1)) (T (PiLp.single 2 1 1))‖ = 1 := by
    apply wedgePair_unit_norm <;> simp [EuclideanSpace.inner_single_left]
  have hare := alternating_pair_area_eq_norm (wedgePairBilinear n) wedgePair_self hunit base u v
  have h := alternating_pair_normalize (wedgePairBilinear n) wedgePair_self base u v
  rw [hare] at h
  exact h

/-- Dimensions zero and one need no fallback frame, since every CAR pair vanishes. -/
theorem wedgePair_eq_zero_low_dim {n : ℕ} (hn : n ≤ 1) (u v : EuclideanSpace ℂ (Fin n)) :
    wedgePair u v = 0 := by
  ext a
  have h := a.property
  have h1 := a.val.1.isLt
  have h2 := a.val.2.isLt
  change a.val.1.val < a.val.2.val at h
  omega

theorem wedgePair_norm_sq_gram {n : ℕ} (u v : EuclideanSpace ℂ (Fin n)) :
    ‖wedgePair u v‖^2 = ‖u‖^2*‖v‖^2-‖inner ℂ u v‖^2 := by
  have hh := wedgePair_inner u v u v
  rw [inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K,
    ← inner_conj_symm v u,Complex.mul_conj,← Complex.sq_norm] at hh
  apply Complex.ofReal_injective
  push_cast
  simpa only [Complex.ofReal_pow] using! hh

/-- Complex nonorthogonal input (e₀, i e₀ + 2i e₁), plus the collinear label (e₀,i e₀). -/
theorem nonorthogonal_two_column_test :
    let a : EuclideanSpace ℂ (Fin 2) := PiLp.single 2 0 1
    let b : EuclideanSpace ℂ (Fin 2) := PiLp.single 2 1 1
    let v := Complex.I • a + (2*Complex.I) • b
    let base := LinearIsometry.id (R := ℂ) (E := EuclideanSpace ℂ (Fin 2))
    pairColumnArea a v = 2 ∧ orthogonalPairFrame base a v b = Complex.I • b ∧
      pairColumnArea a (Complex.I • a) = 0 ∧ wedgePair a v = (2*Complex.I) • wedgePair a b := by
  let a : EuclideanSpace ℂ (Fin 2) := PiLp.single 2 0 1
  let b : EuclideanSpace ℂ (Fin 2) := PiLp.single 2 1 1
  let v := Complex.I • a + (2*Complex.I) • b
  let base := LinearIsometry.id (R := ℂ) (E := EuclideanSpace ℂ (Fin 2))
  have ha : ‖a‖ = 1 := by simp [a]
  have hb : ‖b‖ = 1 := by simp [b]
  have hab : inner ℂ a b = 0 := by simp [a,b,EuclideanSpace.inner_single_left]
  have haa : inner ℂ a a = 1 := by rw [inner_self_eq_norm_sq_to_K,ha]; norm_num
  have hua : unitColumn a = a := by simp [unitColumn,ha]
  have hr : residualColumn a v = (2*Complex.I) • b := by
    simp only [residualColumn,hua,v,inner_add_right,inner_smul_right,hab,haa,mul_one,mul_zero,add_zero]
    abel
  have hnr : ‖residualColumn a v‖ = 2 := by rw [hr,norm_smul,norm_mul,hb]; norm_num
  have hnon : a ≠ 0 ∧ residualColumn a v ≠ 0 := by
    constructor <;> intro h
    · simp [h] at ha
    · simp [h] at hnr
  change pairColumnArea a v = 2 ∧ orthogonalPairFrame base a v b = _ ∧ pairColumnArea a _ = 0 ∧ wedgePair a v = _
  refine ⟨by simp [pairColumnArea,ha,hnr],?_,?_,?_⟩
  · rw [show b = (PiLp.single 2 1 1 : EuclideanSpace ℂ (Fin 2)) from rfl,orthogonalPairFrame_column,ite_eq_left hnon]
    change unitColumn (residualColumn a v) = Complex.I • b
    rw [unitColumn,hnr,hr,smul_smul]
    congr 1
    push_cast
    ring
  · change pairColumnArea a (Complex.I • a) = 0
    simp only [pairColumnArea,residualColumn,hua,inner_smul_right,haa,mul_one,sub_self,norm_zero,mul_zero]
  · change wedgePairBilinear 2 a v = (2*Complex.I) • wedgePairBilinear 2 a b
    simp [v,map_add,map_smul,show wedgePairBilinear 2 a a = 0 from wedgePair_self a]

end VortexGap.Fermion
