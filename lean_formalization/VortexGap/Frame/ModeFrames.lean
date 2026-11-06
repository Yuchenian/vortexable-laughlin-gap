import VortexGap.Examples.CellReference

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open VortexGap.Frame
open scoped BigOperators InnerProduct ComplexConjugate

/-- The actual two orbital columns of a canonical pair. -/
def modeFrameMap {n : ℕ} (a : PairIndex n) : TwoSpace →ₗ[ℂ] EuclideanSpace ℂ (Fin n) where
  toFun x := x 0 • PiLp.single 2 a.val.1 1 + x 1 • PiLp.single 2 a.val.2 1
  map_add' x y := by simp only [PiLp.add_apply, add_smul]; abel
  map_smul' z x := by simp only [PiLp.smul_apply, smul_eq_mul, smul_add, smul_smul, RingHom.id_apply]

theorem modeFrameMap_apply {n : ℕ} (a : PairIndex n) (x : TwoSpace) :
    modeFrameMap a x = x 0 • PiLp.single 2 a.val.1 1 + x 1 • PiLp.single 2 a.val.2 1 := rfl

theorem modeFrameMap_inner {n : ℕ} (a : PairIndex n) (x y : TwoSpace) :
    inner ℂ (modeFrameMap a x) (modeFrameMap a y) = inner ℂ x y := by
  have hne := ne_of_lt a.property
  rw [modeFrameMap_apply, modeFrameMap_apply]
  simp [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    EuclideanSpace.inner_single_left, PiLp.single_apply, hne, Ne.symm hne,
    PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, mul_comm]

def modeFrame {n : ℕ} (a : PairIndex n) : TwoFrame n where
  toLinearMap := modeFrameMap a
  norm_map' := (LinearMap.norm_map_iff_inner_map_map _).mpr (modeFrameMap_inner a)

theorem modeFrame_first {n : ℕ} (a : PairIndex n) :
    modeFrame a (PiLp.single 2 0 1) = PiLp.single 2 a.val.1 1 := by
  change modeFrameMap a _ = _
  rw [modeFrameMap_apply]
  simp

theorem modeFrame_second {n : ℕ} (a : PairIndex n) :
    modeFrame a (PiLp.single 2 1 1) = PiLp.single 2 a.val.2 1 := by
  change modeFrameMap a _ = _
  rw [modeFrameMap_apply]
  simp

theorem modeFrame_wedge {n : ℕ} (a : PairIndex n) :
    wedgePair (modeFrame a (PiLp.single 2 0 1)) (modeFrame a (PiLp.single 2 1 1)) = pairBasis a := by
  rw [modeFrame_first, modeFrame_second, wedgePair_basis]

theorem twoFrameOverlap_self {n : ℕ} (U : TwoFrame n) :
    twoFrameOverlap U U = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  change inner ℂ y (U.toLinearMap.adjoint (U x)) = inner ℂ y x
  rw [LinearMap.adjoint_inner_right]
  exact U.inner_map_map y x

theorem modeFrameOverlap_zero {n : ℕ} (a b : PairIndex n)
    (h00 : a.val.1 ≠ b.val.1) (h01 : a.val.1 ≠ b.val.2)
    (h10 : a.val.2 ≠ b.val.1) (h11 : a.val.2 ≠ b.val.2) :
    twoFrameOverlap (modeFrame a) (modeFrame b) = 0 := by
  apply (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis.ext
  intro j
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  ext i
  change twoFrameOverlap (modeFrame a) (modeFrame b) (PiLp.single 2 j 1) i = 0
  rw [twoFrameOverlap_entry]
  fin_cases i <;> fin_cases j <;>
    simp [modeFrame_first, modeFrame_second, EuclideanSpace.inner_single_left,
      PiLp.single_apply, h00, h01, h10, h11, Ne.symm h00, Ne.symm h01, Ne.symm h10, Ne.symm h11]

theorem pairBasis_frame_energy {n : ℕ} {ι : Type*} [Fintype ι]
    (a : ι → PairIndex n) (q : PairSpace n) :
    (inner ℂ q ((∑ i, pairRankOne (pairBasis (a i))) q)).re = ∑ i, ‖q (a i)‖^2 := by
  simp only [LinearMap.sum_apply, inner_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [pairRankOne, InnerProductSpace.rankOne_apply, ContinuousLinearMap.coe_coe,
    pairBasis, EuclideanSpace.inner_single_left, map_one, one_mul, inner_smul_right,
    EuclideanSpace.inner_single_right, mul_one, Complex.mul_conj']
  simp only [← Complex.ofReal_pow, Complex.ofReal_re]

theorem pairBasis_frame_le_one {n : ℕ} {ι : Type*} [Fintype ι]
    (a : ι → PairIndex n) (ha : Function.Injective a) (q : PairSpace n) :
    (inner ℂ q ((∑ i, pairRankOne (pairBasis (a i))) q)).re ≤ ‖q‖^2 := by
  classical
  rw [pairBasis_frame_energy, EuclideanSpace.norm_sq_eq]
  calc
    _ = ∑ b ∈ Finset.univ.image a, ‖q b‖^2 := by
      rw [Finset.sum_image]; exact fun i _ j _ h => ha h
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun b _ _ => sq_nonneg ‖q b‖)

end VortexGap.Fermion
