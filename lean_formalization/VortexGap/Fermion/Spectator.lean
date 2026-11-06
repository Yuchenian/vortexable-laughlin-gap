import VortexGap.Fermion.Environment

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators InnerProduct

/-- Fix the spectator occupation, retaining the full reference Fock vector. -/
def referenceSlice {n m : ℕ} (B : Finset (Fin m)) : SplitSpace n m →ₗ[ℂ] Space n where
  toFun x := WithLp.toLp 2 (fun A => x (A,B))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem referenceSlice_apply {n m : ℕ} (B : Finset (Fin m)) (x : SplitSpace n m)
    (A : Finset (Fin n)) : referenceSlice B x A = x (A,B) := rfl

/-- Actual reference operator amplified by the spectator identity. -/
def referenceAmplify {n m : ℕ} (H : Module.End ℂ (Space n)) : Module.End ℂ (SplitSpace n m) where
  toFun x := WithLp.toLp 2 (fun AB => H (referenceSlice AB.2 x) AB.1)
  map_add' x y := by
    ext AB
    change H (referenceSlice AB.2 (x+y)) AB.1 = _
    rw [map_add, map_add]
    rfl
  map_smul' z x := by
    ext AB
    change H (referenceSlice AB.2 (z • x)) AB.1 = _
    rw [map_smul, map_smul]
    rfl

theorem referenceAmplify_apply {n m : ℕ} (H : Module.End ℂ (Space n))
    (x : SplitSpace n m) (A : Finset (Fin n)) (B : Finset (Fin m)) :
    referenceAmplify H x (A,B) = H (referenceSlice B x) A := rfl

theorem referenceSlice_amplify {n m : ℕ} (H : Module.End ℂ (Space n))
    (x : SplitSpace n m) (B : Finset (Fin m)) :
    referenceSlice B (referenceAmplify H x) = H (referenceSlice B x) := by
  ext A
  rfl

theorem referenceAmplify_mul {n m : ℕ} (H K : Module.End ℂ (Space n)) :
    referenceAmplify (m := m) (H*K) = referenceAmplify H * referenceAmplify K := by
  ext x AB
  change H (K (referenceSlice AB.2 x)) AB.1 = H (referenceSlice AB.2 (referenceAmplify K x)) AB.1
  rw [referenceSlice_amplify]

theorem referenceAmplify_inner {n m : ℕ} (H : Module.End ℂ (Space n)) (x y : SplitSpace n m) :
    inner ℂ x (referenceAmplify H y) =
      ∑ B, inner ℂ (referenceSlice B x) (H (referenceSlice B y)) := by
  simp only [PiLp.inner_apply, Fintype.sum_prod_type, referenceAmplify_apply, referenceSlice_apply]
  rw [Finset.sum_comm]

theorem referenceSlice_sector {n m N : ℕ} {x : Space (n+m)} (hx : InSector N x)
    (B : Finset (Fin m)) (hB : B.card ≤ N) :
    InSector (N-B.card) (referenceSlice B (fockSplit n m x)) := by
  intro A hA
  rw [referenceSlice_apply, fockSplit_apply]
  apply hx
  rw [joinOccupation_card]
  omega

theorem referenceSlice_zero_of_excess {n m N : ℕ} {x : Space (n+m)} (hx : InSector N x)
    (B : Finset (Fin m)) (hB : N < B.card) :
    referenceSlice B (fockSplit n m x) = 0 := by
  ext A
  rw [referenceSlice_apply, fockSplit_apply]
  apply hx
  rw [joinOccupation_card]
  omega

/-- The spectator inequality is derived by the actual finite occupation slicing.
Only reference sectors K ≤ N are assumed. Self-adjointness/positivity are not
needed for this algebraic implication; the reference input is a real quadratic inequality. -/
theorem referenceAmplify_sector_inequality {n m N : ℕ} (H : Module.End ℂ (Space n)) (γ : ℝ)
    (hgap : ∀ K ≤ N, ∀ y : Space n, InSector K y →
      γ * (inner ℂ y (H y)).re ≤ (inner ℂ y ((H*H) y)).re)
    {x : Space (n+m)} (hx : InSector N x) :
    γ * (inner ℂ (fockSplit n m x) (referenceAmplify H (fockSplit n m x))).re ≤
      (inner ℂ (fockSplit n m x)
        ((referenceAmplify (m := m) H * referenceAmplify (m := m) H) (fockSplit n m x))).re := by
  rw [← referenceAmplify_mul, referenceAmplify_inner, referenceAmplify_inner]
  simp only [Complex.re_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro B _
  by_cases hB : B.card ≤ N
  · exact hgap (N-B.card) (Nat.sub_le _ _) _ (referenceSlice_sector hx B hB)
  · rw [referenceSlice_zero_of_excess hx B (Nat.lt_of_not_ge hB)]
    simp

end VortexGap.Fermion
