import VortexGap.Fermion.CountableSplitFields

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open Filter
open scoped InnerProduct

def countableSplitSector (N : ℕ) : Submodule ℂ CountableSplitSpace where
  carrier := {x | ∀ AB : Finset ℕ × Finset ℕ, AB.1.card + AB.2.card ≠ N → x AB = 0}
  zero_mem' := by intro AB hAB; rfl
  add_mem' hx hy AB hAB := by simp [lp.coeFn_add, hx AB hAB, hy AB hAB]
  smul_mem' c x hx AB hAB := by simp [lp.coeFn_smul, hx AB hAB]

theorem countableSplitSector_isClosed (N : ℕ) :
    IsClosed (countableSplitSector N : Set CountableSplitSpace) := by
  have he : (countableSplitSector N : Set CountableSplitSpace) =
      ⋂ AB : Finset ℕ × Finset ℕ, ⋂ (_h : AB.1.card + AB.2.card ≠ N),
        {x | lp.evalCLM ℂ (fun _ : Finset ℕ × Finset ℕ => ℂ) 2 AB x = 0} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    rfl
  rw [he]
  exact isClosed_iInter fun AB => isClosed_iInter fun _ =>
    isClosed_eq (lp.evalCLM ℂ (fun _ : Finset ℕ × Finset ℕ => ℂ) 2 AB).continuous continuous_const

def countableSplitSectorComplete (N : ℕ) : CompleteSpace (countableSplitSector N) :=
  (countableSplitSector_isClosed N).isComplete.completeSpace_coe

attribute [instance] countableSplitSectorComplete

theorem countableSplitKet_sector (AB : Finset ℕ × Finset ℕ) :
    countableSplitKet AB ∈ countableSplitSector (AB.1.card + AB.2.card) := by
  intro CD hCD
  exact lp.single_apply_ne 2 AB 1 (fun h => hCD (congrArg (fun X => X.1.card + X.2.card) h))

theorem countableFockSplit_sector {N : ℕ} {x : CountableSpace} (hx : x ∈ countableSector N) :
    countableFockSplit x ∈ countableSplitSector N := by
  intro AB hAB
  rw [countableFockSplit_coefficient, countableJoinImage_ket, inner_smul_left,
    countableKet_inner_left, hx _ (by simpa only [countableSplitIndex_card] using hAB), mul_zero]

theorem countableFockJoin_sector {N : ℕ} {x : CountableSplitSpace}
    (hx : x ∈ countableSplitSector N) : countableFockJoin x ∈ countableSector N := by
  apply (countableSector_isClosed N).mem_of_tendsto (countableJoinIsometry_hasSum x)
  apply Eventually.of_forall
  intro s
  apply (countableSector N).sum_mem
  intro AB hAB
  by_cases hn : AB.1.card + AB.2.card = N
  · exact (countableSector N).smul_mem (x AB) (hn ▸ countableJoinImage_sector AB.1 AB.2)
  · rw [hx AB hn, zero_smul]
    exact (countableSector N).zero_mem

theorem countableFockSplit_sector_iff (N : ℕ) (x : CountableSpace) :
    countableFockSplit x ∈ countableSplitSector N ↔ x ∈ countableSector N := by
  constructor
  · intro hx
    simpa only [countableFockSplit, countableFockJoin.apply_symm_apply] using countableFockJoin_sector hx
  · exact countableFockSplit_sector

theorem countableFockJoin_sector_iff (N : ℕ) (x : CountableSplitSpace) :
    countableFockJoin x ∈ countableSector N ↔ x ∈ countableSplitSector N := by
  constructor
  · intro hx
    simpa only [countableFockSplit, countableFockJoin.symm_apply_apply] using countableFockSplit_sector hx
  · exact countableFockJoin_sector

def countableFockJoinSector (N : ℕ) : countableSplitSector N ≃ₗᵢ[ℂ] countableSector N where
  toFun x := ⟨countableFockJoin x, countableFockJoin_sector x.property⟩
  invFun x := ⟨countableFockSplit x, countableFockSplit_sector x.property⟩
  left_inv x := Subtype.ext (countableFockJoin.symm_apply_apply x)
  right_inv x := Subtype.ext (countableFockJoin.apply_symm_apply x)
  map_add' x y := Subtype.ext (countableFockJoin.map_add x y)
  map_smul' c x := Subtype.ext (countableFockJoin.map_smul c x)
  norm_map' x := countableFockJoin.norm_map x

theorem countableFockJoinSector_apply (N : ℕ) (x : countableSplitSector N) :
    (countableFockJoinSector N x : CountableSpace) = countableFockJoin x := rfl

def countableEnvironmentSector (K : ℕ) : Submodule ℂ CountableSplitSpace where
  carrier := {x | ∀ AB : Finset ℕ × Finset ℕ, AB.1.card ≠ K → x AB = 0}
  zero_mem' := by intro AB hAB; rfl
  add_mem' hx hy AB hAB := by simp [lp.coeFn_add, hx AB hAB, hy AB hAB]
  smul_mem' c x hx AB hAB := by simp [lp.coeFn_smul, hx AB hAB]

theorem countableEnvironmentSector_isClosed (K : ℕ) :
    IsClosed (countableEnvironmentSector K : Set CountableSplitSpace) := by
  have he : (countableEnvironmentSector K : Set CountableSplitSpace) =
      ⋂ AB : Finset ℕ × Finset ℕ, ⋂ (_h : AB.1.card ≠ K),
        {x | lp.evalCLM ℂ (fun _ : Finset ℕ × Finset ℕ => ℂ) 2 AB x = 0} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    rfl
  rw [he]
  exact isClosed_iInter fun AB => isClosed_iInter fun _ =>
    isClosed_eq (lp.evalCLM ℂ (fun _ : Finset ℕ × Finset ℕ => ℂ) 2 AB).continuous continuous_const

theorem countableEnvironmentSector_orthogonal {K L : ℕ} {x y : CountableSplitSpace}
    (hx : x ∈ countableEnvironmentSector K) (hy : y ∈ countableEnvironmentSector L)
    (hKL : K ≠ L) : inner ℂ x y = 0 := by
  rw [lp.inner_eq_tsum]
  calc
    _ = ∑' AB : Finset ℕ × Finset ℕ, (0 : ℂ) := by
      apply tsum_congr
      intro AB
      by_cases hA : AB.1.card = K
      · rw [hy AB (by omega), inner_zero_right]
      · rw [hx AB hA, inner_zero_left]
    _ = 0 := tsum_zero

theorem countableSplit_environment_too_many {N K : ℕ} {x : CountableSplitSpace}
    (hx : x ∈ countableSplitSector N) (he : x ∈ countableEnvironmentSector K)
    (hNK : N < K) : x = 0 := by
  ext AB
  change x AB = 0
  by_cases hA : AB.1.card = K
  · exact hx AB (by omega)
  · exact he AB hA

end VortexGap.Fermion
