import VortexGap.Fermion.CountableApproximation
import VortexGap.Fermion.NumberParity

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open Filter
open scoped InnerProduct Topology

/-- Closed actual occupation-number sector in the full countable-mode Fock space. -/
def countableSector (N : ℕ) : Submodule ℂ CountableSpace where
  carrier := {x | ∀ A : Finset ℕ, A.card ≠ N → x A = 0}
  zero_mem' := by intro A hA; rfl
  add_mem' hx hy A hA := by simp [lp.coeFn_add, hx A hA, hy A hA]
  smul_mem' c x hx A hA := by simp [lp.coeFn_smul, hx A hA]

theorem countableSector_isClosed (N : ℕ) : IsClosed (countableSector N : Set CountableSpace) := by
  have he : (countableSector N : Set CountableSpace) =
      ⋂ A : Finset ℕ, ⋂ (_h : A.card ≠ N), {x | lp.evalCLM ℂ (fun _ : Finset ℕ => ℂ) 2 A x = 0} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    rfl
  rw [he]
  exact isClosed_iInter fun A => isClosed_iInter fun _ =>
    isClosed_eq (lp.evalCLM ℂ (fun _ : Finset ℕ => ℂ) 2 A).continuous continuous_const

instance countableSector_complete (N : ℕ) : CompleteSpace (countableSector N) :=
  (countableSector_isClosed N).isComplete.completeSpace_coe

theorem countableKet_sector (A : Finset ℕ) : countableKet A ∈ countableSector A.card := by
  intro B hB
  have h : B ≠ A := fun he => hB (congrArg Finset.card he)
  exact lp.single_apply_ne 2 A 1 h

theorem countableRestrict_sector {N n : ℕ} {x : CountableSpace}
    (hx : x ∈ countableSector N) : InSector N (countableRestrict n x) := by
  intro A hA
  rw [countableRestrict_coefficient]
  exact hx (occupationIndex A) (by simpa only [occupationIndex_card] using hA)

theorem countableEmbed_sector {N n : ℕ} {x : Space n} (hx : InSector N x) :
    countableEmbed n x ∈ countableSector N := by
  intro B hB
  by_cases hs : B ⊆ Finset.range n
  · obtain ⟨A, rfl⟩ := occupationIndex_exists B hs
    change countableEmbedLinear n x (occupationIndex A) = 0
    rw [countableEmbedLinear_coefficient]
    exact hx A (by simpa only [occupationIndex_card] using hB)
  · exact countableEmbed_outside x B hs

theorem countableEmbed_sector_iff {N n : ℕ} (x : Space n) :
    countableEmbed n x ∈ countableSector N ↔ InSector N x := by
  constructor
  · intro hx
    simpa only [countableRestrict_embed] using countableRestrict_sector (n := n) hx
  · exact countableEmbed_sector

theorem countableCutoff_sector {N : ℕ} (n : ℕ) {x : CountableSpace}
    (hx : x ∈ countableSector N) : countableCutoff n x ∈ countableSector N := by
  intro A hA
  rw [countableCutoff_coefficient]
  split_ifs
  · exact hx A hA
  · rfl

/-- Every actual fixed-N state has finite-mode, same-N approximants in Hilbert norm. -/
theorem countableSector_finite_approximation {N : ℕ} (x : countableSector N)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n, ∃ y : Space n, InSector N y ∧ ‖countableEmbed n y - (x : CountableSpace)‖ < ε := by
  obtain ⟨n, hn⟩ := Metric.tendsto_atTop.mp (countableEmbed_restrict_tendsto (x : CountableSpace)) ε hε
  refine ⟨n, countableRestrict n x, countableRestrict_sector x.property, ?_⟩
  simpa only [dist_eq_norm] using hn n le_rfl

end VortexGap.Fermion

