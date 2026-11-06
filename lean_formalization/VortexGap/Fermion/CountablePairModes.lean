import VortexGap.Fermion.CountableBasis
import VortexGap.Fermion.PairBounds

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct

/-- An unordered pair represented once, with its smaller mode first. -/
abbrev CountablePairIndex := {ij : ℕ × ℕ // ij.1 < ij.2}
abbrev CountablePairSpace := lp (fun _ : CountablePairIndex => ℂ) 2

def pairIndexNat {n : ℕ} (a : PairIndex n) : CountablePairIndex :=
  ⟨(a.val.1.val, a.val.2.val), a.property⟩

def countablePairOccupation (a : CountablePairIndex) : Finset ℕ := {a.val.1, a.val.2}

theorem pairIndexNat_injective (n : ℕ) : Function.Injective (@pairIndexNat n) := by
  intro a b h
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    exact congrArg (fun p : CountablePairIndex => p.val.1) h
  · apply Fin.ext
    exact congrArg (fun p : CountablePairIndex => p.val.2) h

theorem countablePairOccupation_card (a : CountablePairIndex) :
    (countablePairOccupation a).card = 2 := by
  simp [countablePairOccupation, ne_of_lt a.property]

theorem countablePairOccupation_injective : Function.Injective countablePairOccupation := by
  intro a b h
  have hi : a.val.1 = b.val.1 ∨ a.val.1 = b.val.2 := by
    have hm : a.val.1 ∈ countablePairOccupation a := by simp [countablePairOccupation]
    rw [h] at hm
    simpa [countablePairOccupation] using hm
  have hj : a.val.2 = b.val.1 ∨ a.val.2 = b.val.2 := by
    have hm : a.val.2 ∈ countablePairOccupation a := by simp [countablePairOccupation]
    rw [h] at hm
    simpa [countablePairOccupation] using hm
  have ha := a.property
  have hb := b.property
  apply Subtype.ext
  apply Prod.ext <;> omega

/-- The larger mode annihilates after the smaller one, matching B(p). -/
def countablePairMode (a : CountablePairIndex) : CountableSpace →L[ℂ] CountableSpace :=
  countableAnnihilateMode a.val.2 * countableAnnihilateMode a.val.1

def countablePairKet (a : CountablePairIndex) : CountableSpace :=
  (countablePairMode a).adjoint (countableKet ∅)

theorem countablePairMode_adjoint (a : CountablePairIndex) :
    (countablePairMode a).adjoint =
      countableCreateMode a.val.1 * countableCreateMode a.val.2 := by
  change ((countableAnnihilateMode a.val.2).comp (countableAnnihilateMode a.val.1)).adjoint = _
  rw [ContinuousLinearMap.adjoint_comp, countableTransition_adjoint, countableTransition_adjoint]
  rfl

theorem countablePairMode_opNorm_le (a : CountablePairIndex) : ‖countablePairMode a‖ ≤ 1 := by
  calc
    _ ≤ ‖countableAnnihilateMode a.val.2‖ * ‖countableAnnihilateMode a.val.1‖ := norm_mul_le _ _
    _ = 1 := by rw [countableTransition_opNorm_eq_one, countableTransition_opNorm_eq_one]; norm_num

theorem countablePairMode_sector {N : ℕ} (a : CountablePairIndex) {x : CountableSpace}
    (hx : x ∈ countableSector (N + 2)) : countablePairMode a x ∈ countableSector N :=
  countableAnnihilateMode_sector _ (countableAnnihilateMode_sector _ hx)

theorem countablePairMode_zero_sector (a : CountablePairIndex) {x : CountableSpace}
    (hx : x ∈ countableSector 0) : countablePairMode a x = 0 := by
  change countableAnnihilateMode a.val.2 (countableAnnihilateMode a.val.1 x) = 0
  rw [countableAnnihilateMode_zero_sector _ hx, map_zero]

theorem countablePairMode_one_sector (a : CountablePairIndex) {x : CountableSpace}
    (hx : x ∈ countableSector 1) : countablePairMode a x = 0 :=
  countableAnnihilateMode_zero_sector _ (countableAnnihilateMode_sector _ hx)

theorem countablePairMode_embed {n : ℕ} (a : PairIndex n) (x : Space n) :
    countablePairMode (pairIndexNat a) (countableEmbed n x) = countableEmbed n (pairMode a x) := by
  change countableAnnihilateMode a.val.2.val
    (countableAnnihilateMode a.val.1.val (countableEmbed n x)) = _
  rw [countableTransition_embed, countableTransition_embed]
  rfl

theorem countablePairKet_occupation (a : CountablePairIndex) :
    countablePairKet a = countableKet (countablePairOccupation a) := by
  unfold countablePairKet
  rw [countablePairMode_adjoint]
  change countableCreateMode a.val.1 (countableCreateMode a.val.2 (countableKet ∅)) = _
  have hj : countableCreateMode a.val.2 (countableKet ∅) = countableKet {a.val.2} := by
    rw [countableCreateMode_ket _ _ (by simp)]
    simp [countableSign]
  rw [hj, countableCreateMode_ket _ _ (by simp [ne_of_lt a.property])]
  simp [countableSign, countablePairOccupation, Finset.filter_singleton, not_lt_of_gt a.property]

theorem countablePairKet_norm (a : CountablePairIndex) : ‖countablePairKet a‖ = 1 := by
  rw [countablePairKet_occupation, countableKet_norm]

theorem countablePairKet_inner (a b : CountablePairIndex) :
    inner ℂ (countablePairKet a) (countablePairKet b) = if a = b then 1 else 0 := by
  rw [countablePairKet_occupation, countablePairKet_occupation, countableKet_inner]
  simp only [countablePairOccupation_injective.eq_iff]

theorem countablePairKet_sector (a : CountablePairIndex) :
    countablePairKet a ∈ countableSector 2 := by
  rw [countablePairKet_occupation]
  simpa only [countablePairOccupation_card] using countableKet_sector (countablePairOccupation a)

theorem countablePairKet_embed {n : ℕ} (a : PairIndex n) :
    countableEmbed n (pairKet a) = countablePairKet (pairIndexNat a) := by
  rw [pairKet, pairMode_adjoint]
  change countableEmbed n (createMode a.val.1 (createMode a.val.2 (ket ∅))) = _
  rw [← countableTransition_embed a.val.1 true, ← countableTransition_embed a.val.2 true,
    countableEmbed_ket]
  change countableCreateMode a.val.1.val (countableCreateMode a.val.2.val (countableKet ∅)) = _
  unfold countablePairKet
  rw [countablePairMode_adjoint]
  rfl

end VortexGap.Fermion

