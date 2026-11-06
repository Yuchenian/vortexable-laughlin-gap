import VortexGap.Fermion.CountableOrbitalActions
import Mathlib.Data.Finset.Sort

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct

/-- Actual ordered creation words on the completed occupation Fock space. -/
def countableWord (v : ℕ → CountableOrbital) : List ℕ → CountableSpace
  | [] => countableKet ∅
  | j :: js => countableCreate (v j) (countableWord v js)

theorem countableWord_nil (v : ℕ → CountableOrbital) :
    countableWord v [] = countableKet ∅ := rfl

theorem countableWord_cons (v : ℕ → CountableOrbital) (j : ℕ) (js : List ℕ) :
    countableWord v (j :: js) = countableCreate (v j) (countableWord v js) := rfl

theorem countableCreate_inner (v : CountableOrbital) (x y : CountableSpace) :
    inner ℂ (countableCreate v x) y = inner ℂ x (countableAnnihilate v y) :=
  (ContinuousLinearMap.adjoint_inner_right (countableCreate v) x y).symm

theorem countableAnnihilate_create (v w : CountableOrbital) (x : CountableSpace) :
    countableAnnihilate v (countableCreate w x) =
      (inner ℂ v w) • x - countableCreate w (countableAnnihilate v x) := by
  have h := congrArg (fun T : CountableSpace →L[ℂ] CountableSpace => T x)
    (countableOrbital_car v w)
  change countableAnnihilate v (countableCreate w x) +
    countableCreate w (countableAnnihilate v x) = (inner ℂ v w) • x at h
  exact eq_sub_of_add_eq h

theorem countableWord_sector (v : ℕ → CountableOrbital) (js : List ℕ) :
    countableWord v js ∈ countableSector js.length := by
  induction js with
  | nil => simpa only [countableWord_nil, List.length_nil, Finset.card_empty]
      using countableKet_sector ∅
  | cons j js ih => exact countableCreate_sector (v j) ih

theorem countableAnnihilate_word_of_not_mem (v : ℕ → CountableOrbital)
    (hv : Orthonormal ℂ v) (j : ℕ) (js : List ℕ) (hj : j ∉ js) :
    countableAnnihilate (v j) (countableWord v js) = 0 := by
  induction js with
  | nil => exact countableAnnihilate_vacuum _
  | cons k ks ih =>
      have hne : j ≠ k := fun h => hj (by simp [h])
      have hn : j ∉ ks := fun h => hj (List.mem_cons_of_mem k h)
      rw [countableWord_cons, countableAnnihilate_create,
        (orthonormal_iff_ite.mp hv) j k, ite_eq_right hne, zero_smul, ih hn, map_zero, sub_zero]

theorem countableAnnihilate_word_cons (v : ℕ → CountableOrbital)
    (hv : Orthonormal ℂ v) (j : ℕ) (js : List ℕ) (hj : j ∉ js) :
    countableAnnihilate (v j) (countableWord v (j :: js)) = countableWord v js := by
  rw [countableWord_cons, countableAnnihilate_create, (orthonormal_iff_ite.mp hv) j j,
    ite_eq_left rfl, one_smul, countableAnnihilate_word_of_not_mem v hv j js hj,
    map_zero, sub_zero]

theorem countableWord_inner_self (v : ℕ → CountableOrbital)
    (hv : Orthonormal ℂ v) (js : List ℕ) (hjs : js.Nodup) :
    inner ℂ (countableWord v js) (countableWord v js) = 1 := by
  induction js with
  | nil => exact (countableKet_inner ∅ ∅).trans (ite_eq_left rfl)
  | cons j js ih =>
      rw [List.nodup_cons] at hjs
      rw [countableWord_cons, countableCreate_inner]
      change inner ℂ (countableWord v js)
        (countableAnnihilate (v j) (countableWord v (j :: js))) = 1
      rw [countableAnnihilate_word_cons v hv j js hjs.1, ih hjs.2]

/-- The occupation projector of a present orbital fixes the actual word. -/
theorem countableWord_occupied (v : ℕ → CountableOrbital)
    (hv : Orthonormal ℂ v) (j : ℕ) (js : List ℕ) (hjs : js.Nodup) (hj : j ∈ js) :
    countableCreate (v j) (countableAnnihilate (v j) (countableWord v js)) =
      countableWord v js := by
  induction js with
  | nil => simp at hj
  | cons k ks ih =>
      rw [List.nodup_cons] at hjs
      by_cases he : j = k
      · subst k
        rw [countableAnnihilate_word_cons v hv j ks hjs.1, countableWord_cons]
      · have hmem : j ∈ ks := (List.mem_cons.mp hj).resolve_left he
        have ha := congrArg (fun T : CountableSpace →L[ℂ] CountableSpace =>
          T (countableAnnihilate (v j) (countableWord v ks)))
          (countableCreate_anticommute (v j) (v k))
        change countableCreate (v j) (countableCreate (v k) _) =
          -(countableCreate (v k) (countableCreate (v j) _)) at ha
        rw [countableWord_cons, countableAnnihilate_create,
          (orthonormal_iff_ite.mp hv) j k, ite_eq_right he, zero_smul, zero_sub, map_neg,
          ha, neg_neg, ih hjs.2 hmem]

theorem countableWord_inner_zero_of_mem (v : ℕ → CountableOrbital)
    (hv : Orthonormal ℂ v) (js ks : List ℕ) (hjs : js.Nodup)
    (j : ℕ) (hj : j ∈ js) (hk : j ∉ ks) :
    inner ℂ (countableWord v js) (countableWord v ks) = 0 := by
  calc
    _ = inner ℂ (countableCreate (v j) (countableAnnihilate (v j) (countableWord v js)))
        (countableWord v ks) := by rw [countableWord_occupied v hv j js hjs hj]
    _ = 0 := by rw [countableCreate_inner, countableAnnihilate_word_of_not_mem v hv j ks hk,
      inner_zero_right]

theorem countableWord_norm (v : ℕ → CountableOrbital)
    (hv : Orthonormal ℂ v) (js : List ℕ) (hjs : js.Nodup) :
    ‖countableWord v js‖ = 1 := by
  have h := inner_self_eq_norm_sq (𝕜 := ℂ) (countableWord v js)
  rw [countableWord_inner_self v hv js hjs] at h
  norm_num at h
  nlinarith [norm_nonneg (countableWord v js)]

end VortexGap.Fermion
