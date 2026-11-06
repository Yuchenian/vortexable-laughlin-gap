import VortexGap.Fermion.CountableFockCovariance

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion

def countableWordSign : List ℕ → ℂ
  | [] => 1
  | j :: js => countableSign j js.toFinset * countableWordSign js

theorem countableWordSign_norm (js : List ℕ) : ‖countableWordSign js‖ = 1 := by
  induction js with
  | nil => simp [countableWordSign]
  | cons j js ih => simp [countableWordSign, norm_mul, ih]

theorem countableWordSign_sq (js : List ℕ) :
    countableWordSign js * countableWordSign js = 1 := by
  induction js with
  | nil => simp [countableWordSign]
  | cons j js ih =>
      calc
        _ = (countableSign j js.toFinset * countableSign j js.toFinset) *
            (countableWordSign js * countableWordSign js) := by simp only [countableWordSign]; ring
        _ = 1 := by rw [countableSign_sq, ih, one_mul]

theorem countableWord_image (v : ℕ → CountableOrbital) (js : List ℕ) (hj : js.Nodup) :
    countableWord v js =
      countableWordSign js • countableOccupationImage v js.toFinset := by
  induction js with
  | nil => simp [countableWordSign, countableWord_nil, countableOccupationImage_empty]
  | cons j js ih =>
      rw [List.nodup_cons] at hj
      rw [countableWord_cons, ih hj.2, map_smul,
        countableCreate_image_of_not_mem v j js.toFinset (by simpa using hj.1)]
      simp only [countableWordSign, List.toFinset_cons, smul_smul]
      rw [mul_comm]

theorem countableWord_ket (js : List ℕ) (hj : js.Nodup) :
    countableWord orbitalKet js = countableWordSign js • countableKet js.toFinset := by
  rw [countableWord_image _ js hj, countableOccupationImage_orbitalKet]

/-- A finite creation word acting on an arbitrary completed Fock vector. -/
def countableWordOperator (v : ℕ → CountableOrbital) :
    List ℕ → CountableSpace →L[ℂ] CountableSpace
  | [] => 1
  | j :: js => (countableCreate (v j)).comp (countableWordOperator v js)

theorem countableWordOperator_nil (v : ℕ → CountableOrbital) (x : CountableSpace) :
    countableWordOperator v [] x = x := rfl

theorem countableWordOperator_cons (v : ℕ → CountableOrbital) (j : ℕ) (js : List ℕ)
    (x : CountableSpace) :
    countableWordOperator v (j :: js) x =
      countableCreate (v j) (countableWordOperator v js x) := rfl

theorem countableWordOperator_vacuum (v : ℕ → CountableOrbital) (js : List ℕ) :
    countableWordOperator v js (countableKet ∅) = countableWord v js := by
  induction js with
  | nil => rfl
  | cons j js ih => rw [countableWordOperator_cons, ih, countableWord_cons]

theorem countableWordOperator_append (v : ℕ → CountableOrbital) (js ks : List ℕ) :
    countableWordOperator v (js ++ ks) =
      (countableWordOperator v js).comp (countableWordOperator v ks) := by
  induction js with
  | nil => rfl
  | cons j js ih =>
      simp only [List.cons_append, countableWordOperator, ih, ContinuousLinearMap.comp_assoc]

theorem countableWord_append (v : ℕ → CountableOrbital) (js ks : List ℕ) :
    countableWord v (js ++ ks) = countableWordOperator v js (countableWord v ks) := by
  rw [← countableWordOperator_vacuum, countableWordOperator_append]
  exact congrArg (countableWordOperator v js) (countableWordOperator_vacuum v ks)

theorem countableWordOperator_create (v : ℕ → CountableOrbital) (js : List ℕ)
    (w : CountableOrbital) (x : CountableSpace) :
    countableCreate w (countableWordOperator v js x) =
      (-1 : ℂ) ^ js.length • countableWordOperator v js (countableCreate w x) := by
  induction js with
  | nil => simp only [List.length_nil, pow_zero, one_smul, countableWordOperator_nil]
  | cons j js ih =>
      have h := congrArg (fun T : CountableSpace →L[ℂ] CountableSpace =>
        T (countableWordOperator v js x)) (countableCreate_anticommute w (v j))
      change countableCreate w (countableCreate (v j) _) =
        -(countableCreate (v j) (countableCreate w _)) at h
      rw [countableWordOperator_cons, h, ih, map_smul]
      simp only [List.length_cons, pow_succ, mul_neg_one, neg_smul, countableWordOperator_cons]

theorem countableWordOperator_map (v : ℕ → CountableOrbital) (f : ℕ → ℕ) (js : List ℕ) :
    countableWordOperator v (js.map f) = countableWordOperator (v ∘ f) js := by
  induction js with
  | nil => rfl
  | cons j js ih => simp only [List.map_cons, countableWordOperator, ih, Function.comp_apply]

theorem countableWord_map (v : ℕ → CountableOrbital) (f : ℕ → ℕ) (js : List ℕ) :
    countableWord v (js.map f) = countableWord (v ∘ f) js := by
  rw [← countableWordOperator_vacuum, countableWordOperator_map, countableWordOperator_vacuum]

end VortexGap.Fermion
