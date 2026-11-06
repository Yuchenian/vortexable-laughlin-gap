import VortexGap.Fermion.CountablePairCompression
import VortexGap.Fermion.CountableFockPullback
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct ComplexOrder

/-- Vacuum compression of the one-particle loss dilation on Fock space. -/
def countableFockCompression (M : CountableOrbital →L[ℂ] CountableOrbital)
    (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) : CountableSpace →L[ℂ] CountableSpace :=
  (countableFockIsometry countableSysOrbital).toContinuousLinearMap.adjoint.comp
    (countableFockIsometry (countableLossEmbedding M hM hc)).toContinuousLinearMap

theorem countableFockCompression_vacuum (M : CountableOrbital →L[ℂ] CountableOrbital)
    (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) :
    countableFockCompression M hM hc (countableKet ∅) = countableKet ∅ := by
  change (countableFockIsometry countableSysOrbital).toContinuousLinearMap.adjoint (countableFockIsometry (countableLossEmbedding M hM hc) (countableKet ∅)) = _
  rw [countableFockIsometry_vacuum]
  have h := congrArg (fun T : CountableSpace →L[ℂ] CountableSpace => T (countableKet ∅))
    (countableFockIsometry_adjoint_self countableSysOrbital)
  change (countableFockIsometry countableSysOrbital).toContinuousLinearMap.adjoint
    (countableFockIsometry countableSysOrbital (countableKet ∅)) = countableKet ∅ at h
  rwa [countableFockIsometry_vacuum] at h

theorem countableFockCompression_create (M : CountableOrbital →L[ℂ] CountableOrbital)
    (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) (v : CountableOrbital) (x : CountableSpace) :
    countableFockCompression M hM hc (countableCreate v x) =
      countableCreate (M v) (countableFockCompression M hM hc x) := by
  let J := countableLossEmbedding M hM hc
  let K := countableSysOrbital
  have h := congrArg (fun T : CountableSpace →L[ℂ] CountableSpace => T.adjoint)
    (countableFock_annihilate_pullback_map K (J v))
  simp only [ContinuousLinearMap.adjoint_comp, countableAnnihilate_adjoint] at h
  change (countableFockIsometry K).toContinuousLinearMap.adjoint
    (countableFockIsometry J (countableCreate v x)) = _
  rw [countableFockIsometry_create]
  have he := congrArg (fun T : CountableSpace →L[ℂ] CountableSpace => T (countableFockIsometry J x)) h
  simp only [ContinuousLinearMap.comp_apply] at he
  simpa only [J, K, countableFockCompression, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap, countableSysOrbital_adjoint_loss] using he

theorem countableFockCompression_word (M : CountableOrbital →L[ℂ] CountableOrbital)
    (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) (v : ℕ → CountableOrbital) (js : List ℕ) :
    countableFockCompression M hM hc (countableWord v js) =
      countableWord (fun j => M (v j)) js := by
  induction js with
  | nil => exact countableFockCompression_vacuum M hM hc
  | cons j js ih => rw [countableWord_cons, countableFockCompression_create, ih, countableWord_cons]
private theorem scaledOrbital_nonneg (M : CountableOrbital →L[ℂ] CountableOrbital)
    (hM : 0 ≤ M) : 0 ≤ (((1 + ‖M‖)⁻¹ : ℝ) : ℂ) • M :=
  ContinuousLinearMap.nonneg_iff_isPositive.mpr
    ((ContinuousLinearMap.nonneg_iff_isPositive.mp hM).smul_of_nonneg
      (Complex.zero_le_real.mpr (by positivity)))

private theorem scaledOrbital_contract (M : CountableOrbital →L[ℂ] CountableOrbital) :
    ‖(((1 + ‖M‖)⁻¹ : ℝ) : ℂ) • M‖ ≤ 1 := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (1 + ‖M‖)⁻¹),
    ← div_eq_inv_mul, div_le_one (by positivity)]
  linarith

/-- On degree N this bounded map is the Nth exterior power of M. The
factor depends on N, so this extension makes no uniform full-Fock bound. -/
def countableDegreeFilter (N : ℕ) (M : CountableOrbital →L[ℂ] CountableOrbital)
    (hM : 0 ≤ M) : CountableSpace →L[ℂ] CountableSpace :=
  (((1 + ‖M‖ : ℝ) : ℂ)^N) • countableFockCompression _ (scaledOrbital_nonneg M hM)
    (scaledOrbital_contract M)

private theorem scaledWord (z : ℂ) (v : ℕ → CountableOrbital) (js : List ℕ) :
    countableWord (fun j => z • v j) js = z ^ js.length • countableWord v js := by
  induction js with
  | nil => simp [countableWord]
  | cons j js ih =>
    simp only [countableWord_cons, ih, map_smul, smul_apply,
      smul_smul, List.length_cons, pow_succ]

theorem countableDegreeFilter_word (M : CountableOrbital →L[ℂ] CountableOrbital)
    (hM : 0 ≤ M) (v : ℕ → CountableOrbital) (js : List ℕ) :
    countableDegreeFilter js.length M hM (countableWord v js) =
      countableWord (fun j => M (v j)) js := by
  have hz : (1 + ‖M‖ : ℝ) ≠ 0 := ne_of_gt (by positivity)
  rw [countableDegreeFilter, smul_apply, countableFockCompression_word]
  simp only [smul_apply, scaledWord, smul_smul, ← mul_pow,
    Complex.ofReal_inv, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hz), one_pow, one_smul]

theorem countableDegreeFilter_cancel (N : ℕ) (S R : CountableOrbital →L[ℂ] CountableOrbital)
    (hS : 0 ≤ S) (hR : 0 ≤ R) (hinv : S * R = 1) (x : countableSector N) :
    countableDegreeFilter N S hS (countableDegreeFilter N R hR x) = x := by
  let T := (countableDegreeFilter N S hS).comp (countableDegreeFilter N R hR)
  have horb (u : CountableOrbital) : S (R u) = u :=
    congrArg (fun L : CountableOrbital →L[ℂ] CountableOrbital => L u) hinv
  have hk (A : Finset ℕ) (hc : A.card = N) : T (countableKet A) = countableKet A := by
    let js := A.sort (· ≤ ·)
    have hn : js.length = N := by simpa [js] using hc
    rw [← countableOccupationImage_orbitalKet A]
    change countableDegreeFilter N S hS (countableDegreeFilter N R hR
      (countableWord orbitalKet js)) = countableWord orbitalKet js
    rw [← hn, countableDegreeFilter_word, countableDegreeFilter_word]
    simp only [horb]
  have hs := (countableSpace_hasSum (x : CountableSpace)).map T.toAddMonoidHom T.continuous
  change HasSum (fun A => T ((x : CountableSpace) A • countableKet A)) (T x) at hs
  apply HasSum.unique _ (countableSpace_hasSum (x : CountableSpace))
  apply hs.congr
  intro s
  apply Finset.sum_congr rfl
  intro A _
  change T ((x : CountableSpace) A • countableKet A) = (x : CountableSpace) A • countableKet A
  by_cases hc : A.card = N
  · rw [map_smul, hk A hc]
  · rw [x.property A hc, zero_smul, map_zero]

theorem countableDegreeFilter_sector (N : ℕ) (M : CountableOrbital →L[ℂ] CountableOrbital)
    (hM : 0 ≤ M) (x : countableSector N) : countableDegreeFilter N M hM x ∈ countableSector N := by
  let T := countableDegreeFilter N M hM
  have hs := (countableSpace_hasSum (x : CountableSpace)).map T.toAddMonoidHom T.continuous
  apply (countableSector_isClosed N).mem_of_tendsto hs
  apply Filter.Eventually.of_forall
  intro s
  apply (countableSector N).sum_mem
  intro A _
  change T ((x : CountableSpace) A • countableKet A) ∈ countableSector N
  rw [map_smul]
  by_cases hc : A.card = N
  · apply (countableSector N).smul_mem
    let js := A.sort (· ≤ ·)
    have hn : js.length = N := by simpa [js] using hc
    rw [← countableOccupationImage_orbitalKet A]
    change countableDegreeFilter N M hM (countableWord orbitalKet js) ∈ countableSector N
    rw [← hn, countableDegreeFilter_word]
    exact countableWord_sector _ js
  · rw [x.property A hc, zero_smul]
    exact (countableSector N).zero_mem

theorem countableFockCompression_annihilate (M : CountableOrbital →L[ℂ] CountableOrbital)
    (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1) (v : CountableOrbital) (x : CountableSpace) :
    countableAnnihilate v (countableFockCompression M hM hc x) =
      countableFockCompression M hM hc (countableAnnihilate (M v) x) := by
  let T := countableFockCompression M hM hc
  have hw (js : List ℕ) : countableAnnihilate v (T (countableWord orbitalKet js)) =
      T (countableAnnihilate (M v) (countableWord orbitalKet js)) := by
    induction js with
    | nil => simp only [countableWord_nil, T, countableFockCompression_vacuum,
        countableAnnihilate_vacuum, map_zero]
    | cons j js ih =>
      change countableAnnihilate v (countableFockCompression M hM hc _) =
        countableFockCompression M hM hc _
      rw [countableWord_cons, countableFockCompression_create, countableAnnihilate_create,
        countableAnnihilate_create, map_sub, map_smul, countableFockCompression_create]
      have hi := (ContinuousLinearMap.nonneg_iff_isPositive.mp hM).isSymmetric v (orbitalKet j)
      change inner ℂ (M v) (orbitalKet j) = inner ℂ v (M (orbitalKet j)) at hi
      rw [hi]
      change _ - countableCreate _ (countableAnnihilate v (T _)) = _
      rw [ih]
  have he : (countableAnnihilate v).comp T = T.comp (countableAnnihilate (M v)) := by
    apply countableSpace_clm_ext
    intro A
    rw [← countableOccupationImage_orbitalKet A]
    exact hw _
  exact congrArg (fun L : CountableSpace →L[ℂ] CountableSpace => L x) he

theorem countableDegreeFilter_annihilate (N : ℕ) (M : CountableOrbital →L[ℂ] CountableOrbital)
    (hM : 0 ≤ M) (v : CountableOrbital) (x : CountableSpace) :
    countableAnnihilate v (countableDegreeFilter (N+1) M hM x) =
      countableDegreeFilter N M hM (countableAnnihilate (M v) x) := by
  have hz : (1 + ‖M‖ : ℝ) ≠ 0 := ne_of_gt (by positivity)
  simp only [countableDegreeFilter, smul_apply, map_smul, countableFockCompression_annihilate,
    countableAnnihilate_smul, map_inv₀, Complex.conj_ofReal, smul_smul, Complex.ofReal_inv, pow_succ]
  rw [mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hz), mul_one]

end VortexGap.Fermion
