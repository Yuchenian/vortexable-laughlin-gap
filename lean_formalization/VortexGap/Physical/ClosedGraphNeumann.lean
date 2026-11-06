import VortexGap.Physical.PlaneVortexDomain
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open Filter
open scoped Topology ComplexOrder

/-- Sum the Neumann orbit in a closed linear graph. Both coordinates converge
in norm even when the bounded commutator B has arbitrarily large norm. -/
theorem closedGraph_neumann {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (G : Submodule ℂ (H × H)) (hG : IsClosed (G : Set (H × H)))
    (T B : H →L[ℂ] H) (ht : ‖T‖ < 1)
    (hstep : ∀ p ∈ G, (T p.1, T p.2 + B p.1) ∈ G)
    (p : H × H) (hp : p ∈ G) :
    ∃ q ∈ G, HasSum (fun n : ℕ => (fun u : H × H => (T u.1, T u.2 + B u.1))^[n] p) q ∧
      q.1 - T q.1 = p.1 := by
  let step := fun u : H × H => (T u.1, T u.2 + B u.1)
  let u (n : ℕ) := step^[n] p
  have hz (n : ℕ) : u (n+1) = step (u n) := Function.iterate_succ_apply' step n p
  let s := (1+‖T‖)/2
  have hts : ‖T‖ < s := by dsimp [s]; linarith
  have hs : s < 1 := by dsimp [s]; linarith
  have hs0 : 0 ≤ s := (norm_nonneg T).trans hts.le
  let a := 1 + ‖B‖/(s-‖T‖)
  have ha : 1 ≤ a := by dsimp [a]; linarith [div_nonneg (norm_nonneg B) (sub_nonneg.mpr hts.le)]
  have hscale : ‖T‖*a + ‖B‖ ≤ a*s := by
    have hh : (s-‖T‖)*a = s-‖T‖+‖B‖ := by dsimp [a]; field_simp [(sub_pos.mpr hts).ne']
    nlinarith
  let d := ‖p.1‖ + ‖p.2‖
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have h (n : ℕ) : ‖(u n).1‖ ≤ s^n*d ∧ ‖(u n).2‖ ≤ a*(s^n*d) := by
    induction n with
    | zero =>
      change ‖p.1‖ ≤ s^0*d ∧ ‖p.2‖ ≤ a*(s^0*d)
      simp only [pow_zero, one_mul]
      exact ⟨le_add_of_nonneg_right (norm_nonneg _),
        (le_add_of_nonneg_left (norm_nonneg _)).trans (le_mul_of_one_le_left hd ha)⟩
    | succ n ih =>
      rw [hz]
      constructor
      · change ‖T (u n).1‖ ≤ _
        calc
          _ ≤ ‖T‖*‖(u n).1‖ := T.le_opNorm _
          _ ≤ s*(s^n*d) := mul_le_mul hts.le ih.1 (norm_nonneg _) hs0
          _ = _ := by ring
      · change ‖T (u n).2 + B (u n).1‖ ≤ _
        calc
          _ ≤ ‖T‖*‖(u n).2‖ + ‖B‖*‖(u n).1‖ :=
            (norm_add_le _ _).trans (add_le_add (T.le_opNorm _) (B.le_opNorm _))
          _ ≤ ‖T‖*(a*(s^n*d)) + ‖B‖*(s^n*d) := by gcongr <;> first | exact ih.2 | exact ih.1
          _ = (‖T‖*a+‖B‖)*(s^n*d) := by ring
          _ ≤ (a*s)*(s^n*d) := mul_le_mul_of_nonneg_right hscale (mul_nonneg (pow_nonneg hs0 _) hd)
          _ = _ := by ring
  have hgeo := (summable_geometric_of_lt_one hs0 hs).mul_right d
  have h1 : Summable (fun n => (u n).1) := Summable.of_norm_bounded hgeo fun n => (h n).1
  have h2 : Summable (fun n => (u n).2) := Summable.of_norm_bounded (hgeo.mul_left a) fun n => (h n).2
  have hu (n : ℕ) : u n ∈ G := by
    induction n with
    | zero => exact hp
    | succ n ih => rw [hz]; exact hstep _ ih
  let q := (∑' n, (u n).1, ∑' n, (u n).2)
  have hq : HasSum u q := h1.hasSum.prodMk h2.hasSum
  refine ⟨q, hG.mem_of_tendsto hq (Eventually.of_forall fun t => G.sum_mem fun n _ => hu n), hq, ?_⟩
  change (∑' n, (u n).1) - T (∑' n, (u n).1) = p.1
  rw [T.map_tsum h1]
  have he (n : ℕ) : T (u n).1 = (u (n+1)).1 := by rw [hz]
  simp_rw [he]
  rw [sub_eq_iff_eq_add, h1.tsum_eq_zero_add]
  rfl

/-- A positive invertible Gram admits a scalar Neumann rescaling. -/
theorem strictPositive_neumann_scale {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : H →L[ℂ] H) (hA : IsStrictlyPositive A) :
    ∃ a : ℝ, 0 < a ∧ ‖1 - (a : ℂ) • A‖ < 1 := by
  rcases subsingleton_or_nontrivial H with h | h
  · refine ⟨1, one_pos, ?_⟩
    rw [Subsingleton.elim (1 - ((1 : ℝ) : ℂ) • A) 0, norm_zero]
    exact zero_lt_one

  let E := H →L[ℂ] H
  obtain ⟨g, hg, hl⟩ : ∃ g > 0, algebraMap ℝ E g ≤ A :=
    (CFC.exists_pos_algebraMap_le_iff A).2 fun x hx => hA.spectrum_pos hx
  let c := max g ‖A‖ + 1
  have hc : 0 < c := by dsimp [c]; linarith [le_max_left g ‖A‖]
  have hgc : g ≤ c := by dsimp [c]; linarith [le_max_left g ‖A‖]
  have hhi : A ≤ c • (1 : H →L[ℂ] H) := by
    have h := IsSelfAdjoint.le_algebraMap_norm_self A (IsSelfAdjoint.of_nonneg hA.nonneg)
    rw [Algebra.algebraMap_eq_smul_one] at h
    exact h.trans (smul_le_smul_of_nonneg_right (by dsimp [c]; linarith [le_max_right g ‖A‖]) zero_le_one)
  have hl' : g • (1 : H →L[ℂ] H) ≤ A := by simpa only [Algebra.algebraMap_eq_smul_one] using hl
  have hu := smul_le_smul_of_nonneg_left hhi (inv_nonneg.mpr hc.le)
  have hpos : 0 ≤ 1-c⁻¹ • A := sub_nonneg.mpr (by simpa [smul_smul, hc.ne'] using hu)
  have hlo := smul_le_smul_of_nonneg_left hl' (inv_nonneg.mpr hc.le)
  have hbound : ‖1-c⁻¹ • A‖ ≤ 1-g/c := by
    apply (CStarAlgebra.norm_le_iff_le_algebraMap _ (sub_nonneg.mpr ((div_le_one hc).mpr hgc)) hpos).mpr
    rw [Algebra.algebraMap_eq_smul_one, sub_smul, one_smul]
    apply sub_le_sub_left
    simpa only [smul_smul, div_eq_inv_mul] using hlo
  refine ⟨c⁻¹, inv_pos.mpr hc, ?_⟩
  rw [Complex.coe_smul]
  exact hbound.trans_lt (sub_lt_self _ (div_pos hg hc))

/-- Inverse-domain implication obtained by summing inside the actual closed graph. -/
theorem closedGraph_strictPositive_preimage {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (G : Submodule ℂ (H × H))
    (hG : IsClosed (G : Set (H × H))) (A B : H →L[ℂ] H) (hA : IsStrictlyPositive A)
    (hstep : ∀ p ∈ G, (A p.1, A p.2 + B p.1) ∈ G) (v b : H) (hp : (A v,b) ∈ G) :
    ∃ y, (v,y) ∈ G := by
  obtain ⟨a,ha,ht⟩ := strictPositive_neumann_scale A hA
  let T := 1 - (a : ℂ) • A
  let D := -((a : ℂ) • B)
  have step (p : H × H) (h : p ∈ G) : (T p.1, T p.2 + D p.1) ∈ G := by
    have hh := G.sub_mem h (G.smul_mem (a : ℂ) (hstep p h))
    convert hh using 1
    ext <;> simp [T,D,smul_add] <;> abel
  obtain ⟨q,hq,_,he⟩ := closedGraph_neumann G hG T D ht step ((a : ℂ) • (A v,b)) (G.smul_mem _ hp)
  have eq : (a : ℂ) • A q.1 = (a : ℂ) • A v := by
    simpa [T] using he
  have hh : A q.1 = A v := (smul_right_injective _ (Complex.ofReal_ne_zero.mpr ha.ne')) eq
  have hinv := congrArg (fun u : H => (Ring.inverse A : H →L[ℂ] H) u) hh
  have hi (u : H) : (Ring.inverse A : H →L[ℂ] H) (A u) = u :=
    congrArg (fun L : H →L[ℂ] H => L u) (Ring.inverse_mul_cancel A hA.isUnit)
  rw [hi, hi] at hinv
  exact ⟨q.2, hinv ▸ hq⟩

end VortexGap.Fermion
