import OAI.Analysis.Laughlin.Spin.Torus
import Mathlib.Tactic
import OAI.Analysis.Laughlin.Spin.Mixing

noncomputable section
namespace VortexGap.Fermion
open OAI.Laughlin.Rotation
open scoped Matrix ComplexConjugate

theorem spinor_phase_of_bloch_data {a b c d : ℂ}
    (hu : Complex.normSq a + Complex.normSq b = 1)
    (hv : Complex.normSq c + Complex.normSq d = 1)
    (hz : Complex.normSq a - Complex.normSq b = Complex.normSq c - Complex.normSq d)
    (hw : conj a*b = conj c*d) :
    ∃ z : ℂ, ‖z‖=1 ∧ c=a*z ∧ d=b*z := by
  have hac : ‖a‖ = ‖c‖ := by
    have h : Complex.normSq a = Complex.normSq c := by linarith
    simp only [Complex.normSq_eq_norm_sq] at h
    nlinarith [norm_nonneg a,norm_nonneg c]
  have hbd : ‖b‖ = ‖d‖ := by
    have h : Complex.normSq b = Complex.normSq d := by linarith
    simp only [Complex.normSq_eq_norm_sq] at h
    nlinarith [norm_nonneg b,norm_nonneg d]
  by_cases ha : a=0
  · subst a
    have hc : c=0 := norm_eq_zero.mp (by simpa using hac.symm)
    have hb : b ≠ 0 := by rintro rfl; norm_num at hu
    exact ⟨d/b,by rw [norm_div,← hbd,div_self (norm_ne_zero_iff.mpr hb)],by simp [hc],by field_simp⟩
  · let z := c/a
    have hn : ‖z‖=1 := by dsimp [z]; rw [norm_div,← hac,div_self (norm_ne_zero_iff.mpr ha)]
    have hc : c=a*z := by dsimp [z]; field_simp
    have hzz : z * conj z = 1 := by simpa [hn] using Complex.mul_conj' z
    refine ⟨z,hn,hc,?_⟩
    rw [hc,map_mul] at hw
    have he : b=conj z*d := mul_left_cancel₀ (show conj a ≠ 0 by simpa using ha)
      (by simpa [mul_assoc] using hw)
    rw [he]
    linear_combination -d*hzz

theorem rotation_eq_of_column (g h : SourceSU2) (hc : ∀ i, g.val i 0 = h.val i 0) : g=h := by
  let k := g⁻¹*h
  have col (i : Fin 2) : k.val i 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) i 0 := by
    change (g⁻¹.val * h.val) i 0 = _
    rw [Matrix.mul_apply]
    simp_rw [← hc]
    rw [← Matrix.mul_apply]
    exact congrArg (fun t : SourceSU2 => t.val i 0) (inv_mul_cancel g)
  have h00 : k.val 0 0 = 1 := by simpa using col 0
  have h10 : k.val 1 0 = 0 := by simpa using col 1
  have hd := (Matrix.mem_specialUnitaryGroup_iff.mp k.property).2
  have h11 : k.val 1 1 = 1 := by simpa [Matrix.det_fin_two,h00,h10] using hd
  have he := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp k.property.1) 0) 1
  have h01 : k.val 0 1 = 0 := by
    simpa [Matrix.mul_apply,Fin.sum_univ_two,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,h00,h10] using he
  have hk : k=1 := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00,h10,h11,h01]
  exact inv_mul_eq_one.mp hk

theorem spinor_rotation_phase (g h : SourceSU2)
    (hz : Complex.normSq (g.val 0 0) - Complex.normSq (g.val 1 0) =
          Complex.normSq (h.val 0 0) - Complex.normSq (h.val 1 0))
    (hw : 2 * conj (g.val 0 0) * g.val 1 0 = 2 * conj (h.val 0 0) * h.val 1 0) :
    ∃ z : ℂ, ∃ hn : ‖z‖=1, h=g*sourceTorus z hn := by
  have unit (k : SourceSU2) : Complex.normSq (k.val 0 0) + Complex.normSq (k.val 1 0) = 1 := by
    have he := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp k.property.1) 0) 0
    simpa [Matrix.mul_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,
      Complex.mul_conj,Fin.sum_univ_two,mul_comm] using congrArg Complex.re he
  obtain ⟨z,hn,h0,h1⟩ := spinor_phase_of_bloch_data (unit g) (unit h) hz (by linear_combination hw/2)
  refine ⟨z,hn,rotation_eq_of_column h _ ?_⟩
  intro i
  change h.val i 0 = (g.val * Matrix.diagonal (fun k : Fin 2 => if k=0 then z else star z)) i 0
  simp only [Matrix.mul_diagonal,ite_true]
  fin_cases i <;> assumption

end VortexGap.Fermion
end

noncomputable section
namespace VortexGap.Fermion
open OAI.Laughlin.Rotation
open scoped ComplexConjugate

/-- The phase of a nonzero spinor component, used on its coordinate chart. -/
def componentPhase (a : ℂ) : ℂ := a / (‖a‖ : ℂ)

theorem componentPhase_unit {a : ℂ} (ha : a ≠ 0) : ‖componentPhase a‖ = 1 := by
  simp [componentPhase, norm_ne_zero_iff.mpr ha]

theorem componentPhase_rotate (a z : ℂ) (hz : ‖z‖=1) :
    componentPhase (a*z) = componentPhase a*z := by
  simp [componentPhase,hz]; ring

def chartSpinor (k : Fin 2) (g : SourceSU2) (i : Fin 2) : ℂ :=
  g.val i 0 / componentPhase (g.val k 0)

theorem chartSpinor_selected (k : Fin 2) (g : SourceSU2) (hk : g.val k 0 ≠ 0) :
    chartSpinor k g k = (‖g.val k 0‖ : ℂ) := by
  simp [chartSpinor,componentPhase,hk]

theorem chartSpinor_rotate (k : Fin 2) (g : SourceSU2) (z : ℂ) (hz : ‖z‖=1) :
    chartSpinor k (g*sourceTorus z hz) = chartSpinor k g := by
  have he (i : Fin 2) : (g*sourceTorus z hz).val i 0 = g.val i 0*z := by
    change (g.val * Matrix.diagonal (fun j : Fin 2 => if j=0 then z else star z)) i 0 = _
    simp [Matrix.mul_diagonal]
  funext i
  simp only [chartSpinor,he,componentPhase_rotate _ _ hz]
  exact mul_div_mul_right _ _ (by intro h; simp [h] at hz)

theorem chartSpinor_continuous (k : Fin 2) :
    ContinuousOn (chartSpinor k) {g | g.val k 0 ≠ 0} := by
  have hc (i : Fin 2) : Continuous (fun g : SourceSU2 => g.val i 0) :=
    (continuous_apply 0).comp ((continuous_apply i).comp continuous_subtype_val)
  intro g hg
  apply ContinuousAt.continuousWithinAt
  apply continuousAt_pi.mpr
  intro i
  have hn : (‖g.val k 0‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hg
  exact (hc i).continuousAt.div ((hc k).continuousAt.div
    (Complex.continuous_ofReal.comp (hc k).norm).continuousAt hn) (div_ne_zero hg hn)

/-- On the overlap the two chart spinors differ by the same unit phase in both entries. -/
theorem chartSpinor_overlap (g : SourceSU2) (h0 : g.val 0 0 ≠ 0) (h1 : g.val 1 0 ≠ 0) :
    let t := componentPhase (g.val 0 0) / componentPhase (g.val 1 0)
    ‖t‖ = 1 ∧ ∀ i, chartSpinor 1 g i = chartSpinor 0 g i * t := by
  dsimp only
  constructor
  · simp [componentPhase_unit h0,componentPhase_unit h1]
  · intro i
    have hn : componentPhase (g.val 0 0) ≠ 0 := by
      intro h
      simpa [h] using componentPhase_unit h0
    unfold chartSpinor
    field_simp [hn]

theorem chartSpinor_mixer_phase (k i : Fin 2) :
    chartSpinor k (sourceMixer * sourceTorus Complex.I Complex.norm_I) i =
      (Real.sqrt (1/2) : ℂ) := by
  rw [chartSpinor_rotate]
  have he (j : Fin 2) : sourceMixer.val j 0 = (Real.sqrt (1/2) : ℂ) := by
    fin_cases j <;> rfl
  have hp : 0 < Real.sqrt (1/2) := Real.sqrt_pos.mpr (by norm_num)
  have hn : (Real.sqrt (1/2) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
  simp only [chartSpinor,he,componentPhase,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hp,div_self hn,div_one]

end VortexGap.Fermion
end
