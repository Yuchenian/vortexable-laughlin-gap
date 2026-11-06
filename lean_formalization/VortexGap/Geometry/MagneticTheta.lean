import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

noncomputable section

namespace VortexGap.MagneticBloch
open Complex MeasureTheory
open scoped Real

def harmonic (n : ℤ) (z : ℂ) := Complex.exp (-(n:ℂ)*(2*Real.pi*I)*z)
def coefficient (f : ℂ → ℂ) (n : ℤ) := ∫ x : ℝ in 0..1, harmonic n (x:ℂ)*f x

private theorem harmonic_one (n : ℤ) (z : ℂ) : harmonic n (z+1) = harmonic n z := by
  unfold harmonic
  rw [mul_add, Complex.exp_add,mul_one,← Int.cast_neg,Complex.exp_int_mul_two_pi_mul_I,mul_one]

private theorem horizontal (h : ℂ → ℂ) (hd : Differentiable ℂ h) (hp : ∀ z, h (z+1)=h z) (y : ℝ) :
    (∫ x : ℝ in 0..1,h x) = ∫ x : ℝ in 0..1,h ((x:ℂ)+(y:ℂ)*I) := by
  have hh := Complex.integral_boundary_rect_eq_zero_of_differentiableOn h 0 (⟨1,y⟩ : ℂ) hd.differentiableOn
  simp only [zero_re,zero_im,ofReal_zero,zero_mul,add_zero,zero_add,ofReal_one] at hh
  simp_rw [add_comm (1:ℂ), hp] at hh
  linear_combination hh

/-- Fourier recurrence for a degree-one entire theta section in a periodic horizontal gauge. -/
theorem coefficient_recurrence (f : ℂ → ℂ) (hd : Differentiable ℂ f)
    (hp : ∀ z, f (z+1)=f z) (B : ℂ) (hv : ∀ z, f (z+I) = B*harmonic 1 z * f z) (n : ℤ) :
    coefficient f n = (Complex.exp (2*(Real.pi:ℂ)*n)*B) * coefficient f (n+1) := by
  let h := fun z => harmonic n z * f z
  have hc : Differentiable ℂ h := by unfold h harmonic; fun_prop
  have hor := horizontal h hc (fun z => by simp only [h,harmonic_one,hp]) 1
  change (∫ x : ℝ in 0..1, h x) = _
  rw [hor]
  have hpoint (x : ℝ) : h ((x:ℂ)+(1:ℝ)*I) =
      (Complex.exp (2*(Real.pi:ℂ)*n)*B) * (harmonic (n+1) (x:ℂ)*f x) := by
    simp only [h,ofReal_one,one_mul,hv,harmonic,Int.cast_add,Int.cast_one]
    have e1 : -(n:ℂ)*(2*Real.pi*I)*((x:ℂ)+I) =
        2*(Real.pi:ℂ)*n + (-(n:ℂ)*(2*Real.pi*I)*x) := by
      linear_combination -(2*(Real.pi:ℂ)*n)*Complex.I_sq
    rw [e1,Complex.exp_add]
    have e2 : -((n:ℂ)+1)*(2*Real.pi*I)*x = -(n:ℂ)*(2*Real.pi*I)*x + -(1:ℂ)*(2*Real.pi*I)*x := by ring
    rw [e2,Complex.exp_add]; ring
  simp_rw [hpoint]
  exact intervalIntegral.integral_const_mul _ _

private theorem harmonic_fourier (f : ℂ → ℂ) (n : ℤ) :
    fourierCoeffOn (by norm_num : (0:ℝ)<1) (fun x : ℝ => f x) n = coefficient f n := by
  rw [fourierCoeffOn_eq_integral]
  simp only [sub_zero,div_one,one_smul]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  simp only [smul_eq_mul, fourier_coe_apply, harmonic, Int.cast_neg, ofReal_sub, ofReal_one, ofReal_zero, sub_zero, div_one]
  congr 2
  ring

theorem coefficient_zero_unique (f : ℂ → ℂ) (hd : Differentiable ℂ f) (hp : ∀ z, f (z+1)=f z)
    (B : ℂ) (hB : B ≠ 0) (hv : ∀ z, f (z+I)=B*harmonic 1 z*f z) (hzero : coefficient f 0 = 0) :
    f = 0 := by
  have hrec := coefficient_recurrence f hd hp B hv
  have iffstep (n : ℤ) : coefficient f n = 0 ↔ coefficient f (n+1)=0 := by
    rw [hrec n,mul_eq_zero]
    simp [Complex.exp_ne_zero,hB]
  have hcoeff (n : ℤ) : coefficient f n = 0 := by
    induction n using Int.induction_on with
    | zero => exact hzero
    | succ n ih => exact (iffstep _).mp ih
    | pred n ih => apply (iffstep _).mpr; simpa using ih
  let u := fun x : ℝ => f (x:ℂ)
  have hc : Continuous u := hd.continuous.comp Complex.continuous_ofReal
  have hi := (hc.norm.pow 2).intervalIntegrable (μ := volume) 0 1
  have hsq : MemLp u 2 (volume.restrict (Set.Ioc 0 1)) :=
    (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr hi.1
  have hparse := tsum_sq_fourierCoeffOn (by norm_num : (0:ℝ)<1) hsq
  simp only [u,harmonic_fourier,hcoeff,norm_zero,zero_pow (by decide : 2≠0),tsum_zero,
    sub_zero,inv_one,one_smul] at hparse
  have hae := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae (by norm_num : (0:ℝ)≤1)
    (Filter.Eventually.of_forall (fun x => sq_nonneg ‖u x‖)) hi).mp hparse.symm
  have heq := Measure.eqOn_Ioc_of_ae_eq volume hae (hc.norm.pow 2).continuousOn continuous_zero.continuousOn
  let seq := fun n : ℕ => ((1/((n:ℝ)+1):ℝ):ℂ)
  have hseq : Filter.Tendsto seq Filter.atTop (nhdsWithin (0:ℂ) {0}ᶜ) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [seq,Function.comp_def,Complex.ofReal_zero] using (Complex.continuous_ofReal.tendsto 0).comp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
    · apply Filter.Eventually.of_forall
      intro n; exact Complex.ofReal_ne_zero.mpr (by positivity)
  apply AnalyticOnNhd.eq_of_frequently_eq (fun z _ => hd.analyticAt z) (fun _ _ => analyticAt_const)
  apply hseq.frequently (Filter.Frequently.of_forall ?_)
  intro n
  have hh := heq (x := (1/((n:ℝ)+1))) ⟨by positivity, (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α:=ℝ) n])⟩
  change ‖f (seq n)‖^2 = 0 at hh
  change f (seq n) = 0
  exact norm_eq_zero.mp (by nlinarith)

def sections (A B : ℂ) : Submodule ℂ (ℂ → ℂ) where
  carrier := {f | Differentiable ℂ f ∧ (∀ z, f (z+1)=A*f z) ∧ (∀ z, f (z+I)=B*harmonic 1 z*f z)}
  zero_mem' := by simp
  add_mem' := by
    rintro f g ⟨hf,hx,hy⟩ ⟨hg,gx,gy⟩
    exact ⟨hf.add hg,fun z => by simp [hx,gx,mul_add],fun z => by simp [hy,gy,mul_add]⟩
  smul_mem' := by
    rintro c f ⟨hf,hx,hy⟩
    exact ⟨hf.const_smul c,fun z => by simp [hx,smul_eq_mul,mul_left_comm],
      fun z => by simp [hy,smul_eq_mul,mul_left_comm]⟩

private theorem theta_nonzero : jacobiTheta₂ 0 I ≠ 0 := by
  have hs := Complex.hasSum_re (hasSum_jacobiTheta₂_term 0 (by simp : 0 < I.im))
  have term (n : ℤ) : (jacobiTheta₂_term n 0 I).re = Real.exp (-Real.pi*(n:ℝ)^2) := by
    unfold jacobiTheta₂_term
    rw [show 2*↑Real.pi*I*↑n*0+↑Real.pi*I*↑n^2*I = ((-Real.pi*(n:ℝ)^2 : ℝ):ℂ) by
      push_cast; linear_combination (Real.pi:ℂ)*(n:ℂ)^2*Complex.I_sq,← Complex.ofReal_exp,ofReal_re]
  have h := sum_le_hasSum ({0}:Finset ℤ) (fun n _ => (term n).symm ▸ (Real.exp_pos _).le) hs
  rw [Finset.sum_singleton,term] at h
  intro hz; rw [hz] at h; norm_num at h

private theorem coefficientLinear_sub (f g : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (c : ℂ) :
    coefficient (fun z => f z-c*g z) 0 = coefficient f 0-c*coefficient g 0 := by
  have hi (v : ℂ → ℂ) (hv : Differentiable ℂ v) :
      IntervalIntegrable (fun x : ℝ => v x) volume 0 1 :=
    (hv.continuous.comp continuous_ofReal).intervalIntegrable _ _
  simp only [coefficient,harmonic,Int.cast_zero,neg_zero,zero_mul,Complex.exp_zero,one_mul]
  rw [intervalIntegral.integral_sub (hi f hf) ((hi g hg).const_mul c),intervalIntegral.integral_const_mul]

private theorem generator (B : ℂ) (hB : B ≠ 0) : ∃ v : sections 1 B, v ≠ 0 := by
  let d := (Complex.log B - Real.pi)/(-(2*(Real.pi:ℂ)*I))
  let g := fun z => jacobiTheta₂ (z+d) I
  have hg : Differentiable ℂ g :=
    (fun z => (differentiableAt_jacobiTheta₂_fst (z+d) (by simp : 0 < I.im)).comp z
      (differentiableAt_id.add_const d))
  have he z : -(Real.pi:ℂ)*I*(I+2*(z+d)) = Complex.log B + -(1:ℂ)*(2*Real.pi*I)*z := by
    have hn : 2*(Real.pi:ℂ)*I ≠ 0 := by exact mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
    have hh : -(2*(Real.pi:ℂ)*I)*d = Complex.log B-Real.pi := by dsimp [d]; field_simp
    linear_combination hh - (Real.pi:ℂ)*Complex.I_sq
  have hmem : g ∈ sections 1 B := by
    refine ⟨hg,fun z => ?_,fun z => ?_⟩
    · simp only [g,show z+1+d=z+d+1 by ring,jacobiTheta₂_add_left,one_mul]
    · simp only [g,show z+I+d=z+d+I by ring,jacobiTheta₂_add_left',he,Complex.exp_add,Complex.exp_log hB,
        harmonic,Int.cast_one]
  refine ⟨⟨g,hmem⟩,?_⟩
  intro hz
  have h := congrArg (fun v : sections 1 B => v.val (-d)) hz
  change jacobiTheta₂ (-d+d) I = 0 at h
  exact theta_nonzero (by simpa using h)

theorem periodicGauge_rank_one (B : ℂ) (hB : B ≠ 0) : Module.finrank ℂ (sections 1 B) = 1 := by
  obtain ⟨v,hv⟩ := generator B hB
  obtain ⟨vd,vx,vy⟩ := v.property
  have vp z : v.val (z+1) = v.val z := by simpa using vx z
  have hcv : coefficient v.val 0 ≠ 0 := fun h => hv (Subtype.ext (coefficient_zero_unique v.val vd vp B hB vy h))
  apply finrank_eq_one v hv
  intro w
  obtain ⟨wd,wx,wy⟩ := w.property
  let c := coefficient w.val 0 / coefficient v.val 0
  refine ⟨c,?_⟩
  let u := w - c • v
  obtain ⟨ud,ux,uy⟩ := u.property
  have he : coefficient u.val 0 = 0 := by
    change coefficient (fun z => w.val z - c*v.val z) 0 = 0
    rw [coefficientLinear_sub _ _ wd vd]; dsimp [c]; field_simp; ring
  have hu := coefficient_zero_unique u.val ud (fun z => by simpa using ux z) B hB uy he
  have hz : w-c • v = 0 := Subtype.ext hu
  exact (sub_eq_zero.mp hz).symm

private def twist (a : ℂ) (f : ℂ → ℂ) (z : ℂ) := Complex.exp (a*z)*f z

private theorem twist_mem (a A B : ℂ) {f : ℂ → ℂ} (hf : f ∈ sections A B) :
    twist a f ∈ sections (Complex.exp a*A) (Complex.exp (a*I)*B) := by
  obtain ⟨hd,hx,hy⟩ := hf
  refine ⟨by unfold twist; fun_prop,fun z => ?_,fun z => ?_⟩
  · simp only [twist,mul_add,mul_one,Complex.exp_add,hx]; ring
  · simp only [twist,mul_add,Complex.exp_add,hy]; ring

private def gaugeEquiv (A B : ℂ) (hA : A ≠ 0) :
    sections 1 (Complex.exp (-(Complex.log A)*I)*B) ≃ₗ[ℂ] sections A B where
  toFun f := ⟨twist (Complex.log A) f.val, by
    simpa only [Complex.exp_log hA,mul_one,neg_mul,Complex.exp_neg,
      ← mul_assoc,mul_inv_cancel₀ (Complex.exp_ne_zero _),one_mul] using twist_mem (Complex.log A) _ _ f.property⟩
  invFun f := ⟨twist (-(Complex.log A)) f.val, by
    simpa only [Complex.exp_neg,Complex.exp_log hA,inv_mul_cancel₀ hA] using twist_mem (-(Complex.log A)) _ _ f.property⟩
  left_inv f := by ext z; simp [twist,neg_mul,Complex.exp_neg,← mul_assoc]
  right_inv f := by ext z; simp [twist,neg_mul,Complex.exp_neg,← mul_assoc]
  map_add' f g := by ext z; simp [twist,mul_add]
  map_smul' c f := by ext z; simp [twist,smul_eq_mul,mul_left_comm]

/-- Every pair of nonzero boundary multipliers has one holomorphic section up to scale. -/
theorem theta_rank_one (A B : ℂ) (hA : A ≠ 0) (hB : B ≠ 0) :
    Module.finrank ℂ (sections A B) = 1 :=
  (gaugeEquiv A B hA).finrank_eq.symm.trans (periodicGauge_rank_one _
    (mul_ne_zero (Complex.exp_ne_zero _) hB))

end VortexGap.MagneticBloch
