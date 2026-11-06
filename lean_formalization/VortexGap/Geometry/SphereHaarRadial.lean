import VortexGap.Geometry.SphereTraceNorm
import OAI.Analysis.Laughlin.Spin.HaarOrthogonality
import Mathlib.Topology.ContinuousMap.Weierstrass
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open OAI.Laughlin.Rotation MeasureTheory
open scoped Matrix ComplexConjugate

/-- Moments of the squared spinor coordinate under normalized Haar measure. -/
theorem sphereHaar_radial_moment (q : ℕ) :
    (∫ g : SourceSU2, (‖g.val 0 0‖^2)^q ∂sourceHaar) = 1/((q:ℝ)+1) := by
  let P : Matrix (Fin (q+1)) (Fin (q+1)) ℂ := Matrix.single 0 0 1
  have hp : P.trace = 1 := by simp [P, Matrix.trace, Matrix.diag, Matrix.single]
  have hs := congrFun (congrFun (source_spin_haar_schur q P) 0) 0
  have hentry (g : SourceSU2) : conjugateOrbit (sourceSpinRepresentation q) P g 0 0 =
      (((‖g.val 0 0‖^2)^q : ℝ):ℂ) := by
    rw [conjugateOrbit, sourceSpinRepresentation_inv, Matrix.mul_apply]
    rw [Finset.sum_eq_single 0]
    · rw [Matrix.mul_single_apply_same, Matrix.conjTranspose_apply]
      have h0 : sourceSpinRepresentation q g 0 0 = g.val 0 0 ^ q := by
        simpa using sphereSpinBlock_first_row q g 0
      simp only [h0, mul_one, Complex.star_def]
      rw [Complex.mul_conj, Complex.sq_norm, map_pow, Complex.ofReal_pow]
    · intro b _ hb
      simp [P, hb]
    · simp
  change (∫ g : SourceSU2, conjugateOrbit (sourceSpinRepresentation q) P g 0 0 ∂sourceHaar) = _ at hs
  simp_rw [hentry] at hs
  rw [integral_complex_ofReal (f := fun g : SourceSU2 => (‖g.val 0 0‖^2)^q), hp] at hs
  apply Complex.ofReal_injective
  simpa using hs

theorem sphereHaar_radial_polynomial (p : Polynomial ℝ) :
    (∫ g : SourceSU2, p.eval (‖g.val 0 0‖^2) ∂sourceHaar) =
      ∫ x in (0:ℝ)..1, p.eval x := by
  have he : Continuous (fun g : SourceSU2 => g.val 0 0) :=
    (continuous_apply 0).comp ((continuous_apply 0).comp continuous_subtype_val)
  have hc (i : ℕ) : Continuous (fun g : SourceSU2 => p.coeff i * (‖g.val 0 0‖^2)^i) := continuous_const.mul ((he.norm.pow 2).pow i)
  simp only [Polynomial.eval_eq_sum_range]
  rw [integral_finsetSum _ (fun i _ => (hc i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
    intervalIntegral.integral_finsetSum (fun i _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul, intervalIntegral.integral_const_mul, sphereHaar_radial_moment, integral_pow]
  simp

/-- Integration against the squared spinor coordinate is uniform integration on [0,1]. -/
theorem sphereHaar_radial_continuous (F : ℝ → ℝ) (hF : Continuous F) :
    (∫ g : SourceSU2, F (‖g.val 0 0‖^2) ∂sourceHaar) = ∫ x in (0:ℝ)..1, F x := by
  let u := fun g : SourceSU2 => ‖g.val 0 0‖^2
  have he : Continuous (fun g : SourceSU2 => g.val 0 0) :=
    (continuous_apply 0).comp ((continuous_apply 0).comp continuous_subtype_val)
  have hu : Continuous u := he.norm.pow 2
  have hr (g : SourceSU2) : u g ∈ Set.Icc 0 1 := by
    have ht := unitary_entry_norm_le_one g.val g.property.1 0 0
    exact ⟨sq_nonneg _, by dsimp [u]; nlinarith [norm_nonneg (g.val 0 0)]⟩
  by_contra h
  let A := ∫ g, F (u g) ∂sourceHaar
  let B := ∫ x in (0:ℝ)..1, F x
  have hpos : 0 < |A-B|/3 := by
    exact div_pos (abs_pos.mpr (sub_ne_zero.mpr h)) (by norm_num)
  obtain ⟨p,hp⟩ := exists_polynomial_near_of_continuousOn 0 1 F hF.continuousOn _ hpos
  have hL := norm_integral_le_of_norm_le_const (μ := sourceHaar)
    (f := fun g => p.eval (u g) - F (u g))
    (Filter.Eventually.of_forall (fun g => (hp _ (hr g)).le))
  have hR := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
    (f := fun x => p.eval x - F x) (C := |A-B|/3) (fun x hx => by
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
      exact (hp x ⟨hx.1.le,hx.2⟩).le)
  rw [integral_sub (μ := sourceHaar) (f := fun x => p.eval (u x)) (g := fun x => F (u x)) ((p.continuous.comp hu).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((hF.comp hu).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))] at hL
  rw [intervalIntegral.integral_sub (p.continuous.intervalIntegrable _ _) (hF.intervalIntegrable _ _)] at hR
  let P := ∫ x in (0:ℝ)..1, p.eval x
  have hl : |P-A| ≤ |A-B|/3 := by
    simpa [P,A, u, sphereHaar_radial_polynomial, Real.norm_eq_abs] using hL
  have hh : |P-B| ≤ |A-B|/3 := by simpa [P,B, Real.norm_eq_abs] using hR
  have ht := abs_sub_le A P B
  rw [abs_sub_comm A P] at ht
  linarith

theorem sphereHaar_relative_radius (g : SourceSU2) (F : ℝ → ℝ) (hF : Continuous F) :
    (∫ h : SourceSU2, F ‖(g⁻¹*h).val 0 0‖ ∂sourceHaar) =
      ∫ t in (0:ℝ)..1, F t * (2*t) := by
  rw [integral_mul_left_eq_self (fun h : SourceSU2 => F ‖h.val 0 0‖) g⁻¹]
  have hx := sphereHaar_radial_continuous (fun x => F (Real.sqrt x)) (hF.comp Real.continuous_sqrt)
  simp only [Real.sqrt_sq (norm_nonneg _)] at hx
  rw [hx]
  have hd (t : ℝ) : HasDerivAt (fun x : ℝ => x^2) (2*t) t := by
    simpa using hasDerivAt_pow 2 t
  have hs := intervalIntegral.integral_comp_mul_deriv (a := (0:ℝ)) (b := 1)
    (fun t _ => hd t) (by fun_prop) (hF.comp Real.continuous_sqrt)
  simp only [zero_pow (by decide : 2 ≠ 0), one_pow, Function.comp_apply] at hs
  rw [← hs]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
  simp [Function.comp_apply, Real.sqrt_sq ht.1]

open VortexGap.Frame

/-- The scaled physical row integral at flux n+1 equals the radial Schur constant. -/
theorem sphereSpinFrame_schur_row (n : ℕ) (g : SourceSU2) :
    (2*(n:ℝ)+1) * (∫ h : SourceSU2,
      traceNormTwo (twoFrameOverlap (sphereSpinFrame n g) (sphereSpinFrame n h)) ∂sourceHaar) =
        sphereRadialSchur n := by
  cases n with
  | zero => simp [sphereSpinFrame_flux_one_traceNorm, sphereRadialSchur_flux_one]
  | succ n =>
    let F := fun t : ℝ => t^n * Real.sqrt (4*t^2+((n:ℝ)+1)^2*(1-t^2)^2)
    have he (h : SourceSU2) : traceNormTwo (twoFrameOverlap (sphereSpinFrame (n+1) g)
        (sphereSpinFrame (n+1) h)) = F ‖(g⁻¹*h).val 0 0‖ := sphereSpinFrame_traceNorm n g h
    simp_rw [he]
    rw [sphereHaar_relative_radius g F (by dsimp [F]; fun_prop), sphereRadialSchur]
    have hfun (t : ℝ) : F t * (2*t) =
        2*(t^(n+1)*Real.sqrt (4*t^2+((n:ℝ)+1)^2*(1-t^2)^2)) := by dsimp [F]; rw [pow_succ]; ring
    simp_rw [hfun]
    rw [intervalIntegral.integral_const_mul]
    push_cast
    ring

theorem sphereSpinFrame_schur_lt (n : ℕ) (g : SourceSU2) :
    (2*(n:ℝ)+1) * (∫ h : SourceSU2,
      traceNormTwo (twoFrameOverlap (sphereSpinFrame n g) (sphereSpinFrame n h)) ∂sourceHaar) <
      8*Real.sqrt 3 := by rw [sphereSpinFrame_schur_row]; exact sphereRadialSchur_lt n

end VortexGap.Fermion
