import VortexGap.Examples.PeriodicPhysical
import VortexGap.Examples.PlaneNodalFourier
import VortexGap.Physical.PlaneMultiplication
import VortexGap.Geometry.PlaneFourierMode

noncomputable section

namespace VortexGap.Fermion
open MeasureTheory
open scoped ComplexConjugate BoundedContinuousFunction
local notation "Orb" => CountableOrbital →L[ℂ] CountableOrbital

def magneticTranslationFactor (ell : ℝ) (d w : ℂ) : ℂ :=
  ((Real.exp (-‖d‖^2/(4*ell^2)) : ℂ))⁻¹ * planeDisplacementFactor ell d w

theorem guidingDisplacement_on_evaluation (ell : ℝ) (hell : 0 < ell) (d w : ℂ) :
    planeGuidingDisplacement ell hell d (planeEvaluation ell w) =
      magneticTranslationFactor ell d w • planeEvaluation ell (w-d) := by
  change ((Real.exp (-‖d‖^2/(4*ell^2)) : ℂ))⁻¹ •
    (planeDisplacementCompression ell hell d (planeEvaluation ell w)) = _
  rw [planeDisplacementCompression_evaluation, smul_smul]
  rfl

def magneticCommutatorPhase (ell : ℝ) (d e : ℂ) :=
  Complex.exp (((2*ell^2 : ℝ):ℂ)⁻¹*(e*conj d - d*conj e))

private theorem phaseProduct (ell : ℝ) (d e w : ℂ) :
    magneticTranslationFactor ell e w * magneticTranslationFactor ell d (w-e) =
      magneticCommutatorPhase ell d e * (magneticTranslationFactor ell d w * magneticTranslationFactor ell e (w-d)) := by
  have h : planeDisplacementFactor ell e w * planeDisplacementFactor ell d (w-e) =
      magneticCommutatorPhase ell d e * (planeDisplacementFactor ell d w * planeDisplacementFactor ell e (w-d)) := by
    unfold planeDisplacementFactor magneticCommutatorPhase
    simp only [← Complex.exp_add]
    congr 1
    let a := ((2*ell^2 : ℝ):ℂ)⁻¹
    change a * _ / 2 + a * _ / 2 = a * _ + (a * _ / 2 + a * _ / 2)
    simp only [map_sub]
    ring
  unfold magneticTranslationFactor
  linear_combination (((Real.exp (-‖d‖^2/(4*ell^2)) : ℂ))⁻¹ *
    ((Real.exp (-‖e‖^2/(4*ell^2)) : ℂ))⁻¹) * h

theorem guidingDisplacement_commutator (ell : ℝ) (hell : 0 < ell) (d e : ℂ) :
    let D := fun z => (planeGuidingDisplacement ell hell z).toLinearIsometry.toContinuousLinearMap
    (D d).comp (D e) = magneticCommutatorPhase ell d e • ((D e).comp (D d)) := by
  let D := fun z => (planeGuidingDisplacement ell hell z).toLinearIsometry.toContinuousLinearMap
  let A := (D d).comp (D e)
  let B := magneticCommutatorPhase ell d e • ((D e).comp (D d))
  have he (z) : A (planeEvaluation ell z) = B (planeEvaluation ell z) := by
    change planeGuidingDisplacement ell hell d (planeGuidingDisplacement ell hell e _) =
      magneticCommutatorPhase ell d e • planeGuidingDisplacement ell hell e (planeGuidingDisplacement ell hell d _)
    simp only [guidingDisplacement_on_evaluation,map_smul,smul_smul,
      show z-e-d = z-d-e by ring]
    rw [phaseProduct ell d e z]
  have had : A.adjoint = B.adjoint := by
    ext1 x
    apply (planeLLLEmbedding ell hell).injective
    apply Lp.ext
    filter_upwards [planeLLLEmbedding_coe ell hell (A.adjoint x),planeLLLEmbedding_coe ell hell (B.adjoint x)]
      with z ha hb
    rw [ha,hb,ContinuousLinearMap.adjoint_inner_right,ContinuousLinearMap.adjoint_inner_right,he]
  simpa only [ContinuousLinearMap.adjoint_adjoint] using congrArg (fun T : Orb => T.adjoint) had

theorem magnetic_square_cell (ell L : ℝ) (hell : 0 < ell) (hL : L^2=2*Real.pi*ell^2) :
    magneticCommutatorPhase ell (L:ℂ) ((L:ℂ)*Complex.I) = 1 := by
  unfold magneticCommutatorPhase
  rw [show ((2*ell^2 : ℝ):ℂ)⁻¹ * ((L:ℂ)*Complex.I*conj (L:ℂ) - (L:ℂ)*conj ((L:ℂ)*Complex.I)) =
    2*(Real.pi:ℂ)*Complex.I by
      have hl : (L:ℂ)^2 = 2*(Real.pi:ℂ)*(ell:ℂ)^2 := by exact_mod_cast hL
      have hn := Complex.ofReal_ne_zero.mpr hell.ne'
      simp only [map_mul,Complex.conj_ofReal,Complex.conj_I,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_ofNat]
      field_simp
      linear_combination 2*hl]
  exact Complex.exp_two_pi_mul_I

theorem magneticTranslationFactor_norm (ell : ℝ) (hell : 0 < ell) (d z : ℂ) :
    ‖magneticTranslationFactor ell d z‖ = 1 := by
  let D := planeGuidingDisplacement ell hell d
  have h := congrArg (fun v : CountableOrbital => ‖v‖^2) (guidingDisplacement_on_evaluation ell hell d z)
  simp only [LinearIsometryEquiv.norm_map,norm_smul,mul_pow,planeEvaluation_norm_sq ell hell] at h
  have hp : 0 < 1/(2*Real.pi*ell^2) := by positivity
  have he : ‖magneticTranslationFactor ell d z‖^2=1 := by
    apply mul_right_cancel₀ hp.ne'; simpa using h.symm
  nlinarith [norm_nonneg (magneticTranslationFactor ell d z)]

/-- The translated physical representative belongs to the same multiplied band
whenever the multiplier is periodic under that displacement. -/
theorem magneticTranslation_band (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ) (d : ℂ)
    (hp : ∀ z, f (z-d) = f z) (v : CountableOrbital) :
    let T := (planeGuidingDisplacement ell hell d).symm
    (planeScalarEmbedding ell hell f (T v) : ℂ → ℂ) =ᵐ[volume] fun z =>
      conj (magneticTranslationFactor ell d z) * planeScalarEmbedding ell hell f v (z-d) := by
  let D := planeGuidingDisplacement ell hell d
  have hshift : MeasurePreserving (fun z : ℂ => z-d) := by
    simpa only [sub_eq_add_neg] using measurePreserving_add_right (volume : Measure ℂ) (-d)
  have h := hshift.quasiMeasurePreserving.ae_eq_comp (planeScalarEmbedding_coe ell hell f v)
  filter_upwards [planeScalarEmbedding_coe ell hell f (D.symm v),h] with z hz hs
  change planeScalarEmbedding ell hell f v (z-d) = f (z-d) * inner ℂ (planeEvaluation ell (z-d)) v at hs
  have hi := D.inner_map_map (planeEvaluation ell z) (D.symm v)
  rw [D.apply_symm_apply, guidingDisplacement_on_evaluation, inner_smul_left] at hi
  rw [hz,← hi,hs,hp]; ring

theorem guiding_square_commute (ell L : ℝ) (hell : 0 < ell) (hL : L^2=2*Real.pi*ell^2) :
    Function.Commute (planeGuidingDisplacement ell hell (L:ℂ)) (planeGuidingDisplacement ell hell ((L:ℂ)*Complex.I)) := by
  have h := guidingDisplacement_commutator ell hell (L:ℂ) ((L:ℂ)*Complex.I)
  dsimp only at h
  rw [magnetic_square_cell ell L hell hL,one_smul] at h
  intro x
  exact congrArg (fun T : Orb => T x) h

def magneticCellLength (ell : ℝ) := Real.sqrt (2*Real.pi)*ell

theorem magneticCell_area (ell : ℝ) : (magneticCellLength ell)^2 = 2*Real.pi*ell^2 := by
  rw [magneticCellLength,mul_pow,Real.sq_sqrt (by positivity)]

private theorem harmonic_period (ell : ℝ) (hell : 0 < ell) (n : ℕ) :
    periodicMagneticWaveNumber ell n * magneticCellLength ell = n*(2*Real.pi) := by
  unfold periodicMagneticWaveNumber magneticCellLength
  have hs := Real.sq_sqrt (show 0 ≤ 2*Real.pi by positivity)
  field_simp
  nlinarith [congrArg (fun w : ℝ => (n:ℝ)*w) hs]

private theorem harmonic_shift (ell : ℝ) (hell : 0 < ell) (n : ℕ) (m : ℤ) (s : ℝ) :
    let q := periodicMagneticWaveNumber ell n
    Real.cos (q*(s-m*magneticCellLength ell)) = Real.cos (q*s) := by
  let q := periodicMagneticWaveNumber ell n
  have he : q*(s-m*magneticCellLength ell) = q*s+((-(m*n):ℤ):ℝ)*(2*Real.pi) := by
    push_cast
    linear_combination - (m:ℝ) * harmonic_period ell hell n
  dsimp only; rw [he,Real.cos_add_int_mul_two_pi]

theorem envelope_magnetic_period (ell : ℝ) (hell : 0 < ell) (n : ℕ)
    (ε : ℝ) (hε : 0 ≤ ε) (m j : ℤ) (z : ℂ) :
    let L := magneticCellLength ell
    let f := periodicEnvelope ε (periodicMagneticWaveNumber ell n) hε
    f (z-(⟨m*L,j*L⟩:ℂ)) = f z := by
  change ((Real.sqrt (1+ε/2*(_+_)):ℝ):ℂ) = _
  dsimp only [Complex.sub_re,Complex.sub_im]
  rw [harmonic_shift ell hell n m, harmonic_shift ell hell n j]; rfl

theorem nodal_magnetic_period (ell : ℝ) (hell : 0 < ell) (m j : ℤ) (z : ℂ) :
    let L := magneticCellLength ell
    planeNodal ell (z-(⟨m*L,j*L⟩:ℂ)) = planeNodal ell z := by
  have he : planeNodalWaveNumber ell = periodicMagneticWaveNumber ell 1 := by
    simp [planeNodalWaveNumber,periodicMagneticWaveNumber]
  change ((2*Real.cos (planeNodalWaveNumber ell * (z.re-m*magneticCellLength ell)) *
    Real.cos (planeNodalWaveNumber ell * (z.im-j*magneticCellLength ell)):ℝ):ℂ) = _
  rw [he,harmonic_shift ell hell 1 m,harmonic_shift ell hell 1 j,← he]
  rfl

end VortexGap.Fermion
