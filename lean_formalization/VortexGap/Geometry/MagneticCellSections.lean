import VortexGap.Geometry.MagneticTheta
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Function.L2Space
import VortexGap.Examples.MagneticCell
import VortexGap.Geometry.PeriodicShear

noncomputable section

namespace VortexGap.MagneticBloch
open Complex MeasureTheory Filter Set
open scoped Real Topology

/-- Dimensionless square coordinates after dividing the physical coordinate by
the one-flux length. The factor converts periodic holomorphic gauge to symmetric gauge. -/
def gauge (z : ℂ) := Complex.exp ((Real.pi:ℂ)/2*(z^2-((‖z‖^2:ℝ):ℂ)))

private theorem gauge_exponent (z : ℂ) : (Real.pi:ℂ)/2*(z^2-((‖z‖^2:ℝ):ℂ)) =
    -(Real.pi:ℂ)*z.im^2 + I*((Real.pi:ℂ)*z.re*z.im) := by
  rw [Complex.sq_norm,Complex.normSq_apply,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_mul]
  conv_lhs => rw [show z^2 = ((z.re:ℂ)+(z.im:ℂ)*I)^2 by rw [Complex.re_add_im]]
  linear_combination ((Real.pi:ℂ)/2)*(z.im:ℂ)^2*I_sq

theorem square_boundary (A B : ℂ) (u : sections A (Complex.exp (Real.pi:ℂ)*B))
    (m : ℂ → ℂ) (hm₁ : ∀ z, m (z+1)=m z) (hm₂ : ∀ z, m (z+I)=m z) (z : ℂ) :
    let ψ := fun w => m w*gauge w*u.val w
    ψ (z+1) = A*Complex.exp (I*((Real.pi:ℂ)*z.im))*ψ z ∧
    ψ (z+I) = B*Complex.exp (-I*((Real.pi:ℂ)*z.re))*ψ z := by
  obtain ⟨_,hx,hy⟩ := u.property
  dsimp only
  rw [hm₁,hm₂,hx,hy]
  unfold gauge harmonic
  simp only [gauge_exponent,add_im,add_re,one_im,one_re,I_im,I_re,add_zero,ofReal_add,ofReal_one,Int.cast_one]
  constructor
  · have hh : -(Real.pi:ℂ)*z.im^2 + I*((Real.pi:ℂ)*(z.re+1)*z.im) =
        I*((Real.pi:ℂ)*z.im)+(-(Real.pi:ℂ)*z.im^2+I*((Real.pi:ℂ)*z.re*z.im)) := by ring
    rw [hh,Complex.exp_add]; ring
  · have hh : -(Real.pi:ℂ)*(z.im+1)^2+I*((Real.pi:ℂ)*z.re*(z.im+1)) + Real.pi +
        -(1:ℂ)*(2*Real.pi*I)*z = -I*((Real.pi:ℂ)*z.re)+(-(Real.pi:ℂ)*z.im^2 + I*((Real.pi:ℂ)*z.re*z.im)) := by
      conv_lhs => rw [show -(1:ℂ)*(2*Real.pi*I)*z = -(1:ℂ)*(2*Real.pi*I)*((z.re:ℂ)+(z.im:ℂ)*I) by rw [re_add_im]]
      linear_combination -(2*(Real.pi:ℂ)*z.im)*I_sq
    have h := congrArg Complex.exp hh
    simp only [Complex.exp_add] at h ⊢
    linear_combination (m z*B*u.val z)*h

def cell : Set ℂ := Complex.equivRealProdCLM ⁻¹' ((Icc (0:ℝ) 1) ×ˢ (Icc (0:ℝ) 1))
def cellMeasure := (volume : Measure ℂ).restrict cell
private theorem cell_compact : IsCompact cell :=
  Complex.equivRealProdCLM.toHomeomorph.isCompact_preimage.mpr (isCompact_Icc.prod isCompact_Icc)

private def wave (F : ℂ ≃ₜ ℂ) {A B : ℂ} (m : ℂ → ℂ) (u : sections A B) (z : ℂ) := m z*gauge (F z)*u.val (F z)

private theorem wave_cont (F : ℂ ≃ₜ ℂ) {A B : ℂ} (m : ℂ → ℂ) (hm : Continuous m) (u : sections A B) :
    Continuous (wave F m u) := by
  have hg : Continuous gauge := by unfold gauge; fun_prop
  exact (hm.mul (hg.comp F.continuous)).mul (u.property.1.continuous.comp F.continuous)

private theorem wave_mem (F : ℂ ≃ₜ ℂ) {A B : ℂ} (m : ℂ → ℂ) (hm : Continuous m) (u : sections A B) :
    MemLp (wave F m u) 2 cellMeasure := by
  have h := wave_cont F m hm u
  exact (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mpr
    ((h.norm.pow 2).continuousOn.integrableOn_compact cell_compact)

def pullbackCellMap (F : ℂ ≃ₜ ℂ) (A B : ℂ) (m : ℂ → ℂ) (hm : Continuous m) : sections A B →ₗ[ℂ] Lp ℂ 2 cellMeasure where
  toFun u := (wave_mem F m hm u).toLp _
  map_add' u v := by
    apply Lp.ext
    filter_upwards [(wave_mem F m hm (u+v)).coeFn_toLp,(wave_mem F m hm u).coeFn_toLp,(wave_mem F m hm v).coeFn_toLp,
      Lp.coeFn_add ((wave_mem F m hm u).toLp _) ((wave_mem F m hm v).toLp _)] with z ht hu hv hs
    simp only [ht,hs,Pi.add_apply,hu,hv,wave,Submodule.coe_add,mul_add]
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [(wave_mem F m hm (c • u)).coeFn_toLp,(wave_mem F m hm u).coeFn_toLp,
      Lp.coeFn_smul c ((wave_mem F m hm u).toLp _)] with z ht hu hs
    simp only [RingHom.id_apply,ht,hs,Pi.smul_apply,hu,wave,Submodule.coe_smul,smul_eq_mul]; ring

theorem pullbackCellMap_injective (F : ℂ ≃ₜ ℂ) (A B : ℂ) (m : ℂ → ℂ) (hm : Continuous m)
    (h : ∃ z ∈ interior cell, m z ≠ 0) : Function.Injective (pullbackCellMap F A B m hm) := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro u hu
  have hz : pullbackCellMap F A B m hm u = 0 := hu
  have hae := (wave_mem F m hm u).coeFn_toLp
  change (pullbackCellMap F A B m hm u : ℂ → ℂ) =ᵐ[cellMeasure] wave F m u at hae
  rw [hz] at hae
  have heq : wave F m u =ᵐ[(volume : Measure ℂ).restrict cell] 0 := hae.symm.trans (Lp.coeFn_zero ..)
  have hs := Measure.eqOn_open_of_ae_eq (μ := volume) (ae_restrict_of_ae_restrict_of_subset interior_subset heq)
    isOpen_interior (wave_cont F m hm u).continuousOn continuous_zero.continuousOn
  obtain ⟨z,hzcell,hzn⟩ := h
  have hzero : (fun w => u.val (F w)) =ᶠ[nhds z] 0 := by
    filter_upwards [isOpen_interior.mem_nhds hzcell, hm.continuousAt.eventually_ne hzn] with w hw hmw
    have hh := hs hw
    change m w*gauge (F w)*u.val (F w)=0 at hh
    exact (mul_eq_zero.mp hh).resolve_left (mul_ne_zero hmw (Complex.exp_ne_zero _))
  have hinv : Tendsto F.symm (nhds (F z)) (nhds z) := by simpa only [F.symm_apply_apply] using (F.symm.continuous.continuousAt (x := F z)).tendsto
  have hlocal : u.val =ᶠ[nhds (F z)] 0 := by
    filter_upwards [hinv.eventually hzero] with w hw
    simpa using hw
  exact Subtype.ext (AnalyticOnNhd.eq_of_eventuallyEq (fun w _ => u.property.1.analyticAt w)
    (fun _ _ => analyticAt_const) hlocal)


def cellMap (A B : ℂ) (m : ℂ → ℂ) (hm : Continuous m) : sections A B →ₗ[ℂ] Lp ℂ 2 cellMeasure :=
  pullbackCellMap (Homeomorph.refl ℂ) A B m hm

theorem cellMap_injective (A B : ℂ) (m : ℂ → ℂ) (hm : Continuous m)
    (h : ∃ z ∈ interior cell, m z ≠ 0) : Function.Injective (cellMap A B m hm) :=
  pullbackCellMap_injective _ A B m hm h

theorem cell_rank_one (A B : ℂ) (hA : A ≠ 0) (hB : B ≠ 0)
    (m : ℂ → ℂ) (hm : Continuous m) (h : ∃ z ∈ interior cell, m z ≠ 0) :
    Module.finrank ℂ (cellMap A (Complex.exp (Real.pi:ℂ)*B) m hm).range = 1 :=
  ((cellMap A _ m hm).finrank_range_of_inj (cellMap_injective A _ m hm h)).trans
    (theta_rank_one A _ hA (mul_ne_zero (Complex.exp_ne_zero _) hB))

end VortexGap.MagneticBloch

namespace VortexGap.MagneticBloch
open Complex MeasureTheory VortexGap.Fermion Set
open scoped Real ComplexConjugate BoundedContinuousFunction

theorem guiding_phase_formula (ell : ℝ) (d w : ℂ) :
    magneticTranslationFactor ell d w =
      Complex.exp ((d*conj w - w*conj d)/(4*(ell:ℂ)^2)) := by
  change ((Real.exp (-‖d‖^2/(4*ell^2)) : ℂ))⁻¹ * Complex.exp
    (((2*ell^2 : ℝ):ℂ)⁻¹ * (d*conj w-w*conj d-d*conj d)/2) = _
  rw [Complex.ofReal_exp,← Complex.exp_neg,← Complex.exp_add]
  congr 1
  push_cast
  have he : ((‖d‖:ℝ):ℂ)^2 = d*conj d := by rw [← Complex.ofReal_pow,Complex.sq_norm,Complex.mul_conj]
  rw [he]
  by_cases hz : ell = 0
  · simp [hz]
  · have hn := Complex.ofReal_ne_zero.mpr hz
    field_simp
    ring

private theorem axis_phase (ell : ℝ) (hell : 0 < ell) (z : ℂ) :
    let L : ℂ := magneticCellLength ell
    conj (magneticTranslationFactor ell L (L*z)) = Complex.exp (I*((Real.pi:ℂ)*z.im)) ∧
    conj (magneticTranslationFactor ell (L*I) (L*z)) = Complex.exp (-I*((Real.pi:ℂ)*z.re)) := by
  let L : ℂ := magneticCellLength ell
  have hL : L^2=2*(Real.pi:ℂ)*(ell:ℂ)^2 := by dsimp only [L]; exact_mod_cast magneticCell_area ell
  have hconj : conj L = L := Complex.conj_ofReal _
  have hn := Complex.ofReal_ne_zero.mpr hell.ne'
  dsimp only
  change conj (magneticTranslationFactor ell L (L*z)) = _ ∧ conj (magneticTranslationFactor ell (L*I) (L*z)) = _
  simp only [guiding_phase_formula,← Complex.exp_conj,map_div₀,map_mul,map_pow,map_ofNat,
    map_sub,hconj,Complex.conj_ofReal,Complex.conj_I,starRingEnd_self_apply]
  constructor <;> congr 1
  · have hh := Complex.sub_conj z
    push_cast at hh
    field_simp
    linear_combination L^2*hh + (2*(z.im:ℂ)*I)*hL
  · have hh := Complex.add_conj z
    push_cast at hh
    simp only [map_neg,Complex.conj_I,neg_neg]
    field_simp
    linear_combination -L^2*hh - (2*(z.re:ℂ))*hL

def scaledMultiplier (ell : ℝ) (f : ℂ →ᵇ ℂ) (z : ℂ) := f ((magneticCellLength ell : ℂ)*z)

private theorem scaled_cont (ell : ℝ) (f : ℂ →ᵇ ℂ) : Continuous (scaledMultiplier ell f) :=
  f.continuous.comp (continuous_const.mul continuous_id)

def physicalCellMap (ell : ℝ) (f : ℂ →ᵇ ℂ) (A B : ℂ) :=
  cellMap A (Complex.exp (Real.pi:ℂ)*B) (scaledMultiplier ell f) (scaled_cont ell f)

theorem cellMap_magnetic_boundary (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hp : ∀ (m j : ℤ) z, f (z-(⟨m*magneticCellLength ell,j*magneticCellLength ell⟩:ℂ)) = f z)
    (A B : ℂ) (u : sections A (Complex.exp (Real.pi:ℂ)*B)) (z : ℂ) :
    let L : ℂ := magneticCellLength ell
    let ψ := fun s => scaledMultiplier ell f s*gauge s*u.val s
    ψ (z+1) = A*conj (magneticTranslationFactor ell L (L*z))*ψ z ∧
    ψ (z+I) = B*conj (magneticTranslationFactor ell (L*I) (L*z))*ψ z := by
  let L : ℂ := magneticCellLength ell
  have xper (w : ℂ) : scaledMultiplier ell f (w+1) = scaledMultiplier ell f w := by
    have he : (⟨(-1:ℤ)*magneticCellLength ell,(0:ℤ)*magneticCellLength ell⟩:ℂ) = -L := by
      apply Complex.ext <;> simp [L]
    have h := hp (-1) 0 (L*w)
    rw [he,sub_neg_eq_add] at h
    simpa only [scaledMultiplier,mul_add,mul_one,L] using h
  have yper (w : ℂ) : scaledMultiplier ell f (w+I) = scaledMultiplier ell f w := by
    have he : (⟨(0:ℤ)*magneticCellLength ell,(-1:ℤ)*magneticCellLength ell⟩:ℂ) = -(L*I) := by
      apply Complex.ext <;> simp [L]
    have h := hp 0 (-1) (L*w)
    rw [he,sub_neg_eq_add] at h
    simpa only [scaledMultiplier,mul_add,L] using h
  dsimp only
  rw [(axis_phase ell hell z).1,(axis_phase ell hell z).2]
  exact square_boundary A B u _ xper yper z

private def midpoint : ℂ := ⟨1/2,1/2⟩
private theorem midpoint_interior : midpoint ∈ interior cell := by
  change midpoint ∈ interior (Icc (0:ℝ) 1 ×ℂ Icc (0:ℝ) 1)
  rw [interior_reProdIm,interior_Icc,mem_reProdIm]
  norm_num [midpoint]

theorem envelope_cell_rank (ell : ℝ) (hell : 0 < ell) (n : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hu : ε < 1) (A B : ℂ) (hA : ‖A‖=1) (hB : ‖B‖=1) :
    Module.finrank ℂ (physicalCellMap ell (periodicEnvelope ε (periodicMagneticWaveNumber ell n) hε) A B).range = 1 := by
  apply cell_rank_one _ _ (fun h => by simp [h] at hA) (fun h => by simp [h] at hB)
  refine ⟨midpoint,midpoint_interior,?_⟩
  let q := periodicMagneticWaveNumber ell n
  let z := (magneticCellLength ell:ℂ)*midpoint
  change periodicEnvelope ε q hε z ≠ 0
  intro hz
  have h := periodicEnvelope_norm_sq hε hu q z
  rw [hz,norm_zero,zero_pow (by decide : 2≠0)] at h
  linarith [(periodicWeight_bounds hε q z).1]

theorem nodal_cell_rank (ell : ℝ) (hell : 0 < ell) (A B : ℂ) (hA : ‖A‖=1) (hB : ‖B‖=1) :
    Module.finrank ℂ (physicalCellMap ell (planeNodal ell) A B).range = 1 := by
  apply cell_rank_one _ _ (fun h => by simp [h] at hA) (fun h => by simp [h] at hB)
  refine ⟨midpoint,midpoint_interior,?_⟩
  have he : planeNodalWaveNumber ell * (magneticCellLength ell*(1/2)) = Real.pi := by
    unfold planeNodalWaveNumber magneticCellLength
    have h := Real.sq_sqrt (show 0 ≤ 2*Real.pi by positivity)
    field_simp
    nlinarith
  change ((2*Real.cos (planeNodalWaveNumber ell*((magneticCellLength ell:ℂ)*midpoint).re)*
    Real.cos (planeNodalWaveNumber ell*((magneticCellLength ell:ℂ)*midpoint).im):ℝ):ℂ) ≠ 0
  simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero,midpoint,he,Real.cos_pi]
  norm_num

end VortexGap.MagneticBloch

namespace VortexGap.MagneticBloch
open Complex MeasureTheory Filter Set VortexGap.Fermion
open scoped Real Topology

private def shearInCell (a ell : ℝ) (z : ℂ) :=
  periodicShear a (2*Real.pi/magneticCellLength ell) ((magneticCellLength ell:ℂ)*z) / (magneticCellLength ell:ℂ)

private theorem shearInCell_continuous (a ell : ℝ) : Continuous (shearInCell a ell) :=
  ((periodicShear_continuous ..).comp (continuous_const.mul continuous_id)).div_const _

private theorem shearInCell_inverse (a ell : ℝ) (hell : 0 < ell) (z : ℂ) :
    shearInCell (-a) ell (shearInCell a ell z) = z := by
  have hL : (magneticCellLength ell : ℂ) ≠ 0 := by
    apply ofReal_ne_zero.mpr; unfold magneticCellLength; positivity
  unfold shearInCell
  rw [show ∀ v : ℂ, (magneticCellLength ell:ℂ)*(v/(magneticCellLength ell:ℂ)) = v by intro v; field_simp,
    periodicShear_inverse]; field_simp

def shearCellCoordinates (a ell : ℝ) (hell : 0 < ell) : ℂ ≃ₜ ℂ where
  toFun := shearInCell a ell
  invFun := shearInCell (-a) ell
  left_inv := shearInCell_inverse a ell hell
  right_inv z := by simpa using shearInCell_inverse (-a) ell hell z
  continuous_toFun := shearInCell_continuous a ell
  continuous_invFun := shearInCell_continuous (-a) ell

theorem shearCell_periods (a ell : ℝ) (hell : 0 < ell) (z : ℂ) :
    let F := shearCellCoordinates a ell hell
    F (z+1)=F z+1 ∧ F (z+I)=F z+I := by
  let L := magneticCellLength ell
  have hL : L ≠ 0 := by dsimp [L,magneticCellLength]; positivity
  have hs (m j : ℤ) := periodicShear_lattice a (2*Real.pi/L) L (by field_simp) m j ((L:ℂ)*z)
  have hx := hs 1 0
  have hy := hs 0 1
  have e1 : (⟨(1:ℤ)*L,(0:ℤ)*L⟩:ℂ) = (L:ℂ) := by apply Complex.ext <;> simp
  have e2 : (⟨(0:ℤ)*L,(1:ℤ)*L⟩:ℂ) = (L:ℂ)*I := by apply Complex.ext <;> simp
  rw [e1] at hx; rw [e2] at hy
  have hc := ofReal_ne_zero.mpr hL
  change periodicShear a _ ((L:ℂ)*(z+1)) / (L:ℂ) = _ ∧ periodicShear a _ ((L:ℂ)*(z+I)) / (L:ℂ) = _
  constructor
  · rw [mul_add,mul_one,hx]
    change (_+(L:ℂ))/(L:ℂ) = periodicShear a (2*Real.pi/L) ((L:ℂ)*z)/(L:ℂ)+1; field_simp
  · rw [mul_add,hy]
    change (_+(L:ℂ)*I)/(L:ℂ) = periodicShear a (2*Real.pi/L) ((L:ℂ)*z)/(L:ℂ)+I; field_simp

/-- Transport the one-flux boundary conditions by the physical coordinate map. -/
theorem shear_boundary (a ell : ℝ) (hell : 0 < ell) (A B : ℂ)
    (u : sections A (Complex.exp (Real.pi:ℂ)*B)) (z : ℂ) :
    let F := shearCellCoordinates a ell hell
    let ψ := fun s => gauge (F s) * u.val (F s)
    ψ (z+1)=A*Complex.exp (I*((Real.pi:ℂ)*(F z).im))*ψ z ∧
    ψ (z+I)=B*Complex.exp (-I*((Real.pi:ℂ)*(F z).re))*ψ z := by
  dsimp only
  rw [(shearCell_periods a ell hell z).1,(shearCell_periods a ell hell z).2]
  simpa only [one_mul] using square_boundary A B u (fun _ => 1) (fun _ => rfl) (fun _ => rfl)
    (shearCellCoordinates a ell hell z)

theorem shear_cell_rank (a ell : ℝ) (hell : 0 < ell) (A B : ℂ) (hA : ‖A‖=1) (hB : ‖B‖=1) :
    Module.finrank ℂ (pullbackCellMap (shearCellCoordinates a ell hell) A (Complex.exp (Real.pi:ℂ)*B)
      (fun _ => 1) continuous_const).range = 1 := by
  rw [LinearMap.finrank_range_of_inj (pullbackCellMap_injective _ _ _ _ _
    ⟨midpoint, midpoint_interior, one_ne_zero⟩)]
  exact theta_rank_one _ _ (fun h => by simp [h] at hA)
    (mul_ne_zero (Complex.exp_ne_zero _) (fun h => by simp [h] at hB))

end VortexGap.MagneticBloch
