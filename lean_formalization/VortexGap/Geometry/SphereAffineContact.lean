import VortexGap.Fermion.SphereSpectator
import VortexGap.Geometry.SphereChartHeads

noncomputable section
namespace VortexGap.Fermion
open OAI.Laughlin.Rotation VortexGap.SpherePolynomial Filter
open scoped Topology
variable {n : ℕ}

-- Radius 1/2 identifies the physical tangent variable with the dimensionless coordinate.
def affineSpinA (k : SourceSU2) (t : ℂ) := k.val 0 0 + k.val 1 0 * t
def affineSpinW (k : SourceSU2) := spinorRatio (k.val 0 0) (k.val 0 1) (k.val 1 0) (k.val 1 1)
def affineSpinF (n : ℕ) (k : SourceSU2) (t : ℝ) :=
  sphereChartOrbital (n+1) 0 (1/2) t * (affineSpinA k t)^(n+1)

theorem rotatedOrbital_affine_germ (g : SourceSU2) (i : Fin (n+2)) (ha : g⁻¹.val 0 0 ≠ 0) :
    (fun t : ℝ => sphereRotatedOrbital n g i (1/2) t) =ᶠ[𝓝 0]
      fun t => affineSpinF n g⁻¹ t * chartMonomial i (affineSpinW g⁻¹ t) := by
  have hc : Continuous (fun t : ℝ => affineSpinA g⁻¹ t) := by unfold affineSpinA; fun_prop
  have hn := hc.continuousAt.eventually_ne (y := 0) (x := 0) (by simpa [affineSpinA] using ha)
  filter_upwards [hn] with t ht
  rw [sphereRotatedOrbital_spinor]
  simp only [one_div,Complex.ofReal_inv,Complex.ofReal_ofNat,mul_inv_cancel₀ (two_ne_zero : (2:ℂ)≠0),div_one]
  unfold affineSpinA at ht
  rw [spinorMonomial_factor i (g⁻¹.val 0 1 + g⁻¹.val 1 1 * (t:ℂ)) ht]
  simp [affineSpinF,affineSpinA,affineSpinW,spinorRatio,sphereChartOrbital,mul_assoc,show (n:ℝ)+1+1=n+2 by ring]

theorem affineSpinF_diff (n : ℕ) (k : SourceSU2) : DifferentiableAt ℝ (affineSpinF n k) 0 := by
  have h := (sphereChartOrbital_jet (n+1) 0 (1/2) 1).differentiableAt
  simp only [mul_one] at h
  apply h.mul
  unfold affineSpinA
  fun_prop

theorem affineSpinF_ne_zero (n : ℕ) (k : SourceSU2) (ha : k.val 0 0 ≠ 0) :
    affineSpinF n k 0 ≠ 0 := by
  rw [affineSpinF,Complex.ofReal_zero,sphereChartOrbital_origin]
  simp only [ite_true,affineSpinA,mul_zero,add_zero]
  exact mul_ne_zero (by exact_mod_cast (Real.sqrt_pos.mpr (by positivity)).ne') (pow_ne_zero _ ha)

theorem rotatedPair_affine_transition (g : SourceSU2) (i j : Fin (n+2)) (ha : g⁻¹.val 0 0 ≠ 0) :
    let u := fun (k : Fin (n+2)) (t : ℝ) => sphereRotatedOrbital n g k (1/2) t
    let s := affineSpinW g⁻¹ 0
    u i 0 * deriv (u j) 0 - u j 0 * deriv (u i) 0 =
      affineSpinF n g⁻¹ 0 ^ 2 * deriv (affineSpinW g⁻¹) 0 *
      (chartPath s i 0 * deriv (chartPath s j) 0 - chartPath s j 0 * deriv (chartPath s i) 0) := by
  dsimp only
  have hi := rotatedOrbital_affine_germ g i ha
  have hj := rotatedOrbital_affine_germ g j ha
  have hw : DifferentiableAt ℂ (affineSpinW g⁻¹) 0 := (spinorRatio_jet ha).differentiableAt
  have h := chartPair_transition i j _ _ (affineSpinF_diff n g⁻¹) hw
  dsimp only at h
  rw [← hi.deriv_eq,← hj.deriv_eq] at h
  simpa only [← hi.eq_of_nhds,← hj.eq_of_nhds] using! h

end VortexGap.Fermion
end

noncomputable section
namespace VortexGap.Fermion
open OAI.Laughlin.Rotation VortexGap.SpherePolynomial
variable {n N : ℕ}

theorem affineSpinW_velocity_ne_zero (k : SourceSU2) (ha : k.val 0 0 ≠ 0) :
    deriv (affineSpinW k) 0 ≠ 0 := by
  apply spinorRatio_deriv_ne_zero ha
  simpa [Matrix.det_fin_two,mul_comm] using (Matrix.mem_specialUnitaryGroup_iff.mp k.property).2

theorem rotatedHead_affine_jet (x : particleSector (n+2) (N+2)) (a : Fin N → Fin (n+2))
    (g : SourceSU2) (ha : g⁻¹.val 0 0 ≠ 0) :
    deriv (rotatedHeadAmplitude x a g (1/2) 1) 0 =
      (affineSpinF n g⁻¹ 0 ^ 2 * deriv (affineSpinW g⁻¹) 0) *
        chartHeadJet x (affineSpinW g⁻¹ 0) a := by
  rw [(rotatedHeadAmplitude_jet x a g (1/2) 1).deriv,spectatorContraction_inner,
    ← sphereRotatedContact_eq_inner]
  unfold sphereRotatedContact chartHeadJet
  simp only [mul_one]
  have h (i j : Fin (n+2)) := rotatedPair_affine_transition g i j ha
  dsimp only at h
  simp only [Complex.ofReal_zero] at h
  simp_rw [h]
  simp only [Finset.mul_sum]

  apply Finset.sum_congr rfl
  intro b _
  ring

theorem spectatorContraction_affine_zero_iff (x : particleSector (n+2) (N+2))
    (a : Fin N → Fin (n+2)) (g : SourceSU2) (ha : g⁻¹.val 0 0 ≠ 0) :
    spectatorContraction (sphereOrbitPair n g) x a = 0 ↔
      chartHeadJet x (affineSpinW g⁻¹ 0) a = 0 := by
  rw [← rotatedHeadAmplitude_zero_iff x a g (1/2) (by norm_num),rotatedHead_affine_jet x a g ha]
  exact mul_eq_zero.trans (or_iff_right (mul_ne_zero (pow_ne_zero _ (affineSpinF_ne_zero n _ ha))
    (affineSpinW_velocity_ne_zero _ ha)))

end VortexGap.Fermion
end

noncomputable section
namespace VortexGap.Fermion
open OAI.Laughlin.Rotation VortexGap.SpherePolynomial
open scoped Matrix ComplexConjugate

theorem affine_center_lift (s : ℂ) : ∃ g : SourceSU2, g⁻¹.val 0 0 ≠ 0 ∧ affineSpinW g⁻¹ 0 = s := by
  let r := Real.sqrt (1 + ‖s‖^2)
  have hr : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hrs : r^2 = 1+‖s‖^2 := Real.sq_sqrt (by positivity)
  let c : ℝ := r⁻¹
  let b : ℂ := s * c
  have hnorm : (c:ℂ)^2 + b * conj b = 1 := by
    have he : c^2 * (1+‖s‖^2) = 1 := by rw [← hrs]; simp [c,hr.ne']
    have hh := congrArg Complex.ofReal he
    push_cast at hh
    simp only [b,map_mul,Complex.conj_ofReal]
    linear_combination hh + (c:ℂ)^2 * (Complex.mul_conj' s)
  let k : SourceSU2 := ⟨!![(c:ℂ),b;-conj b,(c:ℂ)],by
    constructor
    · apply Matrix.mem_unitaryGroup_iff.mpr
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply] <;>
        first | linear_combination hnorm | ring
    · simp [Matrix.det_fin_two]
      linear_combination hnorm⟩
  refine ⟨k⁻¹,?_,?_⟩
  · rw [inv_inv]
    change (c:ℂ) ≠ 0
    exact_mod_cast inv_ne_zero hr.ne'
  · rw [inv_inv]
    change (b + (c:ℂ)*0)/((c:ℂ) + (-conj b)*0) = s
    simp [b,c,hr.ne']

theorem chartHeadJet_zero_of_all_contractions {n N : ℕ} (x : particleSector (n+2) (N+2))
    (h : ∀ g a, spectatorContraction (sphereOrbitPair n g) x a = 0) :
    ∀ s a, chartHeadJet x s a = 0 := by
  intro s a
  obtain ⟨g,ha,hs⟩ := affine_center_lift s
  rw [← hs]
  exact (spectatorContraction_affine_zero_iff x a g ha).mp (h g a)

end VortexGap.Fermion
end

noncomputable section
namespace VortexGap.Fermion
open OAI.Laughlin.Rotation VortexGap.SpherePolynomial Filter
open scoped Matrix ComplexConjugate Topology

private def c (t : ℝ) := (1-t^2)/(1+t^2)
private def b (t : ℝ) := 2*t/(1+t^2)
private def turn (t : ℝ) : SourceSU2 := by
  have h : (c t : ℂ)^2 + (b t : ℂ)^2 = 1 := by
    have hr : (c t)^2+(b t)^2=1 := by
      unfold c b
      field_simp [show 1+t^2 ≠ 0 by positivity]
      ring
    simpa using congrArg Complex.ofReal hr
  refine ⟨!![(c t:ℂ),(b t:ℂ);-(b t:ℂ),(c t:ℂ)],?_⟩
  constructor
  · apply Matrix.mem_unitaryGroup_iff.mpr
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply] <;>
      first | linear_combination h | ring
  · simp [Matrix.det_fin_two]
    linear_combination h

private theorem turn_zero : turn 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [turn,c,b]

private theorem turn_cont : Continuous turn := by
  have hc : Continuous c := by unfold c; fun_prop (disch := intro x; positivity)
  have hb : Continuous b := by unfold b; fun_prop (disch := intro x; positivity)
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem sphere_affine_extension (F : SourceSU2 → ℂ) (hc : Continuous F)
    (hz : ∀ g : SourceSU2, g⁻¹.val 0 0 ≠ 0 → F g = 0) (g : SourceSU2) : F g = 0 := by
  by_cases ha : g⁻¹.val 0 0 = 0
  · have hdet := (Matrix.mem_specialUnitaryGroup_iff.mp g⁻¹.property).2
    rw [Matrix.det_fin_two,ha] at hdet
    have hc10 : g⁻¹.val 1 0 ≠ 0 := by
      intro h
      simp [h] at hdet
    let path := fun t : ℝ => (turn t * g⁻¹)⁻¹
    have hp : Continuous path := (turn_cont.mul continuous_const).inv
    have he (t : ℝ) (ht : t ≠ 0) : F (path t) = 0 := by
      apply hz
      simp only [path,inv_inv]
      change ( (turn t).val * g⁻¹.val ) 0 0 ≠ 0
      simp [Matrix.mul_apply,Fin.sum_univ_two,ha,turn,b,ht,hc10]
      exact_mod_cast (show 1+t^2 ≠ 0 by positivity)
    have hlim : Tendsto (fun t => F (path t)) (𝓝[≠] 0) (𝓝 (F (path 0))) := (hc.comp hp).continuousAt (x := 0) |>.tendsto.mono_left nhdsWithin_le_nhds
    have heq : (fun t => F (path t)) =ᶠ[𝓝[≠] (0:ℝ)] (fun _ => 0) :=
      by filter_upwards [self_mem_nhdsWithin (a := (0:ℝ)) (s := ({0}:Set ℝ)ᶜ)] with t ht; exact he t ht
    have hh := tendsto_nhds_unique (hlim : Tendsto (fun t => F (path t)) (𝓝[≠] 0) _) (tendsto_const_nhds.congr' heq.symm)
    simpa [path,turn_zero] using hh
  · exact hz g ha

theorem all_contractions_iff_chartHeadJet {n N : ℕ} (x : particleSector (n+2) (N+2)) :
    (∀ g a, spectatorContraction (sphereOrbitPair n g) x a = 0) ↔ ∀ s a, chartHeadJet x s a = 0 := by
  refine ⟨chartHeadJet_zero_of_all_contractions x,?_⟩
  intro h g a
  apply sphere_affine_extension (fun k => spectatorContraction (sphereOrbitPair n k) x a) _ _ g
  · simp_rw [spectatorContraction_inner]
    exact (sphereOrbitPair_continuous n).inner continuous_const
  · intro k hk
    exact (spectatorContraction_affine_zero_iff x a k hk).mpr (h _ a)

end VortexGap.Fermion
end
