import VortexGap.Geometry.SphereGaugeSection

noncomputable section
namespace VortexGap.Fermion
open OAI.Laughlin.Rotation
open scoped ComplexConjugate Matrix

/-- Cartesian sphere coordinates, with x+iy stored in the first component. -/
abbrev BlochSphere := {p : ℂ × ℝ // Complex.normSq p.1 + p.2^2 = 1}

private theorem column_unit (g : SourceSU2) :
    Complex.normSq (g.val 0 0) + Complex.normSq (g.val 1 0) = 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp g.property.1) 0) 0
  have h' := congrArg Complex.re h
  simpa [Matrix.mul_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,
    Complex.mul_conj,Fin.sum_univ_two,mul_comm] using h'

def sphereBloch (g : SourceSU2) : BlochSphere :=
  ⟨(2 * conj (g.val 0 0) * g.val 1 0, Complex.normSq (g.val 0 0) - Complex.normSq (g.val 1 0)),by
    dsimp only
    simp only [map_mul,Complex.normSq_conj]
    norm_num
    nlinarith [congrArg (fun r : ℝ => r^2) (column_unit g)]⟩

theorem sphereBloch_phase (g : SourceSU2) (z : ℂ) (hz : ‖z‖=1) :
    sphereBloch (g * sourceTorus z hz) = sphereBloch g := by
  have ent (i : Fin 2) : (g * sourceTorus z hz).val i 0 = g.val i 0 * z := by
    change (g.val * Matrix.diagonal (fun k : Fin 2 => if k=0 then z else star z)) i 0 = _
    simp [Matrix.mul_diagonal]
  apply Subtype.ext
  change (_,_) = (_, _)
  apply Prod.ext
  · dsimp only
    simp only [ent,map_mul]
    have h : z * conj z = 1 := by simpa [hz] using Complex.mul_conj' z
    linear_combination 2 * conj (g.val 0 0) * g.val 1 0 * h
  · dsimp only
    simp [ent,Complex.normSq_eq_norm_sq,hz]

def sphereBlochConfiguration {N : ℕ} : spherePhaseQuotient N → (Fin N → BlochSphere) :=
  Quot.lift (fun g i => sphereBloch (g i)) (by
    rintro g _ ⟨z,hz,rfl⟩
    funext i
    exact (sphereBloch_phase _ _ _).symm)

theorem sphereBloch_north : (sphereBloch 1).val = (0,1) := by
  norm_num [sphereBloch]

theorem sphereBloch_continuous : Continuous sphereBloch := by
  apply Continuous.subtype_mk
  have h (i : Fin 2) : Continuous (fun g : SourceSU2 => g.val i 0) :=
    (continuous_apply 0).comp ((continuous_apply i).comp continuous_subtype_val)
  apply Continuous.prodMk
  · exact (continuous_const.mul (continuous_star.comp (h 0))).mul (h 1)
  · exact (Complex.continuous_normSq.comp (h 0)).sub (Complex.continuous_normSq.comp (h 1))

theorem sphereAxial_bloch (g : SourceSU2) :
    sphereAxialMultiplier g = (Real.sqrt (1+(1+(sphereBloch g).val.2)/2000) : ℂ) := by
  unfold sphereAxialMultiplier
  congr 2
  change 1+‖g.val 0 0‖^2/1000 = 1+(1+(Complex.normSq (g.val 0 0)-Complex.normSq (g.val 1 0)))/2000
  rw [← Complex.normSq_eq_norm_sq]
  linarith [column_unit g]

end VortexGap.Fermion
end

noncomputable section
namespace VortexGap.Fermion
open OAI.Laughlin.Rotation
open scoped Matrix ComplexConjugate

/-- Complete a unit spinor to a special unitary matrix with that first column. -/
def spinorFrame (a b : ℂ) (hu : Complex.normSq a + Complex.normSq b = 1) : SourceSU2 := by
  have hh := congrArg Complex.ofReal hu
  push_cast at hh
  rw [← Complex.mul_conj,← Complex.mul_conj] at hh
  refine ⟨!![a,-conj b;b,conj a],?_⟩
  constructor
  · apply Matrix.mem_unitaryGroup_iff.mpr
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply] <;>
      first | linear_combination hh | ring
  · simp [Matrix.det_fin_two]
    linear_combination hh

theorem spinorFrame_bloch (a b : ℂ) (hu) :
    (sphereBloch (spinorFrame a b hu)).val =
      (2*conj a*b, Complex.normSq a - Complex.normSq b) := rfl

theorem sphereBloch_surjective : Function.Surjective sphereBloch := by
  rintro ⟨⟨w,z⟩,hs⟩
  change Complex.normSq w + z^2 = 1 at hs
  have hz : -1 ≤ z := by nlinarith [Complex.normSq_nonneg w,sq_nonneg (z+1)]
  by_cases hp : z = -1
  · subst z
    have hw : w=0 := Complex.normSq_eq_zero.mp (by linarith)
    subst w
    refine ⟨spinorFrame 0 1 (by simp),Subtype.ext ?_⟩
    rw [spinorFrame_bloch]
    norm_num
  · let a := Real.sqrt ((1+z)/2)
    have ha : 0<a := Real.sqrt_pos.mpr (by linarith [lt_of_le_of_ne hz (Ne.symm hp)])
    have hsq : a^2 = (1+z)/2 := Real.sq_sqrt (by linarith)
    let b : ℂ := w/(2*a)
    have hb : Complex.normSq b = (1-z)/2 := by
      rw [show Complex.normSq b = Complex.normSq w / (4*a^2) by
        simp [b,Complex.normSq_ofReal]; ring_nf]
      apply (div_eq_iff (by positivity)).mpr
      nlinarith [hsq,hs,congrArg (fun x : ℝ => x*z) hsq]
    have hu : Complex.normSq (a:ℂ) + Complex.normSq b = 1 := by
      rw [Complex.normSq_ofReal,hb]; nlinarith
    refine ⟨spinorFrame a b hu,Subtype.ext ?_⟩
    rw [spinorFrame_bloch]
    apply Prod.ext
    · dsimp only
      simp only [Complex.conj_ofReal,b]
      field_simp [show (a:ℂ) ≠ 0 by exact_mod_cast ha.ne']
    · simp only [Complex.normSq_ofReal,hb]
      nlinarith

theorem sphereBlochConfiguration_surjective (N : ℕ) :
    Function.Surjective (@sphereBlochConfiguration N) := by
  intro p
  choose g hg using fun i => sphereBloch_surjective (p i)
  exact ⟨Quot.mk _ g,funext hg⟩

end VortexGap.Fermion
end
