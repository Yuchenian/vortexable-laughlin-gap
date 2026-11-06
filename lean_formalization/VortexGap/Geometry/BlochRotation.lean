import OAI.Analysis.Laughlin.Spin.Torus
import VortexGap.Geometry.RoundArea
import OAI.Analysis.Laughlin.Spin.Mixing
import Mathlib.Tactic

noncomputable section
namespace VortexGap.Fermion
open OAI.Laughlin.Rotation VortexGap.Geometry
open scoped Matrix ComplexConjugate RealInnerProductSpace

def spinorVector (a b : ℂ) : RoundAmbient :=
  WithLp.toLp 2 ![(2*conj a*b).re,(2*conj a*b).im,Complex.normSq a-Complex.normSq b]

theorem spinorVector_inner (a b c d : ℂ) :
    ⟪spinorVector a b,spinorVector c d⟫ =
      2*Complex.normSq (conj a*c+conj b*d) -
        (Complex.normSq a+Complex.normSq b)*(Complex.normSq c+Complex.normSq d) := by
  simp [spinorVector,PiLp.inner_apply,Fin.sum_univ_three,Complex.normSq_apply,
    Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im]
  ring

def rotationVector (g : SourceSU2) := spinorVector (g.val 0 0) (g.val 1 0)

private theorem spinor_overlap (g h : SourceSU2) :
    conj (g.val 0 0)*h.val 0 0 + conj (g.val 1 0)*h.val 1 0 = (g⁻¹*h).val 0 0 := by
  change _ = (star g.val * h.val) 0 0
  simp [Matrix.mul_apply,Fin.sum_univ_two,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply]

private theorem spinor_unit (g : SourceSU2) :
    Complex.normSq (g.val 0 0) + Complex.normSq (g.val 1 0) = 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp g.property.1) 0) 0
  simpa [Matrix.mul_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,
    Complex.mul_conj,Fin.sum_univ_two,mul_comm] using congrArg Complex.re h

theorem rotationVector_inner (g h : SourceSU2) :
    ⟪rotationVector g,rotationVector h⟫ = 2*Complex.normSq ((g⁻¹*h).val 0 0)-1 := by
  simp only [rotationVector,spinorVector_inner,spinor_unit,spinor_overlap,one_mul]

theorem rotationVector_left_inner (k g h : SourceSU2) :
    ⟪rotationVector (k*g),rotationVector (k*h)⟫ = ⟪rotationVector g,rotationVector h⟫ := by
  simp [rotationVector_inner,mul_assoc]

/-- Three lifts of a Cartesian basis suffice to extend the left action to an ambient rotation. -/
theorem rotationVector_ambient_of_basis (p : Fin 3 → SourceSU2)
    (hp : Orthonormal ℝ (fun i => rotationVector (p i))) (k : SourceSU2) :
    ∃ e : RoundAmbient ≃ₗᵢ[ℝ] RoundAmbient, ∀ g, e (rotationVector g) = rotationVector (k*g) := by
  have hq : Orthonormal ℝ (fun i => rotationVector (k*p i)) := by
    rw [orthonormal_iff_ite] at hp ⊢
    intro i j
    exact (rotationVector_left_inner k _ _).trans (hp i j)
  let b := OrthonormalBasis.mk hp (hp.linearIndependent.span_eq_top_of_card_eq_finrank' (by simp [RoundAmbient])).ge
  let c := OrthonormalBasis.mk hq (hq.linearIndependent.span_eq_top_of_card_eq_finrank' (by simp [RoundAmbient])).ge
  refine ⟨b.repr.trans c.repr.symm,fun g => ?_⟩
  apply c.repr.injective
  change c.repr (c.repr.symm _) = _
  rw [c.repr.apply_symm_apply]
  ext i
  change b.repr (rotationVector g) i = c.repr (rotationVector (k*g)) i
  simp only [OrthonormalBasis.repr_apply_apply,b,c,OrthonormalBasis.coe_mk]
  exact (rotationVector_left_inner k _ _).symm

private def yLift : SourceSU2 := by
  let c : ℂ := (Real.sqrt (1/2) : ℝ)
  have hc : c^2 = 1/2 := by
    have H := congrArg Complex.ofReal (Real.sq_sqrt (by norm_num : 0 ≤ (1/2 : ℝ)))
    push_cast at H
    exact H
  have hr : conj c = c := Complex.conj_ofReal _
  refine ⟨!![c,Complex.I*c;Complex.I*c,c],?_⟩
  constructor
  · apply Matrix.mem_unitaryGroup_iff.mpr
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,hr] <;>
      ring_nf <;> norm_num [hc,Complex.I_sq]
  · simp [Matrix.det_fin_two]
    ring_nf <;> norm_num [hc,Complex.I_sq]

theorem rotationVector_ambient (k : SourceSU2) :
    ∃ e : RoundAmbient ≃ₗᵢ[ℝ] RoundAmbient, ∀ g, e (rotationVector g) = rotationVector (k*g) := by
  let p : Fin 3 → SourceSU2 := ![sourceMixer,yLift,1]
  apply rotationVector_ambient_of_basis p _ k
  have hc : (Real.sqrt (1/2))^2 = (1/2:ℝ) := Real.sq_sqrt (by norm_num)
  rw [orthonormal_iff_ite]
  intro i j
  by_cases hij : i=j
  · subst j; rw [rotationVector_inner]; norm_num
  fin_cases i <;> fin_cases j <;> first | contradiction |
    (norm_num [p,rotationVector,spinorVector,PiLp.inner_apply,Fin.sum_univ_three,
      sourceMixer,yLift,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,
      Real.sq_sqrt,Real.sqrt_nonneg] <;> nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)])

end VortexGap.Fermion
end
