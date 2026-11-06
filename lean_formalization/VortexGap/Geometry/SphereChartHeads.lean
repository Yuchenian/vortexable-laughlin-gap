import VortexGap.Fermion.SphereSpectator
import VortexGap.Geometry.SphereChartTensor
import VortexGap.Geometry.LaughlinPolynomial

noncomputable section
namespace VortexGap.SpherePolynomial
open MvPolynomial VortexGap.Fermion
variable {Q N : ℕ}

def chartMonomial (i : Fin (Q+1)) (w : ℂ) : ℂ :=
  (Real.sqrt (Q.choose i.val) : ℂ) * w^i.val

private theorem split_assignments (f : OrbitalTuple Q (N+1) → ℂ) :
    ∑ a, f a = ∑ i, ∑ a, f (Fin.cons i a) := by
  rw [← (Fin.consEquiv (fun _ : Fin (N+1) => Fin (Q+1))).sum_comp f, Fintype.sum_prod_type]
  rfl

theorem spectatorValue_cons (A : OrbitalTuple Q (N+1) → ℂ) (w : ℂ) (z : Fin N → ℂ) :
    spectatorValue A (Fin.cons w z) =
      ∑ i, chartMonomial i w * spectatorValue (fun a => A (Fin.cons i a)) z := by
  unfold spectatorValue
  rw [split_assignments]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ,chartMonomial]
  ring

theorem sectorPoly_two_heads (x : particleSector (Q+1) (N+2)) (w v : ℂ) (z : Fin N → ℂ) :
    eval (Fin.cons w (Fin.cons v z)) (sectorPoly x) =
      spectatorValue (fun a => ∑ i, ∑ j, headCoeff x a i j *
        (chartMonomial i w * chartMonomial j v)) z := by
  rw [sectorPoly_eval]
  change spectatorValue _ _ = _
  rw [spectatorValue_cons]
  simp_rw [spectatorValue_cons]
  unfold spectatorValue
  simp_rw [Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_rhs => enter [2,a]; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro i _
  unfold headCoeff
  ring

end VortexGap.SpherePolynomial
end

noncomputable section
namespace VortexGap.SpherePolynomial
open MvPolynomial VortexGap.Fermion
variable {Q N : ℕ}

def chartPath (s : ℂ) (i : Fin (Q+1)) (t : ℝ) : ℂ := chartMonomial i (s+t)

def chartHeadJet (x : particleSector (Q+1) (N+2)) (s : ℂ) (a : OrbitalTuple Q N) : ℂ :=
  -2 * ∑ b : PairIndex (Q+1), pairSlice x a b *
    (chartPath s b.val.1 0 * deriv (chartPath s b.val.2) 0 -
     chartPath s b.val.2 0 * deriv (chartPath s b.val.1) 0)

theorem sectorPoly_head_hasDerivAt (x : particleSector (Q+1) (N+2)) (s : ℂ) (z : Fin N → ℂ) :
    HasDerivAt (fun t : ℝ => eval (Fin.cons (s+t) (Fin.cons (s-t) z)) (sectorPoly x))
      (spectatorValue (chartHeadJet x s) z) 0 := by
  have hd (i : Fin (Q+1)) : DifferentiableAt ℝ (chartPath s i) 0 := by
    unfold chartPath chartMonomial
    fun_prop
  have h (a : OrbitalTuple Q N) := head_relative_derivative x a (chartPath s)
    (fun i => deriv (chartPath s i) 0) (fun i => (hd i).hasDerivAt)
  have hh := HasDerivAt.fun_sum (u := (Finset.univ : Finset (OrbitalTuple Q N)))
    (fun a _ => (h a).mul_const (∏ k, chartMonomial (a k) (z k)))
  simpa only [sectorPoly_two_heads,spectatorValue,chartHeadJet,chartPath,chartMonomial,
    Complex.ofReal_neg,sub_eq_add_neg] using hh

theorem sectorPoly_head_deriv_zero_iff (x : particleSector (Q+1) (N+2)) (s : ℂ) :
    (∀ z : Fin N → ℂ, deriv (fun t : ℝ => eval
      (Fin.cons (s+t) (Fin.cons (s-t) z)) (sectorPoly x)) 0 = 0) ↔
      ∀ a, chartHeadJet x s a = 0 := by
  simp_rw [(sectorPoly_head_hasDerivAt x s _).deriv]
  exact spectatorValue_zero_iff _

end VortexGap.SpherePolynomial
end

noncomputable section
namespace VortexGap.SpherePolynomial
open MvPolynomial VortexGap.Fermion
variable {Q N : ℕ}

theorem sectorPoly_smul (c : ℂ) (x : particleSector (Q+1) N) :
    sectorPoly (c • x) = C c * sectorPoly x := by
  apply MvPolynomial.funext
  intro z
  simp only [sectorPoly_eval,map_mul,eval_C,map_smul,Submodule.coe_smul,PiLp.smul_apply,
    smul_eq_mul,Finset.mul_sum,mul_assoc]

/-- The chart-jet nullspace in the actual CAR sector at Laughlin flux. -/
theorem sector_chart_jet_line (N : ℕ) :
    ∃ l : particleSector (3*((N+2)-1)+1) (N+2), l ≠ 0 ∧ sectorPoly l = laughlin (N+2) ∧
      ∀ x, (∀ s a, chartHeadJet x s a = 0) ↔ ∃ c : ℂ, x = c • l := by
  obtain ⟨l,hl,_⟩ := laughlin_sector_preimage (N+2)
  have hz := sectorPoly_smul 0 l
  simp only [zero_smul,map_zero,zero_mul] at hz
  have hn : l ≠ 0 := fun h => laughlin_ne_zero _ (hl.symm.trans (h ▸ hz))
  refine ⟨l,hn,hl,?_⟩
  intro x
  have hr := (sectorPoly_range (sectorPoly x)).mp ⟨x,rfl⟩
  have h := head_pointwise_laughlin_iff hr.2 hr.1
  simp_rw [sectorPoly_head_deriv_zero_iff] at h
  rw [h]
  constructor
  · rintro ⟨c,hc⟩
    exact ⟨c,sectorPoly_injective (by rw [sectorPoly_smul,hl,hc])⟩
  · rintro ⟨c,rfl⟩
    exact ⟨c,by rw [sectorPoly_smul,hl]⟩

end VortexGap.SpherePolynomial
end

noncomputable section
namespace VortexGap.SpherePolynomial
variable {Q : ℕ}

/-- The affine coordinate of a spinor varying along a projective line. -/
def spinorRatio (a b c d t : ℂ) : ℂ := (b+d*t)/(a+c*t)

theorem spinorRatio_jet {a b c d : ℂ} (ha : a ≠ 0) :
    HasDerivAt (spinorRatio a b c d) ((a*d-b*c)/a^2) 0 := by
  have h := (((hasDerivAt_id (0:ℂ)).const_mul d).const_add b).div
    (((hasDerivAt_id (0:ℂ)).const_mul c).const_add a) (by simpa)
  simpa [spinorRatio,mul_comm] using! h

private theorem mono_diff (i : Fin (Q+1)) (s : ℂ) : DifferentiableAt ℂ (chartMonomial i) s := by
  unfold chartMonomial
  fun_prop

private theorem mono_path (i : Fin (Q+1)) (s : ℂ) :
    deriv (chartPath s i) 0 = deriv (chartMonomial i) s := by
  have h := ((mono_diff i s).hasDerivAt.comp_of_eq (0:ℂ)
    ((hasDerivAt_id (0:ℂ)).const_add s) (by simp)).comp_ofReal
  simpa [chartPath,Function.comp_def] using! h.deriv

/-- For a complex chart reparametrization and a real-differentiable common
orbital multiplier, the antisymmetric derivative picks up F(0)^2 times the
chart velocity. No derivative of the common multiplier survives. -/
theorem chartPair_transition (i j : Fin (Q+1)) (F : ℝ → ℂ) (w : ℂ → ℂ)
    (hF : DifferentiableAt ℝ F 0) (hw : DifferentiableAt ℂ w 0) :
    let u := fun (k : Fin (Q+1)) (t : ℝ) => F t * chartMonomial k (w t)
    u i 0 * deriv (u j) 0 - u j 0 * deriv (u i) 0 =
      F 0^2 * deriv w 0 *
        (chartPath (w 0) i 0 * deriv (chartPath (w 0) j) 0 -
         chartPath (w 0) j 0 * deriv (chartPath (w 0) i) 0) := by
  dsimp only
  have h (k : Fin (Q+1)) := hF.hasDerivAt.fun_mul
    (((mono_diff k (w 0)).hasDerivAt.comp 0 hw.hasDerivAt).comp_ofReal)
  simp only [Function.comp_def] at h
  rw [(h j).deriv,(h i).deriv,mono_path,mono_path]
  simp only [chartPath,Complex.ofReal_zero,add_zero]
  ring

/-- Orbital of the homogeneous spinor (A,B) in the affine patch A ≠ 0. -/
theorem spinorMonomial_factor (i : Fin (Q+1)) {A : ℂ} (B : ℂ) (hA : A ≠ 0) :
    (Real.sqrt (Q.choose i.val) : ℂ) * B^i.val * A^(Q-i.val) =
      A^Q * chartMonomial i (B/A) := by
  unfold chartMonomial
  rw [div_pow]
  field_simp
  have h := pow_add A (Q-i.val) i.val
  rw [Nat.sub_add_cancel (Nat.le_of_lt_succ i.isLt)] at h
  rw [h]
  ring

theorem spinorRatio_deriv_ne_zero {a b c d : ℂ} (ha : a ≠ 0) (hdet : a*d-b*c = 1) :
    deriv (spinorRatio a b c d) 0 ≠ 0 := by
  rw [(spinorRatio_jet ha).deriv,hdet]
  exact div_ne_zero one_ne_zero (pow_ne_zero _ ha)

end VortexGap.SpherePolynomial
end
