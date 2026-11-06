import VortexGap.Geometry.LaughlinPolynomial
import Mathlib.LinearAlgebra.Vandermonde
import VortexGap.Fermion.TensorSector
import Mathlib.Algebra.MvPolynomial.Funext

noncomputable section
namespace VortexGap.SpherePolynomial
open MvPolynomial VortexGap.Fermion
variable {Q N : ℕ}
abbrev OrbitalTuple (Q N : ℕ) := Fin N → Fin (Q+1)
def powers (a : OrbitalTuple Q N) : Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (a i).val)

private theorem powers_inj : Function.Injective (@powers Q N) := by
  intro a b h
  funext i
  exact Fin.ext (congrArg (fun d : Fin N →₀ ℕ => d i) h)

def tensorPoly (A : OrbitalTuple Q N → ℂ) : Poly N :=
  ∑ a, monomial (powers a) (A a)

theorem coeff_tensorPoly (A : OrbitalTuple Q N → ℂ) (a : OrbitalTuple Q N) :
    (tensorPoly A).coeff (powers a) = A a := by
  classical
  simp [tensorPoly,coeff_monomial,powers_inj.eq_iff]

private theorem coeff_outside (A : OrbitalTuple Q N → ℂ) (m : Fin N →₀ ℕ)
    (h : ∃ i, Q < m i) : (tensorPoly A).coeff m = 0 := by
  obtain ⟨i,hi⟩ := h
  have he (a : OrbitalTuple Q N) : powers a ≠ m := by
    intro hh
    have : (a i).val = m i := congrArg (fun d : Fin N →₀ ℕ => d i) hh
    have := (a i).isLt
    omega
  simp [tensorPoly,coeff_monomial,he]

theorem tensorPoly_degree (A : OrbitalTuple Q N → ℂ) (i : Fin N) : (tensorPoly A).degreeOf i ≤ Q := by
  apply degreeOf_le_iff.mpr
  intro m hm
  by_contra! h
  exact (mem_support_iff.mp hm) (coeff_outside A m ⟨i,h⟩)

theorem bounded_reconstruct (p : Poly N) (hb : ∀ i, p.degreeOf i ≤ Q) :
    tensorPoly (fun a : OrbitalTuple Q N => p.coeff (powers a)) = p := by
  classical
  ext m
  by_cases h : ∀ i, m i ≤ Q
  · let a : OrbitalTuple Q N := fun i => ⟨m i,Nat.lt_succ_of_le (h i)⟩
    have he : powers a = m := by ext i; rfl
    rw [← he,coeff_tensorPoly]
  · push Not at h
    rw [coeff_outside _ m h]
    obtain ⟨i,hi⟩ := h
    exact (notMem_support_iff.mp (fun hm => hi.not_ge ((degreeOf_le_iff.mp (hb i)) m hm))).symm

private theorem swap_powers (i j : Fin N) (a : OrbitalTuple Q N) :
    (powers a).mapDomain (Equiv.swap i j) = powers (a ∘ Equiv.swap i j) := by
  ext k
  rw [Finsupp.mapDomain_equiv_apply]
  rfl

theorem tensorPoly_swap (A : OrbitalTuple Q N → ℂ) (i j : Fin N) :
    rename (Equiv.swap i j) (tensorPoly A) = tensorPoly (fun a => A (a ∘ Equiv.swap i j)) := by
  classical
  simp only [tensorPoly,map_sum,rename_monomial,swap_powers]
  apply Finset.sum_bij' (fun a _ => a ∘ Equiv.swap i j) (fun a _ => a ∘ Equiv.swap i j)
  all_goals intros; simp [Function.comp_def]

/-- Binomial normalization in the dimensionless sphere chart. The common
radial and area prefactors are independent of the orbital index. -/
def tupleWeight (a : OrbitalTuple Q N) : ℂ :=
  ∏ i, (Real.sqrt (Q.choose (a i).val) : ℂ)

private theorem weight_ne (a : OrbitalTuple Q N) : tupleWeight a ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact_mod_cast (Real.sqrt_pos.mpr (by exact_mod_cast Nat.choose_pos (Nat.le_of_lt_succ (a i).isLt))).ne'

private theorem weight_swap (a : OrbitalTuple Q N) (i j : Fin N) :
    tupleWeight (a ∘ Equiv.swap i j) = tupleWeight a :=
  Equiv.prod_comp (Equiv.swap i j) (fun k => (Real.sqrt (Q.choose (a k).val) : ℂ))

def sectorPoly (x : particleSector (Q+1) N) : Poly N :=
  tensorPoly (fun a : OrbitalTuple Q N => tupleWeight a * (sectorTensorIsometry (Q+1) N x).val a)

theorem sectorPoly_injective : Function.Injective (@sectorPoly Q N) := by
  intro x y h
  apply (sectorTensorIsometry _ _).injective
  apply Subtype.ext
  ext a
  have hh := congrArg (fun p : Poly N => p.coeff (powers a)) h
  simp only [sectorPoly,coeff_tensorPoly] at hh
  exact mul_left_cancel₀ (weight_ne a) hh

theorem sectorPoly_alternating (x : particleSector (Q+1) N) (i j : Fin N) (h : i≠j) :
    rename (Equiv.swap i j) (sectorPoly x) = -sectorPoly x := by
  rw [sectorPoly,tensorPoly_swap]
  have ha := (sectorTensorIsometry _ _ x).property i j h
  simp only [tensorPoly,weight_swap,ha,mul_neg,map_neg,Finset.sum_neg_distrib]

theorem sectorPoly_range (p : Poly N) :
    (∃ x : particleSector (Q+1) N, sectorPoly x = p) ↔
      (∀ i, p.degreeOf i ≤ Q) ∧ (∀ i j : Fin N, i ≠ j → rename (Equiv.swap i j) p = -p) := by
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨tensorPoly_degree (fun a : OrbitalTuple Q N => tupleWeight a * (sectorTensorIsometry (Q+1) N x).val a),sectorPoly_alternating x⟩
  · rintro ⟨hb,hs⟩
    let ψ : TensorSpace (Q+1) N := WithLp.toLp 2 (fun a => p.coeff (powers a) / tupleWeight a)
    have ha : ψ ∈ antisymmetricTensors (Q+1) N := by
      intro i j hij a
      have hc := coeff_rename_mapDomain (Equiv.swap i j) (Equiv.swap i j).injective p (powers a)
      rw [swap_powers,hs i j hij,coeff_neg] at hc
      change p.coeff (powers (a ∘ Equiv.swap i j)) / _ = -(p.coeff (powers a) / _)
      rw [weight_swap,← hc,neg_div,neg_neg]
    let t : antisymmetricTensors (Q+1) N := ⟨ψ,ha⟩
    refine ⟨(sectorTensorIsometry _ _).symm t,?_⟩
    simp only [sectorPoly,LinearIsometryEquiv.apply_symm_apply]
    convert bounded_reconstruct p hb using 1
    congr 1
    funext a
    change tupleWeight a * (p.coeff (powers a) / tupleWeight a) = _
    field_simp [weight_ne]

theorem sectorPoly_eval (x : particleSector (Q+1) N) (z : Fin N → ℂ) :
    eval z (sectorPoly x) = ∑ a : OrbitalTuple Q N,
      (sectorTensorIsometry _ _ x).val a * ∏ i, ((Real.sqrt (Q.choose (a i).val) : ℂ) * z i^(a i).val) := by
  simp only [sectorPoly,tensorPoly,map_sum,eval_monomial]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _),Finset.prod_mul_distrib]
  change tupleWeight a * (sectorTensorIsometry _ _ x).val a * (∏ i, z i^(a i).val) = _
  exact (mul_assoc _ _ _).trans (mul_left_comm _ _ _)

theorem laughlin_alternating (i j : Fin N) (h : i ≠ j) :
    rename (Equiv.swap i j) (laughlin N) = -laughlin N := by
  classical
  let v : Fin N → Poly N := fun k => -X k
  have det (e : Fin N → Fin N) : (Matrix.vandermonde (v ∘ e)).det =
      ∏ k, ∏ l ∈ Finset.Ioi k, (X (e k) - X (e l) : Poly N) := by
    simp [Matrix.det_vandermonde,v,sub_eq_add_neg,add_comm]
  have hh := Matrix.det_permute (Equiv.swap i j) (Matrix.vandermonde v)
  change (Matrix.vandermonde (v ∘ Equiv.swap i j)).det = _ at hh
  rw [Equiv.Perm.sign_swap h] at hh
  have hid : (Matrix.vandermonde v).det = _ := det id
  rw [det,hid] at hh
  simp at hh
  simp only [laughlin,map_pow,map_prod,map_sub,rename_X]
  rw [hh]; ring

/-- A unique actual sector vector has the explicit cubic Vandermonde as its
weighted chart polynomial. This statement makes no Hamiltonian assertion. -/
theorem laughlin_sector_preimage (N : ℕ) :
    ∃! x : particleSector (3*(N-1)+1) N, sectorPoly x = laughlin N := by
  obtain ⟨x,hx⟩ := (sectorPoly_range (Q := 3*(N-1)) (laughlin N)).mpr
    ⟨fun i => (laughlin_degree N i).le, fun i j hij => laughlin_alternating i j hij⟩
  exact ⟨x,hx,fun y hy => sectorPoly_injective (hy.trans hx.symm)⟩

/-- At flux three the unique polynomial preimage has the signed chart
value -1 at the ordered points (0,1), fixing the Vandermonde convention. -/
theorem sector_flux_three_chart_test :
    ∃ x : particleSector 4 2, sectorPoly x = laughlin 2 ∧
      eval (fun i : Fin 2 => (i.val : ℂ)) (sectorPoly x) = -1 := by
  obtain ⟨x,hx,_⟩ := laughlin_sector_preimage 2
  refine ⟨x,hx,?_⟩
  rw [hx]
  have h₀ : Finset.Ioi (0 : Fin 2) = {1} := by decide
  have h₁ : Finset.Ioi (1 : Fin 2) = ∅ := by decide
  norm_num [laughlin,Fin.prod_univ_two,h₀,h₁]

end VortexGap.SpherePolynomial
end

noncomputable section
namespace VortexGap.SpherePolynomial
open MvPolynomial
variable {Q N : ℕ}

/-- Evaluation of arbitrary spectator amplitudes in the normalized orbital basis. -/
def spectatorValue (A : OrbitalTuple Q N → ℂ) (z : Fin N → ℂ) : ℂ :=
  ∑ a, A a * ∏ k, ((Real.sqrt (Q.choose (a k).val) : ℂ) * z k^(a k).val)

theorem spectatorValue_eq_eval (A : OrbitalTuple Q N → ℂ) (z : Fin N → ℂ) :
    spectatorValue A z = eval z (tensorPoly fun a => tupleWeight a * A a) := by
  simp only [spectatorValue,tensorPoly,map_sum,eval_monomial]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _),Finset.prod_mul_distrib]
  change A a * (tupleWeight a * _) = tupleWeight a * A a * (∏ k, z k^(a k).val)
  ring

theorem spectatorValue_zero_iff (A : OrbitalTuple Q N → ℂ) :
    (∀ z, spectatorValue A z = 0) ↔ ∀ a, A a = 0 := by
  constructor
  · intro hz a
    have he : tensorPoly (fun b => tupleWeight b * A b) = 0 := by
      apply MvPolynomial.funext
      intro z
      rw [← spectatorValue_eq_eval,map_zero,hz]
    have hc := congrArg (fun p : Poly N => p.coeff (powers a)) he
    rw [coeff_tensorPoly] at hc
    change tupleWeight a * A a = 0 at hc
    apply (mul_eq_zero.mp hc).resolve_left
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact_mod_cast (Real.sqrt_pos.mpr (by exact_mod_cast Nat.choose_pos (Nat.le_of_lt_succ (a i).isLt))).ne'
  · intro ha z
    simp [spectatorValue,ha]

end VortexGap.SpherePolynomial
end
