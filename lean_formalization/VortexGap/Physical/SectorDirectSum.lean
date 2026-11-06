import VortexGap.Fermion.CountablePairLift
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import VortexGap.Reference.CertifiedPlane
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct LinearPMap Topology
open Filter

/-- Hilbert direct sum over the physical occupation-number sectors. -/
abbrev SectorFock := lp (fun N : ℕ => countableSector N) 2

variable (H : (N : ℕ) → countableSector N →L[ℂ] countableSector N)

def sectorSumDomain : Submodule ℂ SectorFock where
  carrier := {x | Memℓp (fun N => H N (x N)) 2}
  zero_mem' := by simpa using! (zero_memℓp (E := fun N : ℕ => countableSector N) (p := 2))
  add_mem' := by
    intro x y hx hy
    simpa only [Set.mem_ofPred_eq,lp.coeFn_add,Pi.add_apply,map_add] using!
      (show Memℓp (fun N => H N (x N)) 2 from hx).add hy
  smul_mem' := by
    intro c x hx
    simpa only [Set.mem_ofPred_eq,lp.coeFn_smul,Pi.smul_apply,map_smul] using!
      (show Memℓp (fun N => H N (x N)) 2 from hx).const_smul c

def sectorSumOperator : SectorFock →ₗ.[ℂ] SectorFock where
  domain := sectorSumDomain H
  toFun :=
    { toFun := fun x => ⟨fun N => H N (x.val N), x.property⟩
      map_add' := fun x y => by apply Subtype.ext; funext N; exact (H N).map_add _ _
      map_smul' := fun c x => by apply Subtype.ext; funext N; exact (H N).map_smul c _ }

private theorem sectorSum_single (N : ℕ) (v : countableSector N) :
    (fun j => H j ((lp.single 2 N v : SectorFock) j)) = (lp.single 2 N (H N v) : SectorFock) := by
  funext j
  by_cases hj : j=N
  · subst j; simp
  · simp [Pi.single_eq_of_ne hj]

theorem sectorSum_single_mem (N : ℕ) (v : countableSector N) :
    lp.single 2 N v ∈ (sectorSumOperator H).domain := by
  change Memℓp _ 2
  rw [sectorSum_single]
  exact lp.memℓp _

theorem sectorSum_dense : Dense ((sectorSumOperator H).domain : Set SectorFock) := by
  intro x
  apply mem_closure_of_tendsto (lp.hasSum_single ENNReal.ofNat_ne_top x)
  exact Eventually.of_forall fun s => (sectorSumOperator H).domain.sum_mem
    (fun i _ => sectorSum_single_mem H i (x i))

theorem sectorSum_selfAdjoint (hH : ∀ N, IsSelfAdjoint (H N)) : IsSelfAdjoint (sectorSumOperator H) := by
  let T := sectorSumOperator H
  have hsym (N : ℕ) (u v : countableSector N) : inner ℂ (H N u) v = inner ℂ u (H N v) := by
    have hh : (H N).adjoint = H N := hH N
    rw [← hh, ContinuousLinearMap.adjoint_inner_left, hh]
  have hf : T.IsFormalAdjoint T := by
    intro x y
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    exact tsum_congr (fun N => hsym N _ _)
  have hd := sectorSum_dense H
  have htest (x : T.adjoint.domain) (N : ℕ) : (T.adjoint x) N = H N (x.val N) := by
    apply ext_inner_right ℂ
    intro v
    let y : T.domain := ⟨lp.single 2 N v, sectorSum_single_mem H N v⟩
    have h := T.adjoint_isFormalAdjoint hd x y
    change inner ℂ (T.adjoint x) (lp.single 2 N v) = inner ℂ x.val (T y) at h
    have he : T y = lp.single 2 N (H N v) := by apply Subtype.ext; exact sectorSum_single H N v
    rw [he, lp.inner_single_right, lp.inner_single_right] at h
    exact h.trans (hsym N _ _).symm
  apply le_antisymm _ (hf.le_adjoint hd)
  have hmem (x : T.adjoint.domain) : x.val ∈ T.domain := by
    change Memℓp (fun N => H N (x.val N)) 2
    simp_rw [← htest x]
    exact lp.memℓp _
  refine ⟨fun x hx => hmem ⟨x,hx⟩, ?_⟩
  intro x y hxy
  apply Subtype.ext
  funext N
  exact (htest x N).trans (congrArg (fun z : SectorFock => H N (z N)) hxy)

/-- Uniform sector bounds extend to the maximal form domain without a uniform bound on H_N. -/
theorem sectorSum_form (γ : ℝ) (hg : ∀ N (v : countableSector N),
    γ*(inner ℂ v (H N v)).re ≤ ‖H N v‖^2) (x : (sectorSumOperator H).domain) :
    γ*(inner ℂ x.val (sectorSumOperator H x)).re ≤ ‖sectorSumOperator H x‖^2 := by
  let y := sectorSumOperator H x
  have h₁ := (Complex.hasSum_re (lp.hasSum_inner (𝕜 := ℂ) x.val y)).mul_left γ
  have h₂ := Complex.hasSum_re (lp.hasSum_inner (𝕜 := ℂ) y y)
  simp only [← RCLike.re_eq_complex_re, ← norm_sq_eq_re_inner (𝕜 := ℂ)] at h₂
  apply hasSum_le (fun N => hg N (x.val N)) h₁
  simpa using! h₂

/-- On D(H²) the same estimate has the operator form. -/
theorem sectorSum_square (hH : ∀ N, IsSelfAdjoint (H N)) (γ : ℝ)
    (hg : ∀ N (v : countableSector N), γ*(inner ℂ v (H N v)).re ≤ ‖H N v‖^2)
    (x : (sectorSumOperator H).domain) (hx : sectorSumOperator H x ∈ (sectorSumOperator H).domain) :
    γ*(inner ℂ x.val (sectorSumOperator H x)).re ≤
      (inner ℂ x.val (sectorSumOperator H ⟨sectorSumOperator H x,hx⟩)).re := by
  let T := sectorSumOperator H
  have ha : T.adjoint = T := sectorSum_selfAdjoint H hH
  have hf := T.adjoint_isFormalAdjoint (sectorSum_dense H)
  rw [ha] at hf
  have he := hf x (⟨T x,hx⟩ : T.domain)
  rw [← he]
  change _ ≤ (inner ℂ (T x) (T x)).re
  rw [← RCLike.re_eq_complex_re, ← norm_sq_eq_re_inner (𝕜 := ℂ)]
  exact sectorSum_form H γ hg x

/-- Full Fock realization of the weak-cosine physical contact in normalized band coordinates. -/
def planeWeakCosFock (ell : ℝ) (hell : 0 < ell) : SectorFock →ₗ.[ℂ] SectorFock :=
  sectorSumOperator (planeWeakCosContactOperator ell hell)

private theorem weakCos_sector_positive (ell : ℝ) (hell : 0 < ell) (N : ℕ) :
    (planeWeakCosContactOperator ell hell N).IsPositive := planeBandContactOperator_positive .. 

theorem planeWeakCosFock_selfAdjoint (ell : ℝ) (hell : 0 < ell) :
    IsSelfAdjoint (planeWeakCosFock ell hell) :=
  sectorSum_selfAdjoint _ (fun N => (weakCos_sector_positive ell hell N).isSelfAdjoint)

private theorem weakCos_sector_form (ell : ℝ) (hell : 0 < ell) (N : ℕ) (v : countableSector N) :
    (3/100:ℝ)*(inner ℂ v (planeWeakCosContactOperator ell hell N v)).re ≤
      ‖planeWeakCosContactOperator ell hell N v‖^2 :=
  (quadratic_positive_norm_iff _ (weakCos_sector_positive ell hell N) _).mp
    ((quadratic_positive_iff_spectrum_gap _ (weakCos_sector_positive ell hell N) _).mpr
      (planeWeakCos_certified_gap ell hell N).2) v

theorem planeWeakCosFock_form (ell : ℝ) (hell : 0 < ell) (x : (planeWeakCosFock ell hell).domain) :
    (3/100:ℝ)*(inner ℂ x.val (planeWeakCosFock ell hell x)).re ≤ ‖planeWeakCosFock ell hell x‖^2 :=
  sectorSum_form _ _ (weakCos_sector_form ell hell) x

theorem planeWeakCosFock_square (ell : ℝ) (hell : 0 < ell) (x : (planeWeakCosFock ell hell).domain)
    (hx : planeWeakCosFock ell hell x ∈ (planeWeakCosFock ell hell).domain) :
    (3/100:ℝ)*(inner ℂ x.val (planeWeakCosFock ell hell x)).re ≤
      (inner ℂ x.val (planeWeakCosFock ell hell ⟨planeWeakCosFock ell hell x,hx⟩)).re :=
  sectorSum_square _ (fun N => (weakCos_sector_positive ell hell N).isSelfAdjoint)
    _ (weakCos_sector_form ell hell) x hx

end VortexGap.Fermion
