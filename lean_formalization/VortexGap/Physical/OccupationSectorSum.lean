import VortexGap.Physical.SectorDirectSum
import VortexGap.Fermion.CountableSpectatorSectors

noncomputable section

namespace VortexGap.Fermion
open scoped ComplexOrder BoundedContinuousFunction

theorem occupationSector_hilbert_sum :
    IsHilbertSum ℂ (fun N : ℕ => countableSector N) (fun N => (countableSector N).subtypeₗᵢ) := by
  apply IsHilbertSum.mkInternal
  · intro i j hij x y
    exact countableSector_orthogonal x.property y.property hij
  · intro x _
    let S := ⨆ N, countableSector N
    change x ∈ S.topologicalClosure
    apply S.isClosed_topologicalClosure.mem_of_tendsto (countableSpace_hasSum x)
    apply Filter.Eventually.of_forall
    intro s
    apply S.le_topologicalClosure
    exact S.sum_mem fun A _ => S.smul_mem (x A) ((le_iSup countableSector A.card) (countableKet_sector A))

def occupationSectorUnitary : CountableSpace ≃ₗᵢ[ℂ] SectorFock :=
  occupationSector_hilbert_sum.linearIsometryEquiv

theorem occupationSectorUnitary_sector (N : ℕ) (u : countableSector N) :
    occupationSectorUnitary (u : CountableSpace) = lp.single 2 N u := by
  apply occupationSectorUnitary.symm.injective
  rw [LinearIsometryEquiv.symm_apply_apply]
  exact (occupationSector_hilbert_sum.linearIsometryEquiv_symm_apply_single u).symm

theorem occupationSectorUnitary_expansion (x : SectorFock) :
    HasSum (fun N => (x N : CountableSpace)) (occupationSectorUnitary.symm x) :=
  occupationSector_hilbert_sum.hasSum_linearIsometryEquiv_symm x

/-- Uniform sector spectral bounds assemble on the full unbounded Fock domain. -/
theorem sectorSum_of_spectral_bounds (H : (N : ℕ) → countableSector N →L[ℂ] countableSector N)
    (hH : ∀ N, (H N).IsPositive) (γ : ℝ)
    (hgap : ∀ N, ∀ s ∈ spectrum ℝ (H N), s = 0 ∨ γ ≤ s) :
    let T := sectorSumOperator H
    IsSelfAdjoint T ∧
      (∀ x : T.domain, γ*(inner ℂ x.val (T x)).re ≤ ‖T x‖^2) ∧
      (∀ (x : T.domain) (hx : T x ∈ T.domain), γ*(inner ℂ x.val (T x)).re ≤
        (inner ℂ x.val (T ⟨T x,hx⟩)).re) := by
  have hp N := (hH N).isSelfAdjoint
  have hg (N : ℕ) := (quadratic_positive_norm_iff _ (hH N) γ).mp
    ((quadratic_positive_iff_spectrum_gap _ (hH N) γ).mpr (hgap N))
  exact ⟨sectorSum_selfAdjoint H hp,sectorSum_form H γ hg,sectorSum_square H hp γ hg⟩

theorem scalar_fullFock_criterion (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hf : Differentiable ℝ f) (g u κ γ : ℝ) (hg : 0 < g) (hgu : g ≤ u) (hκ : 0 < κ)
    (hlo : g • (1 : CountableOrbital →L[ℂ] CountableOrbital) ≤ planeScalarGram ell hell f)
    (hhi : planeScalarGram ell hell f ≤ u • (1 : CountableOrbital →L[ℂ] CountableOrbital))
    (hw : (κ:ℂ) • planePairOperator ≤ planeWeightedPairOperator ell f)
    (href : ∀ j, let H := countablePairLift j planePairOperator
      (H*H-(γ:ℂ) • H).IsPositive) :
    let hG := gramOperator_strict (planeScalarEmbedding ell hell f) g hg hlo
    let T := sectorSumOperator (planeBandContactOperator ell hell f hG hf)
    let b := κ/g^2*(γ-14*(1-g/u)-(1-g/u)^2)
    IsSelfAdjoint T ∧ (∀ x : T.domain, b*(inner ℂ x.val (T x)).re ≤ ‖T x‖^2) ∧
      (∀ (x : T.domain) (hx : T x ∈ T.domain), b*(inner ℂ x.val (T x)).re ≤
        (inner ℂ x.val (T ⟨T x,hx⟩)).re) :=
  sectorSum_of_spectral_bounds _ (fun N => planeBandContactOperator_positive ..) _
    (fun N => physical_scalar_criterion ell hell f hf g u κ γ hg hgu hκ hlo hhi hw N (fun j _ => href j))

end VortexGap.Fermion
