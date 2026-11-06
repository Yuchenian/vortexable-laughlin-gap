import VortexGap.Fermion.LossReference
import VortexGap.Fermion.SplitProduct

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators InnerProduct ComplexConjugate ComplexOrder

variable {n : ℕ}
variable (M : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
variable (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)

theorem create_add (u v : EuclideanSpace ℂ (Fin n)) : create (u+v) = create u + create v := by
  simp only [create, PiLp.add_apply, add_smul, Finset.sum_add_distrib]

theorem annihilate_add (u v : EuclideanSpace ℂ (Fin n)) :
    annihilate (u+v) = annihilate u + annihilate v := by
  simp only [annihilate, PiLp.add_apply, map_add, add_smul, Finset.sum_add_distrib]

theorem loss_create_product (v : EuclideanSpace ℂ (Fin n)) (u x : Space n) :
    create (finiteLossEmbedding M hM hc v) ((fockSplit n n).symm (fockProduct u x)) =
      (fockSplit n n).symm (fockProduct (create (lossDefect M v) u) x +
        fockProduct (parity n u) (create (M v) x)) := by
  apply (fockSplit n n).injective
  rw [(fockSplit n n).apply_symm_apply, finiteLossEmbedding_apply, create_add]
  simp only [LinearMap.add_apply, map_add, fockSplit_create_env_product, fockSplit_create_sys_product]

theorem loss_annihilate_product (v : EuclideanSpace ℂ (Fin n)) (u x : Space n) :
    annihilate (finiteLossEmbedding M hM hc v) ((fockSplit n n).symm (fockProduct u x)) =
      (fockSplit n n).symm (fockProduct (annihilate (lossDefect M v) u) x +
        fockProduct (parity n u) (annihilate (M v) x)) := by
  apply (fockSplit n n).injective
  rw [(fockSplit n n).apply_symm_apply, finiteLossEmbedding_apply, annihilate_add]
  simp only [LinearMap.add_apply, map_add, fockSplit_annihilate_env_product, fockSplit_annihilate_sys_product]

theorem loss_annihilate_vacuum (v : EuclideanSpace ℂ (Fin n)) (x : Space n) :
    annihilate (finiteLossEmbedding M hM hc v) ((fockSplit n n).symm (environmentVacuum n n x)) =
      (fockSplit n n).symm (environmentVacuum n n (annihilate (M v) x)) := by
  rw [← fockProduct_vacuum, loss_annihilate_product]
  simp only [vector_annihilate_vacuum, parity_vacuum, map_zero, LinearMap.zero_apply, zero_add,
    fockProduct_vacuum]

theorem loss_pairAnnihilate_vacuum (u v : EuclideanSpace ℂ (Fin n)) (x : Space n) :
    pairAnnihilate (exteriorSquare (finiteLossEmbedding M hM hc).toLinearMap (wedgePair u v))
      ((fockSplit n n).symm (environmentVacuum n n x)) =
    (fockSplit n n).symm (environmentVacuum n n
      (pairAnnihilate (exteriorSquare M.toLinearMap (wedgePair u v)) x)) := by
  rw [exteriorSquare_wedge, exteriorSquare_wedge, pairAnnihilate_wedge, pairAnnihilate_wedge]
  change annihilate (finiteLossEmbedding M hM hc v)
    (annihilate (finiteLossEmbedding M hM hc u) ((fockSplit n n).symm (environmentVacuum n n x))) = _
  rw [loss_annihilate_vacuum, loss_annihilate_vacuum]
  rfl

/-- The explicit mixed creation amplitude; its minus sign is the fermionic parity sign. -/
def oneLossCreation (u v : EuclideanSpace ℂ (Fin n)) : Space n →ₗ[ℂ] SplitSpace n n :=
  (fockProduct (create (lossDefect M u) (ket ∅))).comp (create (M v)) -
    (fockProduct (create (lossDefect M v) (ket ∅))).comp (create (M u))

/-- The actual normalized two-environment amplitude, with no extra factor two. -/
def twoLossCreation (p : PairSpace n) : Space n →ₗ[ℂ] SplitSpace n n :=
  fockProduct (pairEmbed (exteriorSquare (lossDefect M).toLinearMap p))

theorem loss_pairCreate_vacuum (u v : EuclideanSpace ℂ (Fin n)) (x : Space n) :
    fockSplit n n
      (pairCreate (exteriorSquare (finiteLossEmbedding M hM hc).toLinearMap (wedgePair u v))
        ((fockSplit n n).symm (environmentVacuum n n x))) =
    environmentVacuum n n (pairCreate (exteriorSquare M.toLinearMap (wedgePair u v)) x) +
      oneLossCreation M u v x + twoLossCreation M (wedgePair u v) x := by
  have hp : parity n (create (lossDefect M v) (ket ∅)) = -create (lossDefect M v) (ket ∅) := by
    rw [parity_on_sector (create_sector (lossDefect M v) (sector_ket ∅))]
    norm_num
  rw [exteriorSquare_wedge, exteriorSquare_wedge, pairCreate_wedge, pairCreate_wedge]
  change fockSplit n n (create (finiteLossEmbedding M hM hc u)
    (create (finiteLossEmbedding M hM hc v) ((fockSplit n n).symm (environmentVacuum n n x)))) = _
  rw [← fockProduct_vacuum, loss_create_product, parity_vacuum]
  simp only [map_add, loss_create_product, (fockSplit n n).apply_symm_apply]
  rw [hp, parity_vacuum]
  simp only [map_neg, LinearMap.neg_apply]
  simp only [oneLossCreation, twoLossCreation, LinearMap.sub_apply, LinearMap.comp_apply,
    exteriorSquare_wedge, pairEmbed_wedge, fockProduct_vacuum, Module.End.mul_apply, ContinuousLinearMap.coe_coe]
  abel

/-- The filtered parent interaction, with M on each of the two pair legs. -/
def filteredHamiltonian {ι : Type*} [Fintype ι] (w : ι → ℝ) (p : ι → PairSpace n) :
    Module.End ℂ (Space n) :=
  frameHamiltonian w (fun i => exteriorSquare M.toLinearMap (p i))

/-- Explicit one-environment output of the finite weighted decomposable frame. -/
def oneLossNoise {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (u v : ι → EuclideanSpace ℂ (Fin n)) : Space n →ₗ[ℂ] SplitSpace n n :=
  ∑ i, (w i : ℂ) • (oneLossCreation M (u i) (v i)).comp
    (pairAnnihilate (exteriorSquare M.toLinearMap (wedgePair (u i) (v i))))

/-- Explicit two-environment output. The pair embedding is normalized as in the CAR construction. -/
def twoLossNoise {ι : Type*} [Fintype ι] (w : ι → ℝ) (p : ι → PairSpace n) :
    Space n →ₗ[ℂ] SplitSpace n n :=
  ∑ i, (w i : ℂ) • (twoLossCreation M (p i)).comp
    (pairAnnihilate (exteriorSquare M.toLinearMap (p i)))

theorem oneLossCreation_sector (u v : EuclideanSpace ℂ (Fin n)) (x : Space n) :
    oneLossCreation M u v x ∈ environmentSector n n 1 := by
  apply (environmentSector n n 1).sub_mem
  · exact fockProduct_environmentSector (create_sector _ (sector_ket ∅)) _
  · exact fockProduct_environmentSector (create_sector _ (sector_ket ∅)) _

theorem twoLossCreation_sector (p : PairSpace n) (x : Space n) :
    twoLossCreation M p x ∈ environmentSector n n 2 :=
  fockProduct_environmentSector (pairEmbed_sector _) x

theorem oneLossNoise_sector {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (u v : ι → EuclideanSpace ℂ (Fin n)) (x : Space n) :
    oneLossNoise M w u v x ∈ environmentSector n n 1 := by
  simp only [oneLossNoise, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (oneLossCreation_sector M (u i) (v i) _)

theorem twoLossNoise_sector {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (p : ι → PairSpace n) (x : Space n) :
    twoLossNoise M w p x ∈ environmentSector n n 2 := by
  simp only [twoLossNoise, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (twoLossCreation_sector M (p i) _)

theorem environmentVacuum_environmentSector (x : Space n) :
    environmentVacuum n n x ∈ environmentSector n n 0 := by
  rw [← fockProduct_vacuum]
  exact fockProduct_environmentSector (sector_ket ∅) x

/-- The exact three-sector output, derived from CAR. No normalization or positivity
of the orbitals is required for this algebraic identity; it is also valid for real signed weights. -/
theorem loss_frame_vacuum {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (u v : ι → EuclideanSpace ℂ (Fin n)) (x : Space n) :
    fockSplit n n (lossHamiltonian M hM hc w (fun i => wedgePair (u i) (v i))
      ((fockSplit n n).symm (environmentVacuum n n x))) =
    environmentVacuum n n (filteredHamiltonian M w (fun i => wedgePair (u i) (v i)) x) +
      oneLossNoise M w u v x + twoLossNoise M w (fun i => wedgePair (u i) (v i)) x := by
  simp only [lossHamiltonian, frameHamiltonian, pairLift_frame, LinearMap.sum_apply,
    LinearMap.smul_apply, pairAnnihilate_adjoint, Module.End.mul_apply, map_sum, map_smul,
    loss_pairAnnihilate_vacuum, loss_pairCreate_vacuum]
  simp only [filteredHamiltonian, frameHamiltonian, pairLift_frame, oneLossNoise, twoLossNoise,
    LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, pairAnnihilate_adjoint,
    Module.End.mul_apply, map_sum, map_smul, smul_add, Finset.sum_add_distrib]

end VortexGap.Fermion
