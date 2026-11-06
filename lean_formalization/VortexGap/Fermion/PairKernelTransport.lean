import VortexGap.Fermion.PairCovariance
import VortexGap.Frame.ContinuousPair
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory Filter
open scoped ComplexConjugate ENNReal
variable {α : Type*} [MeasurableSpace α] {n : ℕ} (μ : Measure α)

theorem continuousPairHam_zero_iff_ae (p : α → PairSpace n) (hp : MemLp p 2 μ) (x : Space n) :
    continuousFrameHamiltonian μ p x = 0 ↔ ∀ᵐ g ∂μ, pairAnnihilate (p g) x = 0 := by
  let A := continuousFrameAnalysis μ p hp
  have he := continuousFrameAnalysis_ae μ p hp x
  change (A x) =ᵐ[μ] _ at he
  have hz := Lp.coeFn_zero (Space n) 2 μ
  constructor
  · intro h
    have hn := continuousFrameAnalysis_energy μ p hp x
    rw [h,inner_zero_right,Complex.zero_re] at hn
    have h0 : A x = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
    rw [h0] at he
    filter_upwards [he,hz] with g hg hg0
    exact hg.symm.trans hg0
  · intro h
    have h0 : A x = 0 := by
      apply Lp.ext
      filter_upwards [he,h,hz] with g hg hg' hg0
      exact (hg.trans hg').trans hg0.symm
    rw [← continuousFrameAnalysis_gram μ p hp,ContinuousLinearMap.comp_apply]
    change A.adjoint (A x) = 0
    simp [h0]

theorem continuousPairHam_kernel_transport (p : α → PairSpace n) (hp : MemLp p 2 μ)
    (R S : Module.End ℂ (EuclideanSpace ℂ (Fin n))) (hSR : S.comp R = LinearMap.id)
    (w : α → ℂ) (hw : ∀ᵐ g ∂μ, w g ≠ 0)
    (hq : MemLp (fun g => w g • exteriorSquare R.adjoint (p g)) 2 μ) (x : Space n) :
    continuousFrameHamiltonian μ (fun g => w g • exteriorSquare R.adjoint (p g)) x = 0 ↔
      continuousFrameHamiltonian μ p (fockMap R x) = 0 := by
  have hi : Function.Injective (fockMap R) := by
    apply Function.LeftInverse.injective (g := fockMap S)
    intro y
    have h := congrArg (fun T : Module.End ℂ (Space n) => T y) (fockMap_comp R S)
    simpa [hSR,fockMap_id] using h.symm
  rw [continuousPairHam_zero_iff_ae μ _ hq,continuousPairHam_zero_iff_ae μ _ hp]
  apply Filter.eventually_congr
  filter_upwards [hw] with g hg
  have he := congrArg (fun T : Module.End ℂ (Space n) => T x) (fockMap_pairAnnihilate R (p g))
  change pairAnnihilate (p g) (fockMap R x) = fockMap R (pairAnnihilate (exteriorSquare R.adjoint (p g)) x) at he
  rw [he,pairAnnihilate_smul,LinearMap.smul_apply,smul_eq_zero]
  have hn : conj (w g) ≠ 0 := by simpa using hg
  simp only [hn,false_or]
  exact ⟨fun h => by rw [h,map_zero], fun h => hi (h.trans (map_zero (fockMap R)).symm)⟩
def continuousSectorZeroSpace (p : α → PairSpace n) (N : ℕ) : Submodule ℂ (particleSector n N) :=
  LinearMap.ker ((continuousFrameHamiltonian μ p).toLinearMap.comp (particleSector n N).subtype)

theorem continuousSectorZeroSpace_map (p : α → PairSpace n) (hp : MemLp p 2 μ)
    (R S : Module.End ℂ (EuclideanSpace ℂ (Fin n))) (hSR : S.comp R = LinearMap.id)
    (hRS : R.comp S = LinearMap.id) (w : α → ℂ) (hw : ∀ᵐ g ∂μ, w g ≠ 0)
    (hq : MemLp (fun g => w g • exteriorSquare R.adjoint (p g)) 2 μ) (N : ℕ) :
    let q := fun g => w g • exteriorSquare R.adjoint (p g)
    (continuousSectorZeroSpace μ q N).map (exteriorPower R N) = continuousSectorZeroSpace μ p N := by
  have hz (x : particleSector n N) :
      x ∈ continuousSectorZeroSpace μ (fun g => w g • exteriorSquare R.adjoint (p g)) N ↔
        exteriorPower R N x ∈ continuousSectorZeroSpace μ p N := by
    have h := continuousPairHam_kernel_transport μ p hp R S hSR w hw hq (x : Space n)
    rw [fockMap_on_sector] at h
    exact h
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact (hz y).mp hy
  · intro hx
    have he : exteriorPower R N (exteriorPower S N x) = x := by
      rw [← LinearMap.comp_apply,← exteriorPower_comp,hRS,exteriorPower_id,LinearMap.id_apply]
    exact ⟨exteriorPower S N x,(hz _).mpr (he.symm ▸ hx),he⟩

theorem continuousSectorZeroSpace_finrank (p : α → PairSpace n) (hp : MemLp p 2 μ)
    (R S : Module.End ℂ (EuclideanSpace ℂ (Fin n))) (hSR : S.comp R = LinearMap.id)
    (hRS : R.comp S = LinearMap.id) (w : α → ℂ) (hw : ∀ᵐ g ∂μ, w g ≠ 0)
    (hq : MemLp (fun g => w g • exteriorSquare R.adjoint (p g)) 2 μ) (N : ℕ) :
    let q := fun g => w g • exteriorSquare R.adjoint (p g)
    Module.finrank ℂ (continuousSectorZeroSpace μ q N) = Module.finrank ℂ (continuousSectorZeroSpace μ p N) := by
  dsimp only
  rw [← continuousSectorZeroSpace_map μ p hp R S hSR hRS w hw hq N]
  have hi : Function.Injective (exteriorPower R N) := by
    apply Function.LeftInverse.injective (g := exteriorPower S N)
    intro x
    rw [← LinearMap.comp_apply,← exteriorPower_comp,hSR,exteriorPower_id,LinearMap.id_apply]
  exact (Submodule.equivMapOfInjective _ hi _).finrank_eq
end VortexGap.Fermion
