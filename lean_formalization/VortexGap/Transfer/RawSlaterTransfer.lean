import VortexGap.Fermion.CountableRawPair
import VortexGap.Transfer.CountableSlater

noncomputable section
namespace VortexGap.Fermion
open VortexGap.Frame MeasureTheory

/-- Coherent raw amplitudes retain their phases when their orbital pairs
are orthonormalized, including on labels with vanishing wedge. -/
theorem countableRawExpansion_eq_slater {I : Type*} [Fintype I]
    (base : CountableTwoFrame) (c : I → ℂ) (u v : I → CountableOrbital) :
    ∑ i, c i • countableWedge (u i) (v i) =
      countableSlaterPair (fun i => c i * (pairColumnArea (u i) (v i) : ℂ))
        (fun i => orthogonalPairFrame base (u i) (v i)) :=
  alternating_expansion_normalize countableWedgeBilinear countableWedge_self base c u v

open scoped InnerProduct ENNReal ComplexOrder
open Filter
local instance : MeasurableSpace CountableOrbital := borel _
local instance : BorelSpace CountableOrbital := ⟨rfl⟩
private theorem rawColumn_measurable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (base : CountableTwoFrame) {u v : α → CountableOrbital}
    (hu : AEStronglyMeasurable u μ) (hv : AEStronglyMeasurable v μ) (j : Fin 2) :
    AEStronglyMeasurable (fun a => orthogonalPairFrame base (u a) (v a) (PiLp.single 2 j 1)) μ := by
  classical
  have unit {g : α → CountableOrbital} (h : StronglyMeasurable g) :
      StronglyMeasurable (fun a => unitColumn (g a)) :=
    ((Complex.continuous_ofReal.comp_stronglyMeasurable h.norm).measurable.inv.stronglyMeasurable).smul h
  have U := hu.stronglyMeasurable_mk
  have V := hv.stronglyMeasurable_mk
  have hi : StronglyMeasurable (fun a => inner ℂ (unitColumn (hu.mk u a)) (hv.mk v a)) := (unit U).inner V
  have R : StronglyMeasurable (fun a => residualColumn (hu.mk u a) (hv.mk v a)) :=
    V.sub (hi.smul (unit U))
  have H : StronglyMeasurable (fun a => orthogonalPairFrame base (hu.mk u a) (hv.mk v a) (PiLp.single 2 j 1)) := by
    simp_rw [orthogonalPairFrame_column]
    apply StronglyMeasurable.ite ((U.measurableSet_eq_fun stronglyMeasurable_const).compl.inter
      (R.measurableSet_eq_fun stronglyMeasurable_const).compl) _ stronglyMeasurable_const
    by_cases hj : j = 0
    · simpa [hj] using unit U
    · simpa [hj] using unit R
  apply H.aestronglyMeasurable.congr
  filter_upwards [hu.ae_eq_mk,hv.ae_eq_mk] with a h1 h2
  rw [h1,h2]

variable {α I : Type*} [Fintype I] [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    (base : CountableTwoFrame) (c : α → I → ℂ) (u v : α → I → CountableOrbital)
local notation "rawPair" => (fun a => ∑ i, c a i • countableWedge (u a i) (v a i))
local notation "amp" => (fun a i => c a i * (pairColumnArea (u a i) (v a i) : ℂ))
local notation "cols" => (fun a i => orthogonalPairFrame base (u a i) (v a i))

/-- Transfer on the complete countable orbital space for a coherent finite
sum of raw wedges per label. The Schur test is on the actual normalized
columns and their area-weighted amplitudes. -/
theorem countableRawSlater_transfer
    (hp : ∀ q, MemLp (fun a => inner ℂ (rawPair a) q) 2 μ)
    (β : ℝ) (hβ : 0 ≤ β)
    (hb : ∀ q, (∫ a, ‖inner ℂ (rawPair a) q‖^2 ∂μ) ≤ β * ‖q‖^2)
    (M : CountableOrbital →L[ℂ] CountableOrbital) (hM : 0 ≤ M) (hc : ‖M‖ ≤ 1)
    (hu : ∀ i, AEStronglyMeasurable (fun a => u a i) μ)
    (hv : ∀ i, AEStronglyMeasurable (fun a => v a i) μ)
    (hl : ∀ n i, MemLp (fun a => amp a i) 2 (μ.restrict (spanningSets μ n)))
    (ω : α → ℝ) (hω : ∀ a, 0 < ω a) (hωm : AEStronglyMeasurable ω μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hrowInt : ∀ᵐ a ∂μ, Integrable (fun b => countableSlaterKernel (amp a) (amp b) (cols a) (cols b) * ω b) μ)
    (hrow : ∀ᵐ a ∂μ, (∫ b, countableSlaterKernel (amp a) (amp b) (cols a) (cols b) * ω b ∂μ) ≤ C * ω a)
    (γ : ℝ) (N : ℕ)
    (hgap : ∀ k ≤ N,
      (countablePairLift k (countableContinuousPairOperator μ rawPair hp β hβ hb) *
        countablePairLift k (countableContinuousPairOperator μ rawPair hp β hβ hb) -
        (γ : ℂ) • countablePairLift k (countableContinuousPairOperator μ rawPair hp β hβ hb)).IsPositive) :
    let H := countableContinuousFilteredHamiltonian μ rawPair hp β hβ hb M hM N
    (H*H - ((γ-C*‖1-M^2‖-β*‖1-M^2‖^2 : ℝ) : ℂ) • H).IsPositive :=
  countableSlater_transfer μ rawPair hp β hβ hb M hM hc amp cols
    (fun a => countableRawExpansion_eq_slater base (c a) (u a) (v a)) hl
    (fun i j => rawColumn_measurable base (hu i) (hv i) j)
    ω hω hωm C hC hrowInt hrow γ N hgap

end VortexGap.Fermion
