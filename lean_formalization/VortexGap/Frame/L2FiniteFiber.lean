import VortexGap.Frame.ContinuousAnalysis
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section
set_option autoImplicit false
namespace VortexGap.Frame
open MeasureTheory
open scoped InnerProduct ENNReal BigOperators

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

theorem l2_norm_sq_integral {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (f : Lp E 2 μ) :
    ‖f‖^2 = ∫ a, ‖f a‖^2 ∂μ := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner f f)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun a => (norm_sq_eq_re_inner (𝕜 := ℂ) (f a)).symm

variable {ι : Type*} [Fintype ι]

/-- Coordinate projection on an actual vector-valued quotient L2 space. -/
def l2Coordinate (i : ι) : Lp (EuclideanSpace ℂ ι) 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (PiLp.proj (𝕜 := ℂ) 2 (fun _ : ι => ℂ) i).compLpL 2 μ

theorem l2Coordinate_ae (i : ι) (f : Lp (EuclideanSpace ℂ ι) 2 μ) :
    l2Coordinate μ i f =ᵐ[μ] fun a => f a i :=
  (PiLp.proj (𝕜 := ℂ) 2 (fun _ : ι => ℂ) i).coeFn_compLpL f

theorem l2Coordinate_memLp (i : ι) (f : Lp (EuclideanSpace ℂ ι) 2 μ) :
    MemLp (fun a => f a i) 2 μ :=
  (PiLp.proj (𝕜 := ℂ) 2 (fun _ : ι => ℂ) i).comp_memLp f

theorem l2Coordinate_square_integrable (i : ι) (f : Lp (EuclideanSpace ℂ ι) 2 μ) :
    Integrable (fun a => ‖f a i‖^2) μ :=
  (memLp_two_iff_integrable_sq_norm (l2Coordinate_memLp μ i f).aestronglyMeasurable).mp
    (l2Coordinate_memLp μ i f)

theorem l2Coordinate_norm_sq (i : ι) (f : Lp (EuclideanSpace ℂ ι) 2 μ) :
    ‖l2Coordinate μ i f‖^2 = ∫ a, ‖f a i‖^2 ∂μ := by
  rw [l2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [l2Coordinate_ae μ i f] with a ha
  rw [ha]

/-- Finite coordinate Parseval; there is no dimension factor. -/
theorem l2Finite_norm_sq (f : Lp (EuclideanSpace ℂ ι) 2 μ) :
    ‖f‖^2 = ∑ i, ‖l2Coordinate μ i f‖^2 := by
  rw [l2_norm_sq_integral]
  simp_rw [EuclideanSpace.norm_sq_eq]
  rw [integral_finsetSum _ (fun i _ => l2Coordinate_square_integrable μ i f)]
  exact Finset.sum_congr rfl fun i _ => (l2Coordinate_norm_sq μ i f).symm

end VortexGap.Frame
