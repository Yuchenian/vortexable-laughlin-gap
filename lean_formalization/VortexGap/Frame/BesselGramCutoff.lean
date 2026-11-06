import VortexGap.Frame.L2CutoffLimits
noncomputable section
set_option autoImplicit false
namespace VortexGap.Frame
open MeasureTheory Filter
open scoped InnerProduct ENNReal Topology ComplexOrder
variable {α E F : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  (μ : Measure α)

/-- The actual Gram operator obtained by restricting the analysis labels. -/
def l2GramCutoff (A : E →L[ℂ] Lp F 2 μ) (s : Set α) (hs : MeasurableSet s) :
    E →L[ℂ] E := A.adjoint.comp ((l2Cutoff μ s hs).comp A)

theorem l2GramCutoff_positive (A : E →L[ℂ] Lp F 2 μ) (s : Set α) (hs : MeasurableSet s) :
    (l2GramCutoff μ A s hs).IsPositive :=
  (l2Cutoff_positive μ s hs).adjoint_conj A

theorem l2GramCutoff_complement (A : E →L[ℂ] Lp F 2 μ) (s : Set α) (hs : MeasurableSet s) :
    A.adjoint.comp A - l2GramCutoff μ A s hs = l2GramCutoff μ A sᶜ hs.compl := by
  apply ContinuousLinearMap.ext
  intro x
  change A.adjoint (A x) - A.adjoint (l2Cutoff μ s hs (A x)) =
    A.adjoint (l2Cutoff μ sᶜ hs.compl (A x))
  rw [l2Cutoff_compl μ s hs]
  simp

theorem l2GramCutoff_le (A : E →L[ℂ] Lp F 2 μ) (s : Set α) (hs : MeasurableSet s) :
    l2GramCutoff μ A s hs ≤ A.adjoint.comp A := by
  rw [ContinuousLinearMap.le_def, l2GramCutoff_complement]
  exact l2GramCutoff_positive μ A sᶜ hs.compl

theorem l2GramCutoff_norm_le (A : E →L[ℂ] Lp F 2 μ) (s : Set α) (hs : MeasurableSet s) :
    ‖l2GramCutoff μ A s hs‖ ≤ ‖A‖^2 := by
  let P : Lp F 2 μ →L[ℂ] Lp F 2 μ := l2Cutoff μ s hs
  have hp : ‖P‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun f => by simpa only [one_mul] using l2Cutoff_norm_le μ s hs f)
  change ‖A.adjoint.comp (P.comp A)‖ ≤ ‖A‖^2
  calc
    _ ≤ ‖A.adjoint‖ * ‖P.comp A‖ := A.adjoint.opNorm_comp_le _
    _ ≤ ‖A.adjoint‖ * (‖P‖ * ‖A‖) :=
      mul_le_mul_of_nonneg_left (P.opNorm_comp_le A) (norm_nonneg A.adjoint)
    _ ≤ ‖A.adjoint‖ * (1 * ‖A‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp (norm_nonneg A)) (norm_nonneg A.adjoint)
    _ = _ := by rw [ContinuousLinearMap.adjoint.norm_map]; ring

theorem l2GramCutoff_tendsto (A : E →L[ℂ] Lp F 2 μ)
    (s : ℕ → Set α) (hs : ∀ n, MeasurableSet (s n))
    (hm : Monotone s) (hu : ⋃ n, s n = Set.univ) (x : E) :
    Tendsto (fun n => l2GramCutoff μ A (s n) (hs n) x) atTop (𝓝 (A.adjoint (A x))) :=
  (A.adjoint.continuous.tendsto (A x)).comp (l2Cutoff_tendsto μ s hs hm hu (A x))

theorem l2GramCutoff_spanning_tendsto [SigmaFinite μ] (A : E →L[ℂ] Lp F 2 μ) (x : E) :
    Tendsto (fun n => l2GramCutoff μ A (spanningSets μ n) (measurableSet_spanningSets μ n) x)
      atTop (𝓝 (A.adjoint (A x))) :=
  (A.adjoint.continuous.tendsto (A x)).comp (l2Cutoff_spanning_tendsto μ (A x))

variable (T : α → E →L[ℂ] F) (hT : ∀ x, MemLp (fun a => T a x) 2 μ)
  (β : ℝ) (hβ : 0 ≤ β) (hb : ∀ x : E, (∫ a, ‖T a x‖^2 ∂μ) ≤ β * ‖x‖^2)

/-- The constructed cutoff has the original restricted frame integral as its matrix element. -/
theorem besselGramCutoff_inner (s : Set α) (hs : MeasurableSet s) (x y : E) :
    inner ℂ x (l2GramCutoff μ (besselAnalysis μ T hT β hβ hb) s hs y) =
      ∫ a in s, inner ℂ (T a x) (T a y) ∂μ := by
  change inner ℂ x ((besselAnalysis μ T hT β hβ hb).adjoint
    (l2Cutoff μ s hs (besselAnalysis μ T hT β hβ hb y))) = _
  rw [ContinuousLinearMap.adjoint_inner_right, L2.inner_def, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [besselAnalysis_ae μ T hT β hβ hb x,
    besselAnalysis_ae μ T hT β hβ hb y,
    l2Cutoff_ae μ s hs (besselAnalysis μ T hT β hβ hb y)] with a hx hy hp
  rw [hx,hp]
  by_cases h : a ∈ s <;> simp [h,hy]

theorem besselGramCutoff_norm_le (s : Set α) (hs : MeasurableSet s) :
    ‖l2GramCutoff μ (besselAnalysis μ T hT β hβ hb) s hs‖ ≤ β := by
  apply (l2GramCutoff_norm_le μ _ s hs).trans
  have h := (sq_le_sq₀ (norm_nonneg (besselAnalysis μ T hT β hβ hb))
    (Real.sqrt_nonneg β)).mpr (besselAnalysis_opNorm_le μ T hT β hβ hb)
  simpa only [Real.sq_sqrt hβ] using h
end VortexGap.Frame
