import VortexGap.Frame.BesselAnalysis
noncomputable section
set_option autoImplicit false
namespace VortexGap.Frame
open MeasureTheory
open scoped InnerProduct ENNReal
variable {α E : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (μ : Measure α) (s : Set α) (hs : MeasurableSet s)

def l2CutoffLinear : Lp E 2 μ →ₗ[ℂ] Lp E 2 μ where
  toFun f := ((Lp.memLp f).indicator hs).toLp (s.indicator f)
  map_add' f g := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    filter_upwards [Lp.coeFn_add f g] with a ha
    by_cases h : a ∈ s
    · simp only [Pi.add_apply, Pi.smul_apply, RingHom.id_apply, Set.indicator_of_mem h]
      exact ha
    · simp [h]
  map_smul' z f := by
    rw [← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    filter_upwards [Lp.coeFn_smul z f] with a ha
    by_cases h : a ∈ s
    · simp only [Pi.add_apply, Pi.smul_apply, RingHom.id_apply, Set.indicator_of_mem h]
      exact ha
    · simp [h]

theorem l2CutoffLinear_ae (f : Lp E 2 μ) :
    l2CutoffLinear μ s hs f =ᵐ[μ] s.indicator f :=
  ((Lp.memLp f).indicator hs).coeFn_toLp

theorem l2CutoffLinear_norm_le (f : Lp E 2 μ) :
    ‖l2CutoffLinear μ s hs f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [l2CutoffLinear_ae μ s hs f] with a ha
  rw [ha]
  by_cases h : a ∈ s <;> simp [h]

/-- Multiplication by a measurable label indicator on the actual quotient L2 space. -/
def l2Cutoff : Lp E 2 μ →L[ℂ] Lp E 2 μ :=
  (l2CutoffLinear μ s hs).mkContinuous 1
    (fun f => by simpa only [one_mul] using l2CutoffLinear_norm_le μ s hs f)

theorem l2Cutoff_ae (f : Lp E 2 μ) :
    l2Cutoff μ s hs f =ᵐ[μ] s.indicator f := l2CutoffLinear_ae μ s hs f

theorem l2Cutoff_norm_le (f : Lp E 2 μ) :
    ‖l2Cutoff μ s hs f‖ ≤ ‖f‖ := l2CutoffLinear_norm_le μ s hs f

theorem l2Cutoff_idempotent :
    (l2Cutoff μ s hs : Lp E 2 μ →L[ℂ] Lp E 2 μ) * l2Cutoff μ s hs = l2Cutoff μ s hs := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [l2Cutoff_ae μ s hs (l2Cutoff μ s hs f), l2Cutoff_ae μ s hs f] with a ha hb
  change l2Cutoff μ s hs (l2Cutoff μ s hs f) a = l2Cutoff μ s hs f a
  rw [ha,hb]
  by_cases h : a ∈ s <;> simp [h,hb]

theorem l2Cutoff_adjoint :
    (l2Cutoff μ s hs : Lp E 2 μ →L[ℂ] Lp E 2 μ).adjoint = l2Cutoff μ s hs := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro f g
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [l2Cutoff_ae μ s hs f, l2Cutoff_ae μ s hs g] with a hf hg
  rw [hf,hg]
  by_cases h : a ∈ s <;> simp [h]

theorem l2Cutoff_positive :
    (l2Cutoff μ s hs : Lp E 2 μ →L[ℂ] Lp E 2 μ).IsPositive := by
  have h := ContinuousLinearMap.isPositive_adjoint_comp_self
    (l2Cutoff μ s hs : Lp E 2 μ →L[ℂ] Lp E 2 μ)
  rw [l2Cutoff_adjoint] at h
  change ((l2Cutoff μ s hs : Lp E 2 μ →L[ℂ] Lp E 2 μ) * l2Cutoff μ s hs).IsPositive at h
  rw [l2Cutoff_idempotent] at h
  exact h

theorem l2Cutoff_compl :
    (l2Cutoff μ sᶜ hs.compl : Lp E 2 μ →L[ℂ] Lp E 2 μ) = 1-l2Cutoff μ s hs := by
  apply ContinuousLinearMap.ext
  intro f
  change l2Cutoff μ sᶜ hs.compl f = f-l2Cutoff μ s hs f
  apply Lp.ext
  filter_upwards [l2Cutoff_ae μ sᶜ hs.compl f, l2Cutoff_ae μ s hs f,
    Lp.coeFn_sub f (l2Cutoff μ s hs f)] with a hc hs' hd
  rw [hc,hd]
  change sᶜ.indicator f a = f a-l2Cutoff μ s hs f a
  rw [hs']
  by_cases h : a ∈ s <;> simp [h]
end VortexGap.Frame
