import VortexGap.Examples.PlaneWeakCosine
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

local notation "H" => Lp ℂ 2 (volume : Measure ℂ)

/-- Maximal graph of complex-coordinate multiplication on the ambient plane. -/
def planeCoordinateGraph : Submodule ℂ (H × H) where
  carrier := {p | ∀ᵐ z ∂volume, p.2 z = z * p.1 z}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure ℂ)] with z hz
    change (0 : H) z = z * (0 : H) z
    simp
  add_mem' := by
    intro p q hp hq
    filter_upwards [hp, hq, Lp.coeFn_add p.1 q.1, Lp.coeFn_add p.2 q.2] with z hp hq ha hb
    change (p.2 + q.2) z = z * (p.1 + q.1) z
    simp only [ha, hb, Pi.add_apply, hp, hq, mul_add]
  smul_mem' := by
    intro c p hp
    filter_upwards [hp, Lp.coeFn_smul c p.1, Lp.coeFn_smul c p.2] with z hp ha hb
    change (c • p.2) z = z * (c • p.1) z
    simp only [ha, hb, Pi.smul_apply, smul_eq_mul, hp]
    ring

theorem planeCoordinateGraph_closed : IsClosed (planeCoordinateGraph : Set (H × H)) := by
  apply IsSeqClosed.isClosed
  intro u p hu hlim
  have h₁ : Tendsto (fun n => (u n).1) atTop (𝓝 p.1) := (continuous_fst.tendsto p).comp hlim
  have h₂ : Tendsto (fun n => (u n).2) atTop (𝓝 p.2) := (continuous_snd.tendsto p).comp hlim
  obtain ⟨a, ha, hA⟩ := (tendstoInMeasure_of_tendsto_Lp h₁).exists_seq_tendsto_ae
  obtain ⟨b, hb, hB⟩ := (tendstoInMeasure_of_tendsto_Lp (h₂.comp ha.tendsto_atTop)).exists_seq_tendsto_ae
  have hrel : ∀ᵐ z ∂volume, ∀ n, (u n).2 z = z * (u n).1 z := ae_all_iff.mpr hu
  filter_upwards [hA, hB, hrel] with z hx hy h
  apply tendsto_nhds_unique hy
  simpa only [Function.comp_apply, h] using (hx.comp hb.tendsto_atTop).const_mul z

/-- The domain consists of exactly the square-integrable functions with zψ square integrable. -/
def planeCoordinateDomain : Submodule ℂ H :=
  planeCoordinateGraph.map (LinearMap.fst ℂ H H)

theorem planeCoordinateDomain_iff (x : H) :
    x ∈ planeCoordinateDomain ↔ MemLp (fun z => z * x z) 2 volume := by
  constructor
  · rintro ⟨⟨u,v⟩, hv, rfl⟩
    exact (Lp.memLp v).ae_eq hv
  · intro hx
    exact ⟨(x,hx.toLp _), hx.coeFn_toLp, rfl⟩

def planeCoordinateMul (x : planeCoordinateDomain) : H :=
  ((planeCoordinateDomain_iff x.val).mp x.property).toLp _

theorem planeCoordinateMul_coe (x : planeCoordinateDomain) :
    planeCoordinateMul x =ᵐ[volume] fun z => z * x.val z := MemLp.coeFn_toLp _

theorem planeCoordinateGraph_iff (x y : H) :
    (x,y) ∈ planeCoordinateGraph ↔ ∃ h : x ∈ planeCoordinateDomain, planeCoordinateMul ⟨x,h⟩ = y := by
  constructor
  · intro h
    have hx : x ∈ planeCoordinateDomain := ⟨(x,y), h, rfl⟩
    exact ⟨hx, Lp.ext ((planeCoordinateMul_coe ⟨x,hx⟩).trans (Filter.EventuallyEq.symm h))⟩
  · rintro ⟨hx,rfl⟩
    exact planeCoordinateMul_coe _

private theorem boundedMultiply_memLp (f : ℂ →ᵇ ℂ) (x : H) :
    MemLp (fun z => f z * x z) 2 volume := by
  apply (Lp.memLp x).of_le_mul (c := ‖f‖)
    (f.continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable x))
  exact Eventually.of_forall fun z => by
    change ‖f z * x z‖ ≤ ‖f‖ * ‖x z‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm z) (norm_nonneg _)

def planeAmbientMultiply (f : ℂ →ᵇ ℂ) (x : H) : H := (boundedMultiply_memLp f x).toLp _

theorem planeAmbientMultiply_coe (f : ℂ →ᵇ ℂ) (x : H) :
    planeAmbientMultiply f x =ᵐ[volume] fun z => f z * x z := MemLp.coeFn_toLp _

theorem planeCoordinateGraph_multiply (f : ℂ →ᵇ ℂ) (x y : H)
    (h : (x,y) ∈ planeCoordinateGraph) :
    (planeAmbientMultiply f x, planeAmbientMultiply f y) ∈ planeCoordinateGraph := by
  change ∀ᵐ z ∂volume, planeAmbientMultiply f y z = z * planeAmbientMultiply f x z
  change ∀ᵐ z ∂volume, y z = z * x z at h
  filter_upwards [planeAmbientMultiply_coe f x, planeAmbientMultiply_coe f y, h] with z hx hy hz
  change y z = z * x z at hz
  rw [hx, hy, hz]
  ring

theorem planeCoordinateDomain_multiply (f : ℂ →ᵇ ℂ) (x : planeCoordinateDomain) :
    planeAmbientMultiply f x ∈ planeCoordinateDomain :=
  ⟨_, planeCoordinateGraph_multiply f x (planeCoordinateMul x) (planeCoordinateMul_coe x), rfl⟩

theorem planeCoordinateMul_multiply (f : ℂ →ᵇ ℂ) (x : planeCoordinateDomain) :
    planeCoordinateMul ⟨planeAmbientMultiply f x, planeCoordinateDomain_multiply f x⟩ =
      planeAmbientMultiply f (planeCoordinateMul x) :=
  ((planeCoordinateGraph_iff _ _).mp
    (planeCoordinateGraph_multiply f x (planeCoordinateMul x) (planeCoordinateMul_coe x))).choose_spec

/-- For multipliers bounded away from zero the converse holds on the entire ambient space. -/
theorem planeCoordinateDomain_multiply_iff (f : ℂ →ᵇ ℂ) (m : ℝ) (hm : 0 < m)
    (hlo : ∀ᵐ z ∂volume, m ≤ ‖f z‖) (x : H) :
    planeAmbientMultiply f x ∈ planeCoordinateDomain ↔ x ∈ planeCoordinateDomain := by
  refine ⟨fun h => (planeCoordinateDomain_iff _).mpr ?_, fun h => planeCoordinateDomain_multiply f ⟨x,h⟩⟩
  apply ((planeCoordinateDomain_iff _).mp h).of_le_mul (c := m⁻¹)
    (continuous_id.aestronglyMeasurable.mul (Lp.aestronglyMeasurable x))
  filter_upwards [hlo, planeAmbientMultiply_coe f x] with z hz he
  change ‖z * x z‖ ≤ m⁻¹ * ‖z * planeAmbientMultiply f x z‖
  rw [he, mul_left_comm z (f z), norm_mul (f z) (z * x z), ← mul_assoc]
  exact le_mul_of_one_le_left (norm_nonneg (z * x z)) ((inv_mul_cancel₀ hm.ne').symm.le.trans
    (mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr hm.le)))

theorem planeScalarEmbedding_coordinate_iff (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (m : ℝ) (hm : 0 < m) (hlo : ∀ᵐ z ∂volume, m ≤ ‖f z‖) (v : CountableOrbital) :
    planeScalarEmbedding ell hell f v ∈ planeCoordinateDomain ↔
      planeLLLEmbedding ell hell v ∈ planeCoordinateDomain := by
  have he : planeScalarEmbedding ell hell f v = planeAmbientMultiply f (planeLLLEmbedding ell hell v) :=
    Lp.ext ((planeScalarEmbedding_is_multiplication ell hell f v).trans (planeAmbientMultiply_coe _ _).symm)
  rw [he, planeCoordinateDomain_multiply_iff f m hm hlo]

theorem planeWeakCos_coordinate_iff (ell : ℝ) (hell : 0 < ell) (v : CountableOrbital) :
    planeScalarEmbedding ell hell planeWeakCos v ∈ planeCoordinateDomain ↔
      planeLLLEmbedding ell hell v ∈ planeCoordinateDomain := by
  apply planeScalarEmbedding_coordinate_iff _ _ _ (9999 / 10000) (by norm_num)
  exact Eventually.of_forall fun z => by rw [planeWeakCos_norm]; exact (planeWeakCosValue_bounds z).1

/-- Multiplying a normalized planar LLL orbital by z raises its index. -/
theorem planeWavefunction_coordinate_raise (ell : ℝ) (hell : 0 < ell) (z : ℂ) (n : ℕ) :
    z * planeWavefunction ell z n =
      ((Real.sqrt 2 * ell * Real.sqrt (n+1 : ℝ) : ℝ) : ℂ) * planeWavefunction ell z (n+1) := by
  have hscale : ((Real.sqrt 2 * ell : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (Real.sqrt 2 * ell : ℝ) ≠ 0)
  have hz : ((Real.sqrt 2 * ell : ℝ) : ℂ) * planeCoordinate ell z = z := by
    unfold planeCoordinate
    field_simp
  have hr : (Real.sqrt (n+1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : Real.sqrt (n+1 : ℝ) ≠ 0)
  simp only [planeWavefunction, planeBargmannCoeff, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, Real.sqrt_mul (by positivity : 0 ≤ (n:ℝ)+1), Complex.ofReal_mul, pow_succ]
  conv_lhs => lhs; rw [← hz]
  simp only [Complex.ofReal_mul]
  field_simp

/-- A core raising identity in the actual deformed band for every bounded f, including nodal f. -/
theorem planeCoordinateGraph_band_basis (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ) (n : ℕ) :
    (planeScalarEmbedding ell hell f (orbitalKet n),
      ((Real.sqrt 2 * ell * Real.sqrt (n+1 : ℝ) : ℝ) : ℂ) •
        planeScalarEmbedding ell hell f (orbitalKet (n+1))) ∈ planeCoordinateGraph := by
  let c : ℂ := ((Real.sqrt 2 * ell * Real.sqrt (n+1 : ℝ) : ℝ) : ℂ)
  change ∀ᵐ z ∂volume, (c • planeScalarEmbedding ell hell f (orbitalKet (n+1))) z =
    z * planeScalarEmbedding ell hell f (orbitalKet n) z
  filter_upwards [Lp.coeFn_smul c (planeScalarEmbedding ell hell f (orbitalKet (n+1))),
    planeScalarEmbedding_is_multiplication ell hell f (orbitalKet n),
    planeScalarEmbedding_is_multiplication ell hell f (orbitalKet (n+1)),
    planeLLLEmbedding_basis ell hell n, planeLLLEmbedding_basis ell hell (n+1)] with z hc h₁ h₂ hb hd
  simp only [hc, Pi.smul_apply, smul_eq_mul, h₁, h₂, hb, hd]
  rw [mul_left_comm z, planeWavefunction_coordinate_raise ell hell]
  ring

end VortexGap.Fermion
