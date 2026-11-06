import VortexGap.Fermion.SectorWaveEvaluation
import VortexGap.Physical.SphereLaughlinKernel
import Mathlib.MeasureTheory.Integral.Pi

noncomputable section
namespace VortexGap.Fermion
open OAI.Laughlin.Rotation VortexGap.SpherePolynomial
variable {q N : ℕ}

def sphereReferenceWave (x : particleSector (q+1) N) (z : Fin N → SourceSU2) :=
  sectorWave (fun g i => sphereOrbitalValue q (PiLp.single 2 i (1:ℂ)) g) x z

def sphereDeformedWave (f : SourceSU2 → ℂ) (hf : Continuous f)
    (x : particleSector (q+1) N) (z : Fin N → SourceSU2) :=
  let R := gramInvSqrt (sphereScalarMap q f hf)
  sectorWave (fun g i => sphereScalarRow q f g (R (PiLp.single 2 i 1))) x z

theorem sphereDeformedWave_gram (f : SourceSU2 → ℂ) (hf : Continuous f)
    (a b : ℝ) (ha : 0 < a) (hl : ∀ g, a ≤ ‖f g‖^2) (hu : ∀ g, ‖f g‖^2 ≤ b)
    (x : particleSector (q+1) N) (z : Fin N → SourceSU2) :
    let S := (CFC.sqrt (gramOperator (sphereScalarMap q f hf))).toLinearMap
    sphereDeformedWave f hf (exteriorPower S N x) z = (∏ i, f (z i)) * sphereReferenceWave x z := by
  let F := sphereScalarMap q f hf
  let R := gramInvSqrt F
  let S := CFC.sqrt (gramOperator F)
  have hF := gramOperator_strict F a ha (sphereScalarGram_bounds q f hf a b ha.le hl hu).1
  have hRS : R ∘L S = ContinuousLinearMap.id ℂ _ := gramInvSqrt_left F hF
  change sectorWave (fun g i => sphereScalarRow q f g (R (PiLp.single 2 i 1)))
    (exteriorPower S.toLinearMap N x) z = _
  rw [sectorWave_exterior]
  have he (g : SourceSU2) (j : Fin (q+1)) :
      ∑ k, S (PiLp.single 2 j 1) k * sphereScalarRow q f g (R (PiLp.single 2 k 1)) =
      f g * sphereOrbitalValue q (PiLp.single 2 j (1:ℂ)) g := by
    let v := S (PiLp.single 2 j 1)
    have hv : ∑ k, v k • PiLp.single 2 k (1:ℂ) = v := by ext i; simp [Pi.single_apply]
    have hh := congrArg (fun w => sphereScalarRow q f g (R w)) hv
    simp only [map_sum,map_smul,smul_eq_mul] at hh
    have heval := DFunLike.congr_fun hRS (PiLp.single 2 j 1)
    change R v = PiLp.single 2 j 1 at heval
    rw [heval,sphereScalarRow_apply] at hh
    exact hh
  change sectorWave (fun g j => ∑ k, S (PiLp.single 2 j 1) k *
    sphereScalarRow q f g (R (PiLp.single 2 k 1))) x z = _
  simp_rw [he]
  exact sectorWave_multiply _ _ _ _

theorem sphere_laughlin_product_generator (n N : ℕ) (hQ : 3*((N+2)-1) = n+1)
    (f : SourceSU2 → ℂ) (hf : Continuous f) (a b : ℝ)
    (ha : 0 < a) (hl : ∀ g, a ≤ ‖f g‖^2) (hu : ∀ g, ‖f g‖^2 ≤ b) :
    ∃ l y : particleSector (n+2) (N+2), sectorPoly l = laughlin (N+2) ∧
      LinearMap.ker (sphereSectorHam n (N+2) (spherePhysicalPair n f hf)).toLinearMap = ℂ ∙ y ∧
      ∀ z, sphereDeformedWave f hf y z = (∏ i, f (z i)) * sphereReferenceWave l z := by
  obtain ⟨l,_,hlp,hker⟩ := sphere_deformed_laughlin_kernel n N hQ f hf a b ha hl hu
  exact ⟨l,_,hlp,hker,sphereDeformedWave_gram f hf a b ha hl hu l⟩

end VortexGap.Fermion
end

noncomputable section
namespace VortexGap.Fermion
open MeasureTheory OAI.Laughlin.Rotation
open scoped ComplexConjugate ENNReal
variable {α : Type*} [MeasurableSpace α] {n N : ℕ}

def productOrbital (u : α → Fin n → ℂ) (a : Fin N → Fin n) (z : Fin N → α) : ℂ :=
  ∏ i, u (z i) (a i)

theorem productOrbital_gram (μ : Measure α) [SigmaFinite μ] (u : α → Fin n → ℂ)
    (hu : ∀ i j, (∫ z, conj (u z i) * u z j ∂μ) = if i=j then 1 else 0)
    (a b : Fin N → Fin n) :
    (∫ z, conj (productOrbital u a z) * productOrbital u b z ∂Measure.pi (fun _ => μ)) =
      if a=b then 1 else 0 := by
  simp only [productOrbital,map_prod,← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_eq_prod (fun i z => conj (u z (a i)) * u z (b i))]
  simp_rw [hu]
  by_cases h : a=b
  · simp [h]
  · obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    simp only [h, ite_false]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem sphere_basis_gram (q : ℕ) (i j : Fin (q+1)) :
    (∫ g, conj (sphereOrbitalValue q (PiLp.single 2 i (1:ℂ)) g) *
      sphereOrbitalValue q (PiLp.single 2 j (1:ℂ)) g ∂sphereOrbitalMeasure q) =
        if i=j then 1 else 0 := by
  rw [sphereOrbitalMeasure,integral_smul_measure,sphereOrbitalValue_gram,
    ENNReal.toReal_ofReal (by positivity)]
  have hn : (q:ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero q
  simp [Complex.real_smul, mul_ite, hn,eq_comm]

theorem sphere_product_basis_gram (q N : ℕ) (a b : Fin N → Fin (q+1)) :
    let u := fun g i => sphereOrbitalValue q (PiLp.single 2 i (1:ℂ)) g
    (∫ z, conj (productOrbital u a z) * productOrbital u b z
      ∂Measure.pi (fun _ => sphereOrbitalMeasure q)) = if a=b then 1 else 0 :=
  productOrbital_gram _ _ (sphere_basis_gram q) a b

theorem sectorWave_gram [TopologicalSpace α] [CompactSpace α] [BorelSpace α]
    [SecondCountableTopology α] (μ : Measure α) [IsFiniteMeasure μ] (u : α → Fin n → ℂ)
    (hc : ∀ i, Continuous (fun z => u z i))
    (hu : ∀ i j, (∫ z, conj (u z i) * u z j ∂μ) = if i=j then 1 else 0)
    (x y : particleSector n N) :
    (∫ z, conj (sectorWave u x z) * sectorWave u y z ∂Measure.pi (fun _ => μ)) = inner ℂ x y := by
  let X := (sectorTensorIsometry n N x).val
  let Y := (sectorTensorIsometry n N y).val
  let T (a b : Fin N → Fin n) (z : Fin N → α) :=
    (conj (X a)*Y b) * (conj (productOrbital u a z)*productOrbital u b z)
  have hcont (a : Fin N → Fin n) : Continuous (productOrbital u a) := by
    unfold productOrbital
    exact continuous_finsetProd _ fun i _ => (hc _).comp (continuous_apply i)
  have hint (a b) : Integrable (T a b) (Measure.pi fun _ => μ) := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    unfold T
    fun_prop
  have he (z : Fin N → α) : conj (sectorWave u x z) * sectorWave u y z = ∑ a, ∑ b, T a b z := by
    simp only [sectorWave,map_sum,Finset.sum_mul,Finset.mul_sum,map_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    change conj (X a) * conj (productOrbital u a z) * (Y b * productOrbital u b z) = _
    unfold T
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hint a b))]
  simp_rw [integral_finsetSum _ (fun b _ => hint _ b),T,integral_const_mul,productOrbital_gram μ u hu]
  trans inner ℂ X Y
  rotate_left
  · exact LinearIsometryEquiv.inner_map_map (𝕜 := ℂ) (E' := ↥(antisymmetricTensors n N)) (sectorTensorIsometry n N) x y

  simp [PiLp.inner_apply,RCLike.inner_apply,mul_ite,mul_comm]

theorem sphereReferenceWave_gram {q N : ℕ} (x y : particleSector (q+1) N) :
    (∫ z, conj (sphereReferenceWave x z) * sphereReferenceWave y z
      ∂Measure.pi (fun _ => sphereOrbitalMeasure q)) = inner ℂ x y :=
by
  let _ : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) := inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  let _ : SecondCountableTopology SourceSU2 := inferInstanceAs (SecondCountableTopology ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ)))
  exact sectorWave_gram (sphereOrbitalMeasure q) _ (fun i => sphereOrbitalValue_continuous q _)
    (sphere_basis_gram q) x y

end VortexGap.Fermion
end

noncomputable section
namespace VortexGap.Fermion
open MeasureTheory OAI.Laughlin.Rotation VortexGap.Frame
open scoped ComplexConjugate

def sphereFilteredValue (q : ℕ) (f : SourceSU2 → ℂ) (hf : Continuous f) (g : SourceSU2)
    (i : Fin (q+1)) : ℂ :=
  sphereScalarRow q f g ((gramInvSqrt (sphereScalarMap q f hf)) (PiLp.single 2 i 1))

theorem sphereFilteredValue_continuous (q : ℕ) (f : SourceSU2 → ℂ) (hf : Continuous f)
    (i : Fin (q+1)) : Continuous (fun g => sphereFilteredValue q f hf g i) := by
  simp only [sphereFilteredValue,sphereScalarRow_apply]
  exact hf.mul (sphereOrbitalValue_continuous q _)

theorem sphereFilteredValue_gram (q : ℕ) (f : SourceSU2 → ℂ) (hf : Continuous f)
    (a b : ℝ) (ha : 0 < a) (hl : ∀ g, a ≤ ‖f g‖^2) (hu : ∀ g, ‖f g‖^2 ≤ b)
    (i j : Fin (q+1)) :
    (∫ g, conj (sphereFilteredValue q f hf g i) * sphereFilteredValue q f hf g j
      ∂sphereOrbitalMeasure q) = if i=j then 1 else 0 := by
  let F := sphereScalarMap q f hf
  have hF := gramOperator_strict F a ha (sphereScalarGram_bounds q f hf a b ha.le hl hu).1
  have h := gramNormalized_inner F hF (PiLp.single 2 i 1) (PiLp.single 2 j 1)
  change inner ℂ (F (gramInvSqrt F (PiLp.single 2 i 1))) (F (gramInvSqrt F (PiLp.single 2 j 1))) = _ at h
  rw [show F = operatorAnalysis _ _ (sphereScalarRow_memLp q f hf) from rfl,
    operatorAnalysis_inner_integral] at h
  simpa [sphereFilteredValue,F,RCLike.inner_apply,mul_comm,EuclideanSpace.inner_single_left,eq_comm] using! h

theorem sphereDeformedWave_inner {q N : ℕ} (f : SourceSU2 → ℂ) (hf : Continuous f)
    (a b : ℝ) (ha : 0 < a) (hl : ∀ g, a ≤ ‖f g‖^2) (hu : ∀ g, ‖f g‖^2 ≤ b)
    (x y : particleSector (q+1) N) :
    (∫ z, conj (sphereDeformedWave f hf x z) * sphereDeformedWave f hf y z
      ∂Measure.pi (fun _ => sphereOrbitalMeasure q)) = inner ℂ x y := by
  let _ : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) := inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  let _ : SecondCountableTopology SourceSU2 := inferInstanceAs (SecondCountableTopology ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ)))
  exact sectorWave_gram _ _ (sphereFilteredValue_continuous q f hf)
    (sphereFilteredValue_gram q f hf a b ha hl hu) x y

end VortexGap.Fermion
end

noncomputable section
namespace VortexGap.Fermion
open MeasureTheory
open scoped ComplexConjugate
variable {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [BorelSpace α]
  [SecondCountableTopology α] [CompactSpace α] {n N : ℕ}

def sectorWaveLinear (u : α → Fin n → ℂ) (z : Fin N → α) : particleSector n N →ₗ[ℂ] ℂ where
  toFun x := sectorWave u x z
  map_add' x y := by simp [sectorWave,map_add,add_mul,Finset.sum_add_distrib]
  map_smul' c x := by simp [sectorWave,map_smul,Finset.mul_sum,mul_assoc]

theorem sectorWave_memLp (μ : Measure α) [IsFiniteMeasure μ] (u : α → Fin n → ℂ)
    (hc : ∀ i, Continuous fun z => u z i) (x : particleSector n N) :
    MemLp (sectorWave u x) 2 (Measure.pi fun _ => μ) := by
  apply Continuous.memLp_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
  unfold sectorWave
  exact continuous_finsetSum _ fun a _ => continuous_const.mul
    (continuous_finsetProd _ fun i _ => (hc _).comp (continuous_apply i))

def sectorWaveL2Linear (μ : Measure α) [IsFiniteMeasure μ] (u : α → Fin n → ℂ)
    (hc : ∀ i, Continuous fun z => u z i) :
    particleSector n N →ₗ[ℂ] Lp ℂ 2 (Measure.pi (fun _ : Fin N => μ)) where
  toFun x := (sectorWave_memLp μ u hc x).toLp _
  map_add' x y := by
    apply Lp.ext
    filter_upwards [(sectorWave_memLp μ u hc (x+y)).coeFn_toLp,
      Lp.coeFn_add ((sectorWave_memLp μ u hc x).toLp _) ((sectorWave_memLp μ u hc y).toLp _),
      (sectorWave_memLp μ u hc x).coeFn_toLp,(sectorWave_memLp μ u hc y).coeFn_toLp] with z hs ha hx hy
    simpa only [hs,ha,Pi.add_apply,hx,hy] using! (sectorWaveLinear u z).map_add x y
  map_smul' c x := by
    apply Lp.ext
    filter_upwards [(sectorWave_memLp μ u hc (c • x)).coeFn_toLp,
      Lp.coeFn_smul c ((sectorWave_memLp μ u hc x).toLp _),
      (sectorWave_memLp μ u hc x).coeFn_toLp] with z hs ha hx
    simpa only [hs,ha,Pi.smul_apply,hx,RingHom.id_apply] using! (sectorWaveLinear u z).map_smul c x

def sectorWaveL2Isometry (μ : Measure α) [IsFiniteMeasure μ] (u : α → Fin n → ℂ)
    (hc : ∀ i, Continuous fun z => u z i)
    (hu : ∀ i j, (∫ z, conj (u z i)*u z j ∂μ) = if i=j then 1 else 0) :
    particleSector n N →ₗᵢ[ℂ] Lp ℂ 2 (Measure.pi (fun _ : Fin N => μ)) := by
  refine LinearMap.isometryOfInner (𝕜 := ℂ) (E := ↥(particleSector n N)) (E' := Lp ℂ 2 (Measure.pi (fun _ : Fin N => μ))) (sectorWaveL2Linear μ u hc) ?_
  intro x y
  rw [L2.inner_def,← sectorWave_gram μ u hc hu x y]
  apply integral_congr_ae
  filter_upwards [(sectorWave_memLp μ u hc x).coeFn_toLp,(sectorWave_memLp μ u hc y).coeFn_toLp] with z hx hy

  simp only [sectorWaveL2Linear,LinearMap.coe_mk,AddHom.coe_mk,hx,hy,RCLike.inner_apply,mul_comm]

theorem sectorWaveL2Isometry_ae (μ : Measure α) [IsFiniteMeasure μ] (u : α → Fin n → ℂ)
    (hc : ∀ i, Continuous fun z => u z i)
    (hu : ∀ i j, (∫ z, conj (u z i)*u z j ∂μ) = if i=j then 1 else 0)
    (x : particleSector n N) :
    sectorWaveL2Isometry μ u hc hu x =ᵐ[Measure.pi (fun _ => μ)] sectorWave u x :=
  (sectorWave_memLp μ u hc x).coeFn_toLp

open OAI.Laughlin.Rotation VortexGap.SpherePolynomial
section Sphere
local instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
local instance : SecondCountableTopology SourceSU2 :=
  inferInstanceAs (SecondCountableTopology ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ)))

private def refValue (q : ℕ) (g : SourceSU2) (i : Fin (q+1)) : ℂ :=
  sphereOrbitalValue q (PiLp.single 2 i (1:ℂ)) g

private theorem refValue_cont (q : ℕ) (i : Fin (q+1)) : Continuous (fun g => refValue q g i) :=
  sphereOrbitalValue_continuous q _

def sphereReferenceWaveL2 (q N : ℕ) := sectorWaveL2Isometry (n := q+1) (N := N) (sphereOrbitalMeasure q)
  (refValue q) (refValue_cont q) (sphere_basis_gram q)

def sphereDeformedWaveL2 (q N : ℕ) (f : SourceSU2 → ℂ) (hf : Continuous f)
    (a b : ℝ) (ha : 0 < a) (hl : ∀ g, a ≤ ‖f g‖^2) (hu : ∀ g, ‖f g‖^2 ≤ b) :=
  sectorWaveL2Isometry (N := N) (sphereOrbitalMeasure q) _ (sphereFilteredValue_continuous q f hf)
    (sphereFilteredValue_gram q f hf a b ha hl hu)

theorem sphere_laughlin_product_L2 (n N : ℕ) (hQ : 3*((N+2)-1) = n+1)
    (f : SourceSU2 → ℂ) (hf : Continuous f) (a b : ℝ)
    (ha : 0 < a) (hl : ∀ g, a ≤ ‖f g‖^2) (hu : ∀ g, ‖f g‖^2 ≤ b) :
    ∃ l y : particleSector (n+2) (N+2), sectorPoly l = laughlin (N+2) ∧
      LinearMap.ker (sphereSectorHam n (N+2) (spherePhysicalPair n f hf)).toLinearMap = ℂ ∙ y ∧
      (sphereDeformedWaveL2 (n+1) (N+2) f hf a b ha hl hu y : _ → ℂ) =ᵐ[Measure.pi (fun _ => sphereOrbitalMeasure (n+1))]
        (fun z => (∏ i, f (z i)) * sphereReferenceWaveL2 (n+1) (N+2) l z) := by
  obtain ⟨l,y,hlp,hk,hpoint⟩ := sphere_laughlin_product_generator n N hQ f hf a b ha hl hu
  refine ⟨l,y,hlp,hk,?_⟩
  have hy : (sphereDeformedWaveL2 (n+1) (N+2) f hf a b ha hl hu y : _ → ℂ) =ᵐ[_]
      sphereDeformedWave f hf y := sectorWaveL2Isometry_ae _ _ _ _ y
  have hlr : (sphereReferenceWaveL2 (n+1) (N+2) l : _ → ℂ) =ᵐ[_] sphereReferenceWave l :=
    sectorWaveL2Isometry_ae _ _ _ _ l
  filter_upwards [hy,hlr] with z h1 h2
  rw [h1,h2,hpoint]
end Sphere

end VortexGap.Fermion
end
