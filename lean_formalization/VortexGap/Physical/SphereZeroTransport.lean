import VortexGap.Fermion.PairKernelTransport
import VortexGap.Examples.SphereAxial
noncomputable section
namespace VortexGap.Fermion
open MeasureTheory OAI.Laughlin.Rotation
open scoped ComplexOrder ENNReal

private theorem sphereSector_ker_eq (n N : ℕ) (p : SourceSU2 → PairSpace (n+2)) (hp : Continuous p) :
    LinearMap.ker (sphereSectorHam n N p).toLinearMap =
      continuousSectorZeroSpace (spherePairMeasure n) p N := by
  ext x
  change sphereSectorHam n N p x = 0 ↔ continuousFrameHamiltonian (spherePairMeasure n) p x = 0
  rw [← sphereSectorHam_apply N p hp]
  exact Submodule.coe_eq_zero.symm

/-- The inverse Gram square root maps the physical zero sector onto the
reference zero sector. Their multiplicities agree at every flux and N. -/
theorem spherePhysical_zero_transport (n N : ℕ) (f : SourceSU2 → ℂ) (hf : Continuous f)
    (a b : ℝ) (ha : 0 < a) (hl : ∀ g, a ≤ ‖f g‖^2) (hu : ∀ g, ‖f g‖^2 ≤ b) :
    let R := (gramInvSqrt (sphereScalarMap (n+1) f hf)).toLinearMap
    let Z := LinearMap.ker (sphereSectorHam n N (spherePhysicalPair n f hf)).toLinearMap
    let Z₀ := LinearMap.ker (sphereSectorHam n N (sphereOrbitPair n)).toLinearMap
    Z.map (exteriorPower R N) = Z₀ ∧ Module.finrank ℂ Z = Module.finrank ℂ Z₀ := by
  dsimp only
  rw [sphereSector_ker_eq _ _ _ (spherePhysicalPair_continuous n f hf),
      sphereSector_ker_eq _ _ _ (sphereOrbitPair_continuous n)]
  let F := sphereScalarMap (n+1) f hf
  let R := (gramInvSqrt F).toLinearMap
  let S := (CFC.sqrt (gramOperator F)).toLinearMap
  have hF := gramOperator_strict F a ha (sphereScalarGram_bounds (n+1) f hf a b ha.le hl hu).1
  have hSR : S.comp R = LinearMap.id := congrArg ContinuousLinearMap.toLinearMap (gramInvSqrt_right F hF)
  have hRS : R.comp S = LinearMap.id := congrArg ContinuousLinearMap.toLinearMap (gramInvSqrt_left F hF)
  have hpos : 0 ≤ gramInvSqrt F := by rw [gramInvSqrt_eq_sqrt_inverse]; exact CFC.sqrt_nonneg _
  have hR : R.adjoint = R := by
    rw [LinearMap.adjoint_eq_toCLM_adjoint]
    exact congrArg ContinuousLinearMap.toLinearMap (show (gramInvSqrt F).adjoint = gramInvSqrt F from (IsSelfAdjoint.of_nonneg hpos).star_eq)
  let w := fun g => f g ^ 2
  have hw : ∀ᵐ g ∂spherePairMeasure n, w g ≠ 0 := Filter.Eventually.of_forall fun g => by
    apply pow_ne_zero
    intro hz
    simpa [hz,ha.not_ge] using hl g
  have he : (fun g => w g • exteriorSquare R.adjoint (sphereOrbitPair n g)) = spherePhysicalPair n f hf := by
    rw [hR]; rfl
  have hp := (sphereOrbitPair_continuous n).memLp_of_hasCompactSupport
    (μ := spherePairMeasure n) (p := 2) (HasCompactSupport.of_compactSpace _)
  have hq := (spherePhysicalPair_continuous n f hf).memLp_of_hasCompactSupport
    (μ := spherePairMeasure n) (p := 2) (HasCompactSupport.of_compactSpace _)
  rw [← he] at hq ⊢
  exact ⟨continuousSectorZeroSpace_map _ _ hp R S hSR hRS w hw hq N,
    continuousSectorZeroSpace_finrank _ _ hp R S hSR hRS w hw hq N⟩

/-- Nonconstant axial deformation at every positive flux and particle number. -/
theorem sphereAxial_zero_multiplicity (n N : ℕ) :
    Module.finrank ℂ (LinearMap.ker (sphereSectorHam n N (spherePhysicalPair n
      sphereAxialMultiplier sphereAxialMultiplier_continuous)).toLinearMap) =
      Module.finrank ℂ (LinearMap.ker (sphereSectorHam n N (sphereOrbitPair n)).toLinearMap) := by
  apply (spherePhysical_zero_transport n N _ sphereAxialMultiplier_continuous 1 (1001/1000)
    zero_lt_one ?_ ?_).2
  · intro g
    rw [sphereAxialMultiplier_weight]
    linarith [sq_nonneg ‖g.val 0 0‖]
  · intro g
    rw [sphereAxialMultiplier_weight]
    have h := unitary_entry_norm_le_one g.val g.property.1 0 0
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (add_nonneg (norm_nonneg (g.val 0 0)) zero_le_one)]

/-- The two-particle reference kernel is the embedded orthogonal complement
of the V1 pair channel. -/
theorem sphereReference_two_kernel (n : ℕ) :
    LinearMap.ker (sphereSectorHam n 2 (sphereOrbitPair n)).toLinearMap =
      (spherePairSector n)ᗮ.map pairSectorEmbed := by
  ext x
  obtain ⟨p,hp⟩ := (pairEmbed_range_iff (x : Space (n+2))).mpr x.property
  have hx : pairSectorEmbed p = x := Subtype.ext hp
  subst x
  have hker : pairSectorEmbed p ∈ LinearMap.ker (sphereSectorHam n 2 (sphereOrbitPair n)).toLinearMap ↔
      p ∈ (spherePairSector n)ᗮ := by
    rw [LinearMap.mem_ker]
    change sphereSectorHam n 2 (sphereOrbitPair n) (pairSectorEmbed p) = 0 ↔ _
    rw [← Submodule.coe_eq_zero]
    change pairLift (continuousPairOperator (spherePairMeasure n) (sphereOrbitPair n)).toLinearMap (pairEmbed p) = 0 ↔ _
    rw [spherePairMeasure_operator,pairLift_pairEmbed,← map_zero pairEmbed]
    exact (pairEmbedding _).injective.eq_iff.trans (Submodule.starProjection_apply_eq_zero_iff _)
  rw [hker]
  constructor
  · intro h
    exact ⟨p,h,rfl⟩
  · rintro ⟨q,hq,he⟩
    have he' : q = p := (pairEmbedding _).injective (congrArg Subtype.val he)
    simpa [he'] using hq

theorem spherePhysical_flux_three_two_unique (f : SourceSU2 → ℂ) (hf : Continuous f)
    (a b : ℝ) (ha : 0 < a) (hl : ∀ g, a ≤ ‖f g‖^2) (hu : ∀ g, ‖f g‖^2 ≤ b) :
    Module.finrank ℂ (LinearMap.ker (sphereSectorHam 2 2 (spherePhysicalPair 2 f hf)).toLinearMap) = 1 := by
  rw [(spherePhysical_zero_transport 2 2 f hf a b ha hl hu).2, sphereReference_two_kernel]
  have hi : Function.Injective (@pairSectorEmbed 4) := fun _ _ h =>
    (pairEmbedding 4).injective (congrArg Subtype.val h)
  rw [← (Submodule.equivMapOfInjective _ hi _).finrank_eq]
  have h := (spherePairSector 2).finrank_add_finrank_orthogonal
  obtain ⟨hd,ht⟩ := spherePair_flux_three_test
  rw [hd,show Module.finrank ℂ (PairSpace (2+2)) = 6 from ht] at h
  change Module.finrank ℂ (spherePairSector 2)ᗮ = 1
  exact Nat.add_left_cancel (show 5 + Module.finrank ℂ (spherePairSector 2)ᗮ = 5 + 1 from h)

end VortexGap.Fermion
