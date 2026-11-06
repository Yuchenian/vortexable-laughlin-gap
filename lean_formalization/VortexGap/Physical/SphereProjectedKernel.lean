import VortexGap.Physical.SphereProjectedGap
import VortexGap.Geometry.SphereGaugeSection

noncomputable section

namespace VortexGap.Fermion
open MeasureTheory OAI.Laughlin.Rotation VortexGap.SpherePolynomial
open scoped InnerProduct ComplexOrder

private theorem sector_kernel (n N : ℕ) (p : SourceSU2 → PairSpace (n+2)) (hp : Continuous p) :
    LinearMap.ker (sphereSectorHam n N p).toLinearMap = continuousSectorZeroSpace (spherePairMeasure n) p N := by
  ext x
  change sphereSectorHam n N p x = 0 ↔ continuousFrameHamiltonian (spherePairMeasure n) p x = 0
  rw [← sphereSectorHam_apply N p hp]
  exact Submodule.coe_eq_zero.symm

theorem sphere_projected_zero_transport (n N : ℕ) (f : SourceSU2 → ℂ) (hf : Continuous f)
    (hG : IsStrictlyPositive (gramOperator (sphereScalarMap (n+1) f hf))) (κ : ℝ) (hk : 0 < κ)
    (hpair : ∀ q : PairSpace (n+2),
      κ*(∫ g, ‖inner ℂ (sphereOrbitPair n g) q‖^2 ∂spherePairMeasure n) ≤
        ∫ g, ‖f g‖^4 * ‖inner ℂ (sphereOrbitPair n g) q‖^2 ∂spherePairMeasure n) :
    let R := (gramInvSqrt (sphereScalarMap (n+1) f hf)).toLinearMap
    let Z := LinearMap.ker (sphereSectorHam n N (spherePhysicalPair n f hf)).toLinearMap
    let Z₀ := LinearMap.ker (sphereSectorHam n N (sphereOrbitPair n)).toLinearMap
    Z.map (exteriorPower R N) = Z₀ := by
  let F := sphereScalarMap (n+1) f hf
  let R := (gramInvSqrt F).toLinearMap
  let S := (CFC.sqrt (gramOperator F)).toLinearMap
  have hSR : S.comp R = LinearMap.id := congrArg ContinuousLinearMap.toLinearMap (gramInvSqrt_right F hG)
  have hRS : R.comp S = LinearMap.id := congrArg ContinuousLinearMap.toLinearMap (gramInvSqrt_left F hG)
  have hR : R.adjoint = R := by
    rw [LinearMap.adjoint_eq_toCLM_adjoint]
    exact congrArg ContinuousLinearMap.toLinearMap (show (gramInvSqrt F).adjoint = gramInvSqrt F from
      (IsSelfAdjoint.of_nonneg (gramInvSqrt_nonneg F hG)).star_eq)
  let p := sphereOrbitPair n
  let E := (exteriorSquare R).toContinuousLinearMap
  have hc := (sphere_projected_comparison n N E (fun g => f g^2) (hf.pow 2) κ hk (by
    simpa only [norm_pow,← pow_mul] using! hpair)).1
  change LinearMap.ker (sphereSectorHam n N (spherePhysicalPair n f hf)).toLinearMap =
    LinearMap.ker (sphereSectorHam n N (fun g => E (p g))).toLinearMap at hc
  dsimp only
  rw [hc,sector_kernel n N (fun g => E (p g)) (E.continuous.comp (sphereOrbitPair_continuous n)),sector_kernel n N _ (sphereOrbitPair_continuous n)]
  have hp := (sphereOrbitPair_continuous n).memLp_of_hasCompactSupport (μ := spherePairMeasure n)
    (p := 2) (HasCompactSupport.of_compactSpace _)
  have hq := (E.continuous.comp (sphereOrbitPair_continuous n)).memLp_of_hasCompactSupport
    (μ := spherePairMeasure n) (p := 2) (HasCompactSupport.of_compactSpace _)
  have he (g : SourceSU2) : (1:ℂ) • exteriorSquare R.adjoint (p g) = E (p g) := by rw [hR,one_smul]; rfl
  have ht := continuousSectorZeroSpace_map (spherePairMeasure n) p hp R S hSR hRS (fun _ => 1)
    (Filter.Eventually.of_forall (fun _ => one_ne_zero)) (by simpa only [he,p,Function.comp_def] using! hq) N
  simpa only [he] using! ht

variable {q N : ℕ}
theorem sphereProjectedWave_product (f : SourceSU2 → ℂ) (hf : Continuous f)
    (hF : IsStrictlyPositive (gramOperator (sphereScalarMap q f hf)))
    (x : particleSector (q+1) N) (z : Fin N → SourceSU2) :
    let S := (CFC.sqrt (gramOperator (sphereScalarMap q f hf))).toLinearMap
    sphereDeformedWave f hf (exteriorPower S N x) z = (∏ i, f (z i)) * sphereReferenceWave x z := by
  let F := sphereScalarMap q f hf
  let R := gramInvSqrt F
  let S := CFC.sqrt (gramOperator F)
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

theorem sphere_projected_laughlin (n N : ℕ) (hQ : 3*((N+2)-1) = n+1)
    (f : SourceSU2 → ℂ) (hf : Continuous f) (hG : IsStrictlyPositive (gramOperator (sphereScalarMap (n+1) f hf)))
    (κ : ℝ) (hk : 0 < κ) (hpair : ∀ q : PairSpace (n+2),
      κ*(∫ g, ‖inner ℂ (sphereOrbitPair n g) q‖^2 ∂spherePairMeasure n) ≤
        ∫ g, ‖f g‖^4 * ‖inner ℂ (sphereOrbitPair n g) q‖^2 ∂spherePairMeasure n) :
    ∃ l y : particleSector (n+2) (N+2), sectorPoly l = laughlin (N+2) ∧ y ≠ 0 ∧
      LinearMap.ker (sphereSectorHam n (N+2) (spherePhysicalPair n f hf)).toLinearMap = ℂ ∙ y ∧
      ∀ z, sphereDeformedWave f hf y z = (∏ i, f (z i)) * sphereReferenceWave l z := by
  obtain ⟨l,hn,hp,hl⟩ := sphere_reference_laughlin_kernel n N hQ
  let F := sphereScalarMap (n+1) f hf
  let S := (CFC.sqrt (gramOperator F)).toLinearMap
  let R := (gramInvSqrt F).toLinearMap
  have hSR : S.comp R = LinearMap.id := congrArg ContinuousLinearMap.toLinearMap (gramInvSqrt_right F hG)
  have hRS : R.comp S = LinearMap.id := congrArg ContinuousLinearMap.toLinearMap (gramInvSqrt_left F hG)
  have ht := sphere_projected_zero_transport n (N+2) f hf hG κ hk hpair
  dsimp only at ht
  rw [hl] at ht
  have hh := congrArg (Submodule.map (exteriorPower S (N+2))) ht
  rw [← Submodule.map_comp,← exteriorPower_comp,hSR,exteriorPower_id,Submodule.map_id,
    Submodule.map_span,Set.image_singleton] at hh
  refine ⟨l,exteriorPower S (N+2) l,hp,?_,hh,sphereProjectedWave_product f hf hG l⟩
  intro hzero
  have h := congrArg (exteriorPower R (N+2)) hzero
  rw [map_zero,← LinearMap.comp_apply,← exteriorPower_comp,hRS,exteriorPower_id,LinearMap.id_apply] at h
  exact hn h

end VortexGap.Fermion
