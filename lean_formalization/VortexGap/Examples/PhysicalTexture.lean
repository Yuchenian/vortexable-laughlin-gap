import VortexGap.Physical.OrbitalColumn
import VortexGap.Examples.PlaneNodalFourier

noncomputable section

namespace VortexGap.Fermion
open MeasureTheory
open scoped BoundedContinuousFunction

def textureBandField (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hG : IsStrictlyPositive (planeScalarGram ell hell f)) (θ k : ℝ) (i : Fin 2) (z : ℂ) :=
  orbitalTexture θ k z i • planeBandField ell hell f hG z

def textureDirectionalEnergy (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hG : IsStrictlyPositive (planeScalarGram ell hell f)) (θ k : ℝ) (z c : ℂ) (x : CountableSpace) :=
  ∑ i, ∑ j, ‖((textureBandField ell hell f hG θ k i z) *
    deriv (fun t : ℝ => textureBandField ell hell f hG θ k j (z+(t:ℂ)*c)) 0) x‖^2

theorem textureDirectionalEnergy_eq (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hG : IsStrictlyPositive (planeScalarGram ell hell f)) (hf : Differentiable ℝ f)
    (θ k : ℝ) (z c : ℂ) (x : CountableSpace) :
    textureDirectionalEnergy ell hell f hG θ k z c x =
      ‖(planeScalarContactField (gramInvSqrt (planeScalarEmbedding ell hell f)) ell f z c) x‖^2 := by
  let R := gramInvSqrt (planeScalarEmbedding ell hell f)
  let p := fun t : ℝ => z+(t:ℂ)*c
  have hp : HasDerivAt p c 0 := by simpa [p] using (Complex.ofRealCLM.hasDerivAt.mul_const c).const_add z
  have hz : p 0 = z := by simp [p]
  have h := orbitalTexture_contact_energy θ k p hp.differentiableAt
    (fun s => planeFilteredField R ell (p s))
    (planeFilteredField_hasDerivAt_direction R ell z c)
    (v := R (planeEvaluation ell (p 0))) rfl (fun s => f (p s)) ((hf _).comp 0 hp.differentiableAt) x
  rw [hz] at h
  rw [planeScalarContactField_cancel _ _ _ _ _ (hf z)]
  simp only [textureDirectionalEnergy,textureBandField,planeBandField_eq_filtered,smul_smul,
    smul_apply,norm_smul,norm_pow,mul_pow, ← pow_mul]
  simpa only [R,p,mul_comm (orbitalTexture θ k _ _) _, ← pow_mul] using h

def textureContactDensity (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hG : IsStrictlyPositive (planeScalarGram ell hell f)) (θ k : ℝ) (z : ℂ) (N : ℕ) (x : countableSector N) :=
  4*Real.pi*ell^4 * (textureDirectionalEnergy ell hell f hG θ k z 1 x +
    textureDirectionalEnergy ell hell f hG θ k z Complex.I x)

theorem textureContact_energy (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hG : IsStrictlyPositive (planeScalarGram ell hell f)) (hf : Differentiable ℝ f)
    (θ k : ℝ) (N : ℕ) (x : countableSector N) :
    (∫ z, textureContactDensity ell hell f hG θ k z N x) =
      (inner ℂ x (planeBandContactOperator ell hell f hG hf N x)).re := by
  rw [planeBandContactOperator_energy]
  apply integral_congr_ae
  filter_upwards with z
  rw [textureContactDensity,textureDirectionalEnergy_eq _ _ _ _ hf, textureDirectionalEnergy_eq _ _ _ _ hf,
    planeBandContactDensity_eq]
  rfl

/-- The normalized orbital coordinates embed in actual two-component Lebesgue L². -/
def textureBandEmbedding (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hG : IsStrictlyPositive (planeScalarGram ell hell f)) (θ k : ℝ) :=
  (orbitalColumnIsometry (μ := (volume : Measure ℂ)) (orbitalTexture θ k)
    (orbitalTexture_continuous θ k).aestronglyMeasurable
    (Filter.Eventually.of_forall (orbitalTexture_norm θ k))).comp
    (gramIsometry (planeScalarEmbedding ell hell f) hG)

theorem textureBandEmbedding_represents (ell : ℝ) (hell : 0 < ell) (f : ℂ →ᵇ ℂ)
    (hG : IsStrictlyPositive (planeScalarGram ell hell f)) (θ k : ℝ) (v : CountableOrbital) :
    (textureBandEmbedding ell hell f hG θ k v : ℂ → EuclideanSpace ℂ (Fin 2)) =ᵐ[volume]
      fun z => (f z * inner ℂ (planeEvaluation ell z) (gramInvSqrt (planeScalarEmbedding ell hell f) v)) •
        orbitalTexture θ k z := by
  have hu := planeScalarUnitary_coe ell hell f hG v
  have hj := orbitalColumnIsometry_apply (μ := (volume : Measure ℂ)) (orbitalTexture θ k)
    (orbitalTexture_continuous θ k).aestronglyMeasurable
    (Filter.Eventually.of_forall (orbitalTexture_norm θ k)) ((gramIsometry (planeScalarEmbedding ell hell f) hG) v)
  filter_upwards [hj,hu] with z h1 h2
  exact h1.trans (congrArg (fun w : ℂ => w • orbitalTexture θ k z) h2)

theorem textured_nodal_physical (ell : ℝ) (hell : 0 < ell) (θ k : ℝ) (N : ℕ)
    (href : ∀ j ≤ N, let H := countablePairLift j planePairOperator
      (H*H-(1/5:ℂ) • H).IsPositive) :
    ∃ A : countableSector N →L[ℂ] countableSector N, A.IsPositive ∧
      (∀ x, (inner ℂ x (A x)).re = ∫ z, textureContactDensity ell hell (planeNodal ell)
        (planeNodal_gram_strict ell hell) θ k z N x) ∧
      ∀ t ∈ spectrum ℝ A, t = 0 ∨ (0.1763:ℝ) ≤ t :=
  ⟨_,planeBandContactOperator_positive ..,
    fun x => (textureContact_energy ell hell _ _ (planeNodal_differentiable ell) θ k N x).symm,
    planeNodal_gap_of_reference_fifth ell hell N href⟩

end VortexGap.Fermion
