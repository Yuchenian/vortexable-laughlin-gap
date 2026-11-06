import VortexGap.Reference.PlanarPair
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped BigOperators Matrix InnerProduct

theorem upstreamPlanarPair_create_action (L p : ℕ) (x : OAI.Laughlin.Fock.Space L) :
    upstreamCoordinates L (OAI.Laughlin.Fock.pairCreateEnd L
      (fun i j => OAI.Laughlin.Planar.planarCoefficient p i.val j.val) x) =
      -((pairAnnihilate (planeFiniteBlock L p)).adjoint (upstreamCoordinates L x)) := by
  apply ext_inner_right ℂ
  intro y
  obtain ⟨z, rfl⟩ := upstreamCoordinates_surjective L y
  rw [upstreamCoordinates_inner, OAI.Laughlin.Fock.pairCreate_pair_adjoint,
    ← upstreamCoordinates_inner, upstreamPlanarPair_action, inner_neg_right,
    inner_neg_left, LinearMap.adjoint_inner_left]

theorem upstreamPairCreateMatrix_toMatrix (L : ℕ) (c : Fin (L+1) → Fin (L+1) → ℂ) :
    (OAI.Laughlin.Planar.pairMatrix L c)ᴴ = LinearMap.toMatrix
      (OAI.Laughlin.Fock.occupationBasis L) (OAI.Laughlin.Fock.occupationBasis L)
      (OAI.Laughlin.Fock.pairCreateEnd L c) := by
  rw [upstreamPairMatrix_toMatrix]
  ext A B
  simp only [Matrix.conjTranspose_apply, LinearMap.toMatrix_apply]
  have h := OAI.Laughlin.Fock.pairCreate_pair_adjoint L c
    (OAI.Laughlin.Fock.occupationBasis L B) (OAI.Laughlin.Fock.occupationBasis L A)
  have hl (D : Finset (Fin (L+1))) (y : OAI.Laughlin.Fock.Space L) :
      OAI.Laughlin.Fock.occupationInner L (OAI.Laughlin.Fock.occupationBasis L D) y =
        (OAI.Laughlin.Fock.occupationBasis L).repr y D := by
    simp [OAI.Laughlin.Fock.occupationInner, Module.Basis.repr_self, Finsupp.single_apply]
  have hr (D : Finset (Fin (L+1))) (y : OAI.Laughlin.Fock.Space L) :
      OAI.Laughlin.Fock.occupationInner L y (OAI.Laughlin.Fock.occupationBasis L D) =
        star ((OAI.Laughlin.Fock.occupationBasis L).repr y D) := by
    simp [OAI.Laughlin.Fock.occupationInner, Module.Basis.repr_self, Finsupp.single_apply]
  rw [hl, hr] at h
  simpa only [star_star] using (congrArg star h).symm

def planeFiniteHamiltonian (L : ℕ) : Module.End ℂ (Space (L+1)) :=
  ∑ p ∈ Finset.range (2*L+1),
    (pairAnnihilate (planeFiniteBlock L p)).adjoint * pairAnnihilate (planeFiniteBlock L p)

def upstreamPlanarEnd (L : ℕ) : Module.End ℂ (OAI.Laughlin.Fock.Space L) :=
  ∑ p ∈ Finset.range (2*L+1),
    OAI.Laughlin.Fock.pairCreateEnd L (fun i j => OAI.Laughlin.Planar.planarCoefficient p i.val j.val) *
    OAI.Laughlin.Fock.pairEnd L (fun i j => OAI.Laughlin.Planar.planarCoefficient p i.val j.val)

theorem upstreamPlanarHamiltonian_toMatrix (L : ℕ) :
    OAI.Laughlin.Planar.planarHamiltonian L = LinearMap.toMatrix
      (OAI.Laughlin.Fock.occupationBasis L) (OAI.Laughlin.Fock.occupationBasis L)
      (upstreamPlanarEnd L) := by
  unfold OAI.Laughlin.Planar.planarHamiltonian upstreamPlanarEnd
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [LinearMap.toMatrix_mul]
  change (OAI.Laughlin.Planar.pairMatrix L _)ᴴ * OAI.Laughlin.Planar.pairMatrix L _ = _
  rw [upstreamPairCreateMatrix_toMatrix, upstreamPairMatrix_toMatrix]

theorem upstreamCoordinates_planarHamiltonian (L : ℕ) (x : OAI.Laughlin.Fock.Space L) :
    upstreamCoordinates L (upstreamPlanarEnd L x) =
      planeFiniteHamiltonian L (upstreamCoordinates L x) := by
  change upstreamCoordinateEquiv L _ = _
  simp only [upstreamPlanarEnd, planeFiniteHamiltonian, LinearMap.sum_apply,
    Module.End.mul_apply, map_sum, upstreamCoordinateEquiv_apply,
    upstreamPlanarPair_create_action, upstreamPlanarPair_action, map_neg, neg_neg]

theorem upstreamPlanar_squareNorm (L : ℕ) (x : OAI.Laughlin.Fock.Space L) :
    OAI.Laughlin.Planar.squareNorm L (OAI.Laughlin.Planar.planarHamiltonian L)
      ((OAI.Laughlin.Fock.occupationBasis L).repr x) =
      ‖planeFiniteHamiltonian L (upstreamCoordinates L x)‖^2 := by
  rw [OAI.Laughlin.Planar.squareNorm, upstreamPlanarHamiltonian_toMatrix,
    LinearMap.toMatrix_mulVec_repr]
  change OAI.Laughlin.Fock.occupationNormSq L (upstreamPlanarEnd L x) = _
  rw [← upstreamCoordinates_norm_sq, upstreamCoordinates_planarHamiltonian]

theorem planeFiniteHamiltonian_pairLift (L : ℕ) :
    planeFiniteHamiltonian L =
      pairLift (∑ p ∈ Finset.range (2*L+1), pairRankOne (planeFiniteBlock L p)) := by
  change _ = pairLiftLinear (L+1) (∑ p ∈ Finset.range (2*L+1), pairRankOne (planeFiniteBlock L p))
  rw [map_sum]
  unfold planeFiniteHamiltonian
  apply Finset.sum_congr rfl
  intro p hp
  exact (pairLift_rankOne (planeFiniteBlock L p)).symm

theorem planeFiniteHamiltonian_quadratic (L : ℕ) (x : Space (L+1)) :
    (inner ℂ x (planeFiniteHamiltonian L x)).re =
      ∑ p ∈ Finset.range (2*L+1), ‖pairAnnihilate (planeFiniteBlock L p) x‖^2 := by
  simp only [planeFiniteHamiltonian, LinearMap.sum_apply, Module.End.mul_apply,
    inner_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [LinearMap.adjoint_inner_right]
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm

end VortexGap.Fermion

