import VortexGap.Fermion.CountableOrbitalSpace
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.Bases
import Mathlib.Basic.Denumerable
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open TopologicalSpace
open scoped InnerProduct

/-- Countability follows from disjoint metric balls, not from a countable-basis premise. -/
theorem separable_orthonormal_countable
    {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [SeparableSpace H]
    (v : ι → H) (hv : Orthonormal ℂ v) : Countable ι := by
  have hd (i j : ι) (hij : i ≠ j) : 1 ≤ dist (v i) (v j) := by
    have hs : ‖v i - v j‖^2 = 2 := by
      rw [norm_sub_sq (𝕜 := ℂ), hv.norm_eq_one, hv.norm_eq_one, hv.inner_eq_zero hij]
      norm_num
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (v i - v j)]
  have hdis : Pairwise (fun i j => Disjoint (Metric.ball (v i) (1/2 : ℝ))
      (Metric.ball (v j) (1/2 : ℝ))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hi hj
    have hix : dist (v i) x < (1/2 : ℝ) := by simpa [dist_comm] using hi
    have hxj : dist x (v j) < (1/2 : ℝ) := hj
    have ht := dist_triangle (v i) x (v j)
    have hh := hd i j hij
    linarith
  exact hdis.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun i => ⟨v i, Metric.mem_ball_self (by norm_num)⟩)

/-- Every infinite-dimensional separable complete complex Hilbert space admits
coordinates in the completed countable orbital model. -/
theorem separable_exists_nat_hilbertBasis
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [SeparableSpace H] (hinf : ¬ FiniteDimensional ℂ H) :
    Nonempty (HilbertBasis ℕ ℂ H) := by
  classical
  obtain ⟨w, b, _⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  letI : Countable w := separable_orthonormal_countable b b.orthonormal
  rcases finite_or_infinite w with hw | hw
  · letI := hw
    letI := Fintype.ofFinite w
    exact False.elim (hinf b.toOrthonormalBasis.toBasis.finiteDimensional_of_finite)
  · letI := hw
    obtain ⟨e⟩ : Nonempty (w ≃ ℕ) := nonempty_equiv_of_countable
    have hr : Set.range (fun n => b (e.symm n)) = Set.range b := by
      ext x
      constructor
      · rintro ⟨n, rfl⟩; exact ⟨e.symm n, rfl⟩
      · rintro ⟨i, rfl⟩; exact ⟨e i, by simp⟩
    refine ⟨HilbertBasis.mk (b.orthonormal.comp e.symm e.symm.injective) ?_⟩
    change ⊤ ≤ (Submodule.span ℂ (Set.range (fun n => b (e.symm n)))).topologicalClosure
    rw [hr, b.dense_span]

theorem separable_exists_countableOrbital_unitary
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [SeparableSpace H] (hinf : ¬ FiniteDimensional ℂ H) :
    Nonempty (H ≃ₗᵢ[ℂ] CountableOrbital) := by
  obtain ⟨b⟩ := separable_exists_nat_hilbertBasis H hinf
  exact ⟨b.repr⟩

theorem hilbertBasis_coordinate_ket
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (b : HilbertBasis ℕ ℂ H) (j : ℕ) : b.repr (b j) = orbitalKet j :=
  b.repr_self j
end VortexGap.Fermion