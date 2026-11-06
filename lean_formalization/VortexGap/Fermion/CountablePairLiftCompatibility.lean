import VortexGap.Fermion.CountablePairLift

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct ComplexConjugate

theorem finitePairEmbedding_adjoint_embed {n : ℕ} (p : PairSpace n) :
    (finitePairEmbedding n).toContinuousLinearMap.adjoint (finitePairEmbedding n p) = p := by
  apply ext_inner_left ℂ
  intro q
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (finitePairEmbedding n).inner_map_map q p

/-- Extend a finite pair operator by zero on the orthogonal complement of its pair space. -/
def finitePairOperator {n : ℕ} (Q : Module.End ℂ (PairSpace n)) :
    CountablePairSpace →L[ℂ] CountablePairSpace :=
  (finitePairEmbedding n).toContinuousLinearMap.comp
    ((LinearMap.toContinuousLinearMap Q).comp (finitePairEmbedding n).toContinuousLinearMap.adjoint)

theorem finitePairOperator_embed {n : ℕ} (Q : Module.End ℂ (PairSpace n)) (p : PairSpace n) :
    finitePairOperator Q (finitePairEmbedding n p) = finitePairEmbedding n (Q p) := by
  change finitePairEmbedding n (Q ((finitePairEmbedding n).toContinuousLinearMap.adjoint
    (finitePairEmbedding n p))) = _
  rw [finitePairEmbedding_adjoint_embed]

theorem finitePairOperator_expansion {n : ℕ} (Q : Module.End ℂ (PairSpace n)) :
    finitePairOperator Q = ∑ b : PairIndex n, InnerProductSpace.rankOne ℂ
      (finitePairEmbedding n (Q (pairBasis b))) (finitePairEmbedding n (pairBasis b)) := by
  apply ContinuousLinearMap.ext
  intro p
  have hc (b : PairIndex n) :
      inner ℂ (finitePairEmbedding n (pairBasis b)) p =
        ((finitePairEmbedding n).toContinuousLinearMap.adjoint p) b := by
    calc
      _ = inner ℂ (pairBasis b) ((finitePairEmbedding n).toContinuousLinearMap.adjoint p) :=
        (ContinuousLinearMap.adjoint_inner_right (finitePairEmbedding n).toContinuousLinearMap
          (pairBasis b) p).symm
      _ = _ := by simp [pairBasis, EuclideanSpace.inner_single_left]
  change finitePairEmbedding n (Q ((finitePairEmbedding n).toContinuousLinearMap.adjoint p)) = _
  conv_lhs => rw [← pairBasis_expansion ((finitePairEmbedding n).toContinuousLinearMap.adjoint p)]
  simp only [map_sum, map_smul, sum_apply]
  apply Finset.sum_congr rfl
  intro b hb
  change _ = inner ℂ (finitePairEmbedding n (pairBasis b)) p • finitePairEmbedding n (Q (pairBasis b))
  rw [hc]

theorem countablePairAnnihilate_finite_restrict {n N : ℕ} (p : PairSpace n)
    (x : countableSector N) :
    countableRestrict n (countablePairAnnihilate N (finitePairEmbedding n p) x) =
      pairAnnihilate p (countableRestrict n x) := by
  rw [countablePairAnnihilate_finite_sum]
  simp only [map_sum, map_smul, countableRestrict_pairMode, pairAnnihilate,
    LinearMap.sum_apply, LinearMap.smul_apply]

theorem countablePairLift_finite_outer {n N : ℕ} (p q : PairSpace n)
    (x : Space n) (hx : InSector N x) :
    (countablePairLift N (InnerProductSpace.rankOne ℂ
      (finitePairEmbedding n p) (finitePairEmbedding n q))
        ⟨countableEmbed n x, countableEmbed_sector hx⟩ : CountableSpace) =
      countableEmbed n (pairLift (InnerProductSpace.rankOne ℂ p q).toLinearMap x) := by
  let y : countableSector N := ⟨countableEmbed n
    (pairLift (InnerProductSpace.rankOne ℂ p q).toLinearMap x),
      countableEmbed_sector (pairLift_preserves_sector _ hx)⟩
  have heq : countablePairLift N (InnerProductSpace.rankOne ℂ
      (finitePairEmbedding n p) (finitePairEmbedding n q))
        ⟨countableEmbed n x, countableEmbed_sector hx⟩ = y := by
    apply ext_inner_left ℂ
    intro z
    rw [countablePairLift_rankOne]
    change inner ℂ z ((countablePairAnnihilate N (finitePairEmbedding n p)).adjoint
      (countablePairAnnihilate N (finitePairEmbedding n q)
        ⟨countableEmbed n x, countableEmbed_sector hx⟩)) = _
    rw [ContinuousLinearMap.adjoint_inner_right, countablePairAnnihilate_finite_embed q x hx]
    change inner ℂ (countablePairAnnihilate N (finitePairEmbedding n p) z)
      (countableEmbed n (pairAnnihilate q x)) = inner ℂ (z : CountableSpace) (y : CountableSpace)
    calc
      _ = inner ℂ (countableRestrict n (countablePairAnnihilate N (finitePairEmbedding n p) z))
          (pairAnnihilate q x) :=
        (ContinuousLinearMap.adjoint_inner_left (countableEmbed n).toContinuousLinearMap
          (pairAnnihilate q x) (countablePairAnnihilate N (finitePairEmbedding n p) z)).symm
      _ = inner ℂ (pairAnnihilate p (countableRestrict n z)) (pairAnnihilate q x) := by
        rw [countablePairAnnihilate_finite_restrict]
      _ = inner ℂ (countableRestrict n z) (pairCreate p (pairAnnihilate q x)) := by
        rw [← pairAnnihilate_adjoint, LinearMap.adjoint_inner_right]
      _ = inner ℂ (z : CountableSpace) (countableEmbed n (pairCreate p (pairAnnihilate q x))) :=
        ContinuousLinearMap.adjoint_inner_left (countableEmbed n).toContinuousLinearMap _ _
      _ = _ := by simp only [y, pairLift_outer, Module.End.mul_apply]
  exact congrArg (fun z : countableSector N => (z : CountableSpace)) heq

/-- Exact agreement with the independently defined finite CAR Hamiltonian, for every n,N,Q. -/
theorem countablePairLift_finite_embed {n N : ℕ} (Q : Module.End ℂ (PairSpace n))
    (x : Space n) (hx : InSector N x) :
    (countablePairLift N (finitePairOperator Q)
      ⟨countableEmbed n x, countableEmbed_sector hx⟩ : CountableSpace) =
        countableEmbed n (pairLift Q x) := by
  rw [finitePairOperator_expansion, countablePairLift_sum]
  simp only [sum_apply, Submodule.coe_sum]
  simp_rw [countablePairLift_finite_outer _ _ x hx, pairLift_outer, Module.End.mul_apply,
    pairAnnihilate_basis]
  simp only [pairLift, LinearMap.sum_apply, Module.End.mul_apply, map_sum]

end VortexGap.Fermion
