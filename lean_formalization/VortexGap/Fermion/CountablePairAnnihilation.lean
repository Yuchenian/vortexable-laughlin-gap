import VortexGap.Fermion.CountablePairContraction

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open Filter
open scoped InnerProduct BigOperators ComplexConjugate Topology

/-- B(p) on the complete N-particle sector, with its actual CAR pair coefficients. -/
def countablePairAnnihilate (N : ℕ) (p : CountablePairSpace) :
    countableSector N →L[ℂ] CountableSpace :=
  (countablePairContract p).comp (countablePairStack N)

theorem countablePairAnnihilate_apply {N : ℕ} (p : CountablePairSpace) (x : countableSector N) :
    countablePairAnnihilate N p x = ∑' a, conj (p a) • countablePairMode a x := rfl

theorem countablePairAnnihilate_hasSum {N : ℕ} (p : CountablePairSpace) (x : countableSector N) :
    HasSum (fun a => conj (p a) • countablePairMode a x) (countablePairAnnihilate N p x) :=
  countablePairContract_hasSum p (countablePairStack N x)

theorem countablePairAnnihilate_norm_summable {N : ℕ} (p : CountablePairSpace)
    (x : countableSector N) : Summable (fun a => ‖conj (p a) • countablePairMode a x‖) :=
  countablePairContract_norm_summable p (countablePairStack N x)

theorem countablePairAnnihilate_opNorm_le (N : ℕ) (p : CountablePairSpace) :
    ‖countablePairAnnihilate N p‖ ≤ Real.sqrt (N.choose 2 : ℝ) * ‖p‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  intro x
  calc
    _ ≤ ‖p‖ * ‖countablePairStack N x‖ := countablePairContractLinear_norm_le p _
    _ = _ := by rw [countablePairStack_norm]; ring

theorem countablePairAnnihilate_norm_le {N : ℕ} (p : CountablePairSpace) (x : countableSector N) :
    ‖countablePairAnnihilate N p x‖ ≤ Real.sqrt (N.choose 2 : ℝ) * ‖p‖ * ‖x‖ :=
  ((countablePairAnnihilate N p).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (countablePairAnnihilate_opNorm_le N p) (norm_nonneg _))

theorem countablePairAnnihilate_add (N : ℕ) (p q : CountablePairSpace) :
    countablePairAnnihilate N (p + q) = countablePairAnnihilate N p + countablePairAnnihilate N q := by
  apply ContinuousLinearMap.ext
  intro x
  change countablePairContract (p + q) (countablePairStack N x) = _
  rw [countablePairContract_add]
  rfl

theorem countablePairAnnihilate_smul (N : ℕ) (c : ℂ) (p : CountablePairSpace) :
    countablePairAnnihilate N (c • p) = conj c • countablePairAnnihilate N p := by
  apply ContinuousLinearMap.ext
  intro x
  change countablePairContract (c • p) (countablePairStack N x) = _
  rw [countablePairContract_smul]
  rfl

theorem countablePairAnnihilate_single {N : ℕ} (a : CountablePairIndex) (c : ℂ)
    (x : countableSector N) :
    countablePairAnnihilate N (lp.single 2 a c) x = conj c • countablePairMode a x :=
  countablePairContract_single a c (countablePairStack N x)

theorem countablePairAnnihilate_sector {N : ℕ} (p : CountablePairSpace)
    (x : countableSector (N + 2)) :
    countablePairAnnihilate (N + 2) p x ∈ countableSector N := by
  apply (countableSector_isClosed N).mem_of_tendsto (countablePairAnnihilate_hasSum p x)
  exact Eventually.of_forall fun s => (countableSector N).sum_mem fun a ha =>
    (countableSector N).smul_mem (conj (p a)) (countablePairMode_sector a x.property)

theorem countablePairAnnihilate_zero_sector (p : CountablePairSpace) :
    countablePairAnnihilate 0 p = 0 := by
  ext x A
  change countablePairContract p (countablePairStack 0 x) A = 0
  rw [countablePairStack_zero]
  simp

theorem countablePairAnnihilate_one_sector (p : CountablePairSpace) :
    countablePairAnnihilate 1 p = 0 := by
  ext x A
  change countablePairContract p (countablePairStack 1 x) A = 0
  rw [countablePairStack_one]
  simp

theorem countablePairAnnihilate_pairEmbedding (p q : CountablePairSpace) :
    countablePairAnnihilate 2 p ⟨countablePairEmbedding q, countablePairEmbedding_sector q⟩ =
      (inner ℂ p q) • countableKet ∅ := by
  have h : Summable (fun a => conj (p a) * q a) := by
    have hi := lp.summable_inner (𝕜 := ℂ) p q
    change Summable (fun a => q a * conj (p a)) at hi
    simpa only [mul_comm] using hi
  rw [countablePairAnnihilate_apply]
  simp_rw [countablePairMode_pairEmbedding, smul_smul]
  rw [h.tsum_smul_const]
  congr 1
  rw [lp.inner_eq_tsum]
  apply tsum_congr
  intro a
  simp only [RCLike.inner_apply, mul_comm]

theorem countablePairAnnihilate_finite_sum {n N : ℕ} (p : PairSpace n) (x : countableSector N) :
    countablePairAnnihilate N (finitePairEmbedding n p) x =
      ∑ a : PairIndex n, conj (p a) • countablePairMode (pairIndexNat a) x := by
  classical
  let s : Finset CountablePairIndex := Finset.univ.image (@pairIndexNat n)
  have hz (a : CountablePairIndex) (ha : a ∉ s) : finitePairEmbedding n p a = 0 := by
    apply finitePairEmbedding_outside
    by_contra h
    have hlt : a.val.2 < n := Nat.lt_of_not_ge h
    let b : PairIndex n :=
      ⟨(⟨a.val.1, lt_trans a.property hlt⟩, ⟨a.val.2, hlt⟩), a.property⟩
    exact ha (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩)
  rw [countablePairAnnihilate_apply, tsum_eq_sum (s := s) (fun a ha => by
    rw [hz a ha, map_zero]
    ext A
    change (0 : ℂ) * countablePairMode a x A = 0
    exact zero_mul _)]
  dsimp [s]
  rw [Finset.sum_image (pairIndexNat_injective n).injOn]
  apply Finset.sum_congr rfl
  intro a ha
  rw [finitePairEmbedding_coefficient]

/-- Exact agreement with the old finite CAR implementation, on every finite-mode N-state. -/
theorem countablePairAnnihilate_finite_embed {n N : ℕ} (p : PairSpace n)
    (x : Space n) (hx : InSector N x) :
    countablePairAnnihilate N (finitePairEmbedding n p) ⟨countableEmbed n x, countableEmbed_sector hx⟩ =
      countableEmbed n (pairAnnihilate p x) := by
  rw [countablePairAnnihilate_finite_sum]
  simp only [countablePairMode_embed]
  simp only [pairAnnihilate, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]

end VortexGap.Fermion

