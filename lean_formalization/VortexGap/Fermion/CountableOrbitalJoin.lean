import VortexGap.Fermion.CountableEnvironmentFields
import VortexGap.Operator.LossDefect
noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open Filter
open scoped InnerProduct

def countableOrbitalJoinLinear : Doubled CountableOrbital →ₗ[ℂ] CountableOrbital where
  toFun z := countableEnvOrbital z.fst + countableSysOrbital z.snd
  map_add' z w := by simp; abel
  map_smul' c z := by simp [smul_add]

theorem countableOrbitalJoinLinear_inner (z w : Doubled CountableOrbital) :
    inner ℂ (countableOrbitalJoinLinear z) (countableOrbitalJoinLinear w) = inner ℂ z w := by
  change inner ℂ (countableEnvOrbital z.fst + countableSysOrbital z.snd)
    (countableEnvOrbital w.fst + countableSysOrbital w.snd) =
      inner ℂ z.fst w.fst + inner ℂ z.snd w.snd
  rw [inner_add_left, inner_add_right, inner_add_right,
    countableEnvOrbital.inner_map_map, countableSysOrbital.inner_map_map,
    countableEnvSysOrbital_orthogonal]
  have h : inner ℂ (countableSysOrbital z.snd) (countableEnvOrbital w.fst) = 0 := by
    rw [← inner_conj_symm, countableEnvSysOrbital_orthogonal, map_zero]
  rw [h]; simp

def countableOrbitalJoinIsometry : Doubled CountableOrbital →ₗᵢ[ℂ] CountableOrbital :=
  countableOrbitalJoinLinear.isometryOfInner countableOrbitalJoinLinear_inner

theorem countableOrbitalJoinIsometry_ket_range (j : ℕ) :
    orbitalKet j ∈ countableOrbitalJoinIsometry.toLinearMap.range := by
  obtain ⟨s,rfl⟩ := Equiv.natSumNatEquivNat.surjective j
  cases s with
  | inl k =>
    refine ⟨WithLp.toLp 2 (orbitalKet k, (0 : CountableOrbital)), ?_⟩
    change countableEnvOrbital (orbitalKet k) + countableSysOrbital 0 = _
    rw [map_zero, add_zero, countableEnvOrbital_ket]; rfl
  | inr k =>
    refine ⟨WithLp.toLp 2 ((0 : CountableOrbital), orbitalKet k), ?_⟩
    change countableEnvOrbital 0 + countableSysOrbital (orbitalKet k) = _
    rw [map_zero, zero_add, countableSysOrbital_ket]; rfl

theorem countableOrbitalJoinIsometry_surjective : Function.Surjective countableOrbitalJoinIsometry := by
  intro v
  change v ∈ countableOrbitalJoinIsometry.toLinearMap.range
  have hc : IsClosed (countableOrbitalJoinIsometry.toLinearMap.range : Set CountableOrbital) :=
    countableOrbitalJoinIsometry.isometry.isClosedEmbedding.isClosed_range
  apply hc.mem_of_tendsto (orbital_hasSum v)
  apply Eventually.of_forall
  intro s
  apply countableOrbitalJoinIsometry.toLinearMap.range.sum_mem
  intro j hj
  exact countableOrbitalJoinIsometry.toLinearMap.range.smul_mem (v j)
    (countableOrbitalJoinIsometry_ket_range j)

def countableOrbitalJoin : Doubled CountableOrbital ≃ₗᵢ[ℂ] CountableOrbital :=
  LinearIsometryEquiv.ofSurjective countableOrbitalJoinIsometry countableOrbitalJoinIsometry_surjective

theorem countableOrbitalJoin_apply (v w : CountableOrbital) :
    countableOrbitalJoin (WithLp.toLp 2 (v,w)) = countableEnvOrbital v + countableSysOrbital w := rfl
end VortexGap.Fermion
