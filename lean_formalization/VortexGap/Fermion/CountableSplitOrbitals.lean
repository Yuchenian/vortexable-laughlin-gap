import VortexGap.Fermion.CountableSplitFields

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open scoped InnerProduct

/-- Relabel a complete orbital into a specified injective set of modes. -/
def countableOrbitalEmbedding (f : ℕ → ℕ) (hf : Function.Injective f) :
    CountableOrbital →ₗᵢ[ℂ] CountableOrbital :=
  (orbitalKet_orthonormal.comp f hf).orthogonalFamily.linearIsometry

theorem countableOrbitalEmbedding_ket (f : ℕ → ℕ) (hf : Function.Injective f) (j : ℕ) :
    countableOrbitalEmbedding f hf (orbitalKet j) = orbitalKet (f j) := by
  rw [countableOrbitalEmbedding, orbitalKet, OrthogonalFamily.linearIsometry_apply_single,
    LinearIsometry.toSpanSingleton_apply, one_smul]
  rfl

theorem countableOrbitalEmbedding_hasSum (f : ℕ → ℕ) (hf : Function.Injective f)
    (v : CountableOrbital) :
    HasSum (fun j => v j • orbitalKet (f j)) (countableOrbitalEmbedding f hf v) := by
  have h := (orbital_hasSum v).map
    (countableOrbitalEmbedding f hf).toContinuousLinearMap.toAddMonoidHom
    (countableOrbitalEmbedding f hf).continuous
  change HasSum (fun j => countableOrbitalEmbedding f hf (v j • orbitalKet j))
    (countableOrbitalEmbedding f hf v) at h
  simpa only [map_smul, countableOrbitalEmbedding_ket] using h

theorem countableOrbitalEmbedding_coordinate (f : ℕ → ℕ) (hf : Function.Injective f)
    (v : CountableOrbital) (j : ℕ) :
    countableOrbitalEmbedding f hf v (f j) = v j := by
  rw [← orbitalKet_inner_left, ← countableOrbitalEmbedding_ket f hf j,
    (countableOrbitalEmbedding f hf).inner_map_map, orbitalKet_inner_left]

theorem countableOrbitalEmbedding_outside (f : ℕ → ℕ) (hf : Function.Injective f)
    (v : CountableOrbital) (k : ℕ) (hk : ∀ j, f j ≠ k) :
    countableOrbitalEmbedding f hf v k = 0 := by
  have h := (countableOrbitalEmbedding_hasSum f hf v).map
    (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 k).toAddMonoidHom
    (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 k).continuous
  change HasSum (fun j => (v j • orbitalKet (f j)) k)
    (countableOrbitalEmbedding f hf v k) at h
  have hz (j : ℕ) : (v j • orbitalKet (f j)) k = 0 := by
    simp [orbitalKet, lp.single_apply, hk j, Ne.symm (hk j)]
  simp only [hz] at h
  exact h.unique hasSum_zero

def countableEnvOrbital : CountableOrbital →ₗᵢ[ℂ] CountableOrbital :=
  countableOrbitalEmbedding (fun j => Equiv.natSumNatEquivNat (Sum.inl j))
    (by intro i j h; exact Sum.inl.inj (Equiv.natSumNatEquivNat.injective h))

def countableSysOrbital : CountableOrbital →ₗᵢ[ℂ] CountableOrbital :=
  countableOrbitalEmbedding (fun j => Equiv.natSumNatEquivNat (Sum.inr j))
    (by intro i j h; exact Sum.inr.inj (Equiv.natSumNatEquivNat.injective h))

theorem countableEnvOrbital_ket (j : ℕ) :
    countableEnvOrbital (orbitalKet j) = countableEnvBasis j :=
  countableOrbitalEmbedding_ket _ _ j

theorem countableSysOrbital_ket (j : ℕ) :
    countableSysOrbital (orbitalKet j) = countableSysBasis j :=
  countableOrbitalEmbedding_ket _ _ j

theorem countableEnvOrbital_env_coordinate (v : CountableOrbital) (j : ℕ) :
    countableEnvOrbital v (Equiv.natSumNatEquivNat (Sum.inl j)) = v j :=
  countableOrbitalEmbedding_coordinate _ _ v j

theorem countableSysOrbital_sys_coordinate (v : CountableOrbital) (j : ℕ) :
    countableSysOrbital v (Equiv.natSumNatEquivNat (Sum.inr j)) = v j :=
  countableOrbitalEmbedding_coordinate _ _ v j

theorem countableEnvOrbital_sys_coordinate (v : CountableOrbital) (j : ℕ) :
    countableEnvOrbital v (Equiv.natSumNatEquivNat (Sum.inr j)) = 0 := by
  apply countableOrbitalEmbedding_outside
  intro i h
  have hi := Equiv.natSumNatEquivNat.injective h
  cases hi

theorem countableSysOrbital_env_coordinate (v : CountableOrbital) (j : ℕ) :
    countableSysOrbital v (Equiv.natSumNatEquivNat (Sum.inl j)) = 0 := by
  apply countableOrbitalEmbedding_outside
  intro i h
  have hi := Equiv.natSumNatEquivNat.injective h
  cases hi

theorem countableEnvSysOrbital_orthogonal (v w : CountableOrbital) :
    inner ℂ (countableEnvOrbital v) (countableSysOrbital w) = 0 := by
  rw [lp.inner_eq_tsum]
  have hz (k : ℕ) : inner ℂ (countableEnvOrbital v k) (countableSysOrbital w k) = 0 := by
    obtain ⟨s, rfl⟩ := Equiv.natSumNatEquivNat.surjective k
    cases s with
    | inl j => rw [countableSysOrbital_env_coordinate, inner_zero_right]
    | inr j => rw [countableEnvOrbital_sys_coordinate, inner_zero_left]
  simp only [hz, tsum_zero]

theorem countableEnvOrbital_norm (v : CountableOrbital) : ‖countableEnvOrbital v‖ = ‖v‖ :=
  countableEnvOrbital.norm_map v

theorem countableSysOrbital_norm (v : CountableOrbital) : ‖countableSysOrbital v‖ = ‖v‖ :=
  countableSysOrbital.norm_map v

/-- The CAR cross term vanishes for arbitrary orbitals in the two actual ranges. -/
theorem countableEnvSysOrbital_car (v w : CountableOrbital) (x : CountableSpace) :
    countableAnnihilate (countableEnvOrbital v) (countableCreate (countableSysOrbital w) x) =
      -countableCreate (countableSysOrbital w) (countableAnnihilate (countableEnvOrbital v) x) := by
  rw [countableAnnihilate_create, countableEnvSysOrbital_orthogonal, zero_smul, zero_sub]

end VortexGap.Fermion
