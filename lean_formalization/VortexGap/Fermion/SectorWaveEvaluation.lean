import VortexGap.Fermion.ExteriorPower

noncomputable section
namespace VortexGap.Fermion
variable {α : Type*} {n m N : ℕ}

def sectorWave (u : α → Fin n → ℂ) (x : particleSector n N) (z : Fin N → α) : ℂ :=
  ∑ a : Fin N → Fin n, (sectorTensorIsometry _ _ x).val a * ∏ i, u (z i) (a i)

theorem sectorWave_multiply (f : α → ℂ) (u : α → Fin n → ℂ) (x : particleSector n N)
    (z : Fin N → α) :
    sectorWave (fun y j => f y * u y j) x z = (∏ i, f (z i)) * sectorWave u x z := by
  simp only [sectorWave,Finset.prod_mul_distrib,Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => mul_left_comm _ _ _

theorem sectorWave_exterior (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m))
    (u : α → Fin m → ℂ) (x : particleSector n N) (z : Fin N → α) :
    sectorWave u (exteriorPower A N x) z =
      sectorWave (fun y j => ∑ k, A (PiLp.single 2 j 1) k * u y k) x z := by
  unfold sectorWave
  rw [exteriorPower_tensor]
  change (∑ a, (∑ b, tensorKernel A a b * (sectorTensorIsometry n N x).val b) *
    ∏ i, u (z i) (a i)) = _
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Fintype.prod_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [tensorKernel,Finset.prod_mul_distrib]
  ring

end VortexGap.Fermion
end
