import OAI.Analysis.Laughlin.Spin.Representation
import VortexGap.Geometry.SphereRadial

noncomputable section
set_option autoImplicit false
namespace VortexGap.Fermion
open OAI.Laughlin.Rotation
open scoped Matrix

/-- The two highest-weight columns in the rotated spin-(n+1)/2 representation. -/
def sphereSpinColumns (n : ℕ) (g : SourceSU2) :
    Matrix (Fin (n+1+1)) (Fin 2) ℂ :=
  fun i j => sourceSpinRepresentation (n+1) g i (Fin.castLE (by omega) j)

/-- All four overlaps are entries of a single relative rotation. -/
theorem sphereSpinColumns_overlap (n : ℕ) (g h : SourceSU2) (i j : Fin 2) :
    ((sphereSpinColumns n g)ᴴ * sphereSpinColumns n h) i j =
      sourceSpinRepresentation (n+1) (g⁻¹*h)
        (Fin.castLE (by omega) i) (Fin.castLE (by omega) j) := by
  let ρ := sourceSpinRepresentation (n+1)
  have hu : (ρ g)ᴴ * ρ g = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (sourceSpinRepresentation_unitary _ g)
  have hinv : (ρ g)ᴴ = ρ g⁻¹ := by
    calc
      _ = (ρ g)ᴴ * (ρ g * ρ g⁻¹) := by rw [← map_mul, mul_inv_cancel, map_one, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hu, Matrix.one_mul]
  change ((ρ g)ᴴ * ρ h) _ _ = ρ (g⁻¹*h) _ _
  rw [hinv, map_mul]

theorem sphereSpinColumns_orthonormal (n : ℕ) (g : SourceSU2) :
    (sphereSpinColumns n g)ᴴ * sphereSpinColumns n g = 1 := by
  ext i j
  rw [sphereSpinColumns_overlap, inv_mul_cancel, map_one]
  simp [Matrix.one_apply]

end VortexGap.Fermion
