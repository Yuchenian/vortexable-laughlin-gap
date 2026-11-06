import VortexGap.Examples.PeriodicPhysical
import VortexGap.Physical.ShearBand
import VortexGap.Reference.CertifiedPlane

noncomputable section

namespace VortexGap.Fermion

/-- The existing plane reference adapter suffices for the entire positive
second-harmonic path, including the half-amplitude endpoint. -/
theorem periodic_path_old_gap (ell : ℝ) (hell : 0 < ell) {ε : ℝ} (hε : 0 ≤ ε)
    (hm : ε ≤ 1/2) (N : ℕ) :
    ∀ t ∈ spectrum ℝ (periodicEnvelopeHamiltonian ell hell hε (by linarith)
      (periodicMagneticWaveNumber ell 2) N), t = 0 ∨ (3/1000:ℝ) < t := by
  intro t ht
  have h := periodicEnvelope_physical_gap ell hell hε (by linarith) _ (1/1000) (1/25)
    (by norm_num) (periodicMagnetic_path ell hell ε hm) N (fun j _ => by simpa using countablePlane_old_bound j) t ht
  apply h.imp_right
  intro hb
  apply lt_of_lt_of_le _ hb
  have hh : (1/2:ℝ)^2 ≤ (1-ε)^2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
  unfold periodicGapBound
  norm_num at hh ⊢
  nlinarith

theorem shearPhysical_old_gap (a k ell : ℝ) (hk : k ≠ 0) (hell : 0 < ell) (N : ℕ) :
    ∀ t ∈ spectrum ℝ (shearHamiltonian a k ell hell N), t = 0 ∨ 1/25 ≤ t :=
  (shearPhysical_kernel_gap a k ell hk hell N (1/25) (by simpa using countablePlane_old_bound N)).2

end VortexGap.Fermion
