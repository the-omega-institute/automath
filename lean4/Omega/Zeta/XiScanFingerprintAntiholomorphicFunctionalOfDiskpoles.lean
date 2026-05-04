import Mathlib

namespace Omega.Zeta

noncomputable section

/-- Concrete scan-fingerprint data for the finite disk-pole model. The atom family is finite,
the scan sequence has the recorded Fourier expansion, and the Phi-node formula identifies each
Fourier atom with the antiholomorphic disk-pole node. -/
structure xi_scan_fingerprint_antiholomorphic_functional_of_diskpoles_Data where
  atomCount : ℕ
  diskPole : Fin atomCount → ℂ
  phiNode : Fin atomCount → ℂ
  atomWeight : Fin atomCount → ℂ
  scanSequence : ℕ → ℂ
  hFourierExpansion :
    ∀ n : ℕ, scanSequence n = ∑ j : Fin atomCount, atomWeight j * phiNode j ^ n
  hAntiholomorphicPhiNode : ∀ j : Fin atomCount, phiNode j = star (diskPole j)

namespace xi_scan_fingerprint_antiholomorphic_functional_of_diskpoles_Data

/-- The closed disk-pole form of the scan sequence. -/
def closedForm (D : xi_scan_fingerprint_antiholomorphic_functional_of_diskpoles_Data) : Prop :=
  ∀ n : ℕ, D.scanSequence n = ∑ j : Fin D.atomCount, D.atomWeight j * star (D.diskPole j) ^ n

end xi_scan_fingerprint_antiholomorphic_functional_of_diskpoles_Data

/-- Paper label: `prop:xi-scan-fingerprint-antiholomorphic-functional-of-diskpoles`.
The stored finite Fourier expansion becomes the disk-pole closed form after rewriting each
Phi-node by the antiholomorphic conjugacy identity. -/
theorem paper_xi_scan_fingerprint_antiholomorphic_functional_of_diskpoles
    (D : xi_scan_fingerprint_antiholomorphic_functional_of_diskpoles_Data) :
    D.closedForm := by
  intro n
  rw [D.hFourierExpansion n]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [D.hAntiholomorphicPhiNode j]

end
end Omega.Zeta
