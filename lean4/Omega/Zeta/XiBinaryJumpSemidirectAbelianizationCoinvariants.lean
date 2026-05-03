import Mathlib.Logic.Equiv.Prod

namespace Omega.Zeta

/-- Paper label: `thm:xi-binary-jump-semidirect-abelianization-coinvariants`. -/
def paper_xi_binary_jump_semidirect_abelianization_coinvariants
    {Wab VG Gab : Type} (orbitCount : Nat) (hab : Wab ≃ VG × Gab)
    (hcoinv : VG ≃ (Fin orbitCount → Bool)) :
    Wab ≃ (Fin orbitCount → Bool) × Gab := by
  exact hab.trans (Equiv.prodCongr hcoinv (Equiv.refl Gab))

end Omega.Zeta
