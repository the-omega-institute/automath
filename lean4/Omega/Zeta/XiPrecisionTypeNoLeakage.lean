import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.ReadUsDeterministicTristate

namespace Omega.Zeta

/-- Paper label: `cor:xi-precision-type-no-leakage`. Missing typed certificates and explicit
mixed-precision mismatches both force the typed `Read_US` backend onto the `NULL` branch. -/
theorem paper_xi_precision_type_no_leakage
    (a : Omega.TypedAddressBiaxialCompletion.AddrUS)
    (Ver : Omega.TypedAddressBiaxialCompletion.TypedCertificate → Bool)
    (cert? : Option Omega.TypedAddressBiaxialCompletion.TypedCertificate)
    (hmixed : cert? = none ∨
      ∃ cert, cert? = some cert ∧
        Omega.TypedAddressBiaxialCompletion.precisionCompatible a cert = false) :
    Omega.TypedAddressBiaxialCompletion.Read_US a Ver cert? =
      Omega.TypedAddressBiaxialCompletion.ReadUSOutput.NULL := by
  have hnull :=
    (Omega.TypedAddressBiaxialCompletion.paper_xi_us_deterministic_tristate
      a Ver Ver cert? cert? (fun _ => rfl) rfl).2
  exact hnull.mpr <| by
    rcases hmixed with hnone | ⟨cert, hcert, hprec⟩
    · exact Or.inl hnone
    · exact Or.inr ⟨cert, hcert, Or.inl hprec⟩

end Omega.Zeta
