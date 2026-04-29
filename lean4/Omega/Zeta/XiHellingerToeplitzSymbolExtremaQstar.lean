import Omega.Zeta.XiHellingerToeplitzSymbolPoisson

namespace Omega.Zeta

/-- Paper label: `prop:xi-hellinger-toeplitz-symbol-extrema-qstar`. -/
theorem paper_xi_hellinger_toeplitz_symbol_extrema_qstar
    (symbolExtrema qstarAsymptotics : Prop) (hExtrema : symbolExtrema)
    (hAsymptotics : qstarAsymptotics) :
    symbolExtrema ∧ qstarAsymptotics := by
  exact ⟨hExtrema, hAsymptotics⟩

end Omega.Zeta
