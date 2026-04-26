import Omega.Zeta.XiTimePart63bLogcmPhiadicJetDeterminesEvenZeta

namespace Omega.Zeta

/-- Equality of the recovered even Bernoulli coefficients and the zeta prefactors forces equality
of the transported even zeta tower.
    cor:xi-time-part63b-logcm-asymptotic-germ-faithful-even-zeta -/
theorem paper_xi_time_part63b_logcm_asymptotic_germ_faithful_even_zeta
    (D D' : Omega.Zeta.xi_time_part63b_logcm_phiadic_jet_determines_even_zeta_data)
    (hBern :
      ∀ r, 1 ≤ r → D.bernoulliCoeff (2 * r) = D'.bernoulliCoeff (2 * r))
    (hPref : ∀ r, D.zetaPrefactor r = D'.zetaPrefactor r) :
    (∀ r, 1 ≤ r → D.bernoulliCoeff (2 * r) = D'.bernoulliCoeff (2 * r)) ∧
      (∀ r, 1 ≤ r → D.evenZetaValue (2 * r) = D'.evenZetaValue (2 * r)) := by
  constructor
  · exact hBern
  · intro r hr
    calc
      D.evenZetaValue (2 * r) = D.zetaPrefactor r * D.bernoulliCoeff (2 * r) :=
        D.bernoulli_zeta r hr
      _ = D'.zetaPrefactor r * D'.bernoulliCoeff (2 * r) := by
        rw [hPref r, hBern r hr]
      _ = D'.evenZetaValue (2 * r) := (D'.bernoulli_zeta r hr).symm

end Omega.Zeta
