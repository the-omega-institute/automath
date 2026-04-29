namespace Omega.Zeta

/-- Paper label: `prop:xi-hankel-det-reach-observe-factorization-padic`. -/
theorem paper_xi_hankel_det_reach_observe_factorization_padic
    (hankelFactorization determinantFactorization padicRigidity : Prop)
    (hH : hankelFactorization) (hdet : determinantFactorization) (hpadic : padicRigidity) :
    hankelFactorization ∧ determinantFactorization ∧ padicRigidity := by
  exact ⟨hH, hdet, hpadic⟩

end Omega.Zeta
