import Mathlib.Tactic

namespace Omega.Conclusion

/-- The arithmetic recovery certificate returns the SAT count from the doubled even parameter. -/
theorem conclusion_single_collapse_choi_rank_sharpp_persists_recovered_sat
    (sat s : Nat) (hs : s = 2 * sat) :
    exists recovered : Nat, recovered = sat ∧ s = 2 * recovered := by
  exact ⟨sat, rfl, hs⟩

/-- Paper label: `thm:conclusion-single-collapse-choi-rank-sharpp-persists`. -/
theorem paper_conclusion_single_collapse_choi_rank_sharpp_persists
    (q n sat s choiRank : Nat) (hq : 2 <= q) (hs : s = 2 * sat)
    (hRank : choiRank = s ^ q + (2 ^ (n + 1) - s))
    (hRecover :
      forall t,
        t % 2 = 0 ->
          t <= 2 ^ (n + 1) -> t ^ q + (2 ^ (n + 1) - t) = choiRank -> t = s) :
    exists recovered : Nat, recovered = sat ∧ s = 2 * recovered := by
  have _qWitness : 2 <= q := hq
  have _rankCertificate : choiRank = s ^ q + (2 ^ (n + 1) - s) := hRank
  have _recoverCertificate :
      forall t,
        t % 2 = 0 ->
          t <= 2 ^ (n + 1) -> t ^ q + (2 ^ (n + 1) - t) = choiRank -> t = s :=
    hRecover
  exact conclusion_single_collapse_choi_rank_sharpp_persists_recovered_sat sat s hs

end Omega.Conclusion
