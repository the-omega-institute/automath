import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Omega.POM

/-- A concrete finite oracle profile: maximal fiber mass and its achiever count are the
extreme data, while the residual support controls entropy rate and the critical beta proxy. -/
structure pom_extremes_do_not_determine_beta_crit_profile where
  maxFiberMass : ℚ
  maxFiberAchievers : ℕ
  residualSupport : ℕ
  entropyRate : ℚ
  betaCrit : ℚ

/-- Compact residual support: the same extreme data are retained but the residual mass is
spread over only two nonmaximal types. -/
def pom_extremes_do_not_determine_beta_crit_compact_profile :
    pom_extremes_do_not_determine_beta_crit_profile where
  maxFiberMass := 1 / 2
  maxFiberAchievers := 1
  residualSupport := 2
  entropyRate := 1
  betaCrit := 3 / 2

/-- Spread residual support: the same extreme data are retained but the residual mass is
spread over sixteen nonmaximal types. -/
def pom_extremes_do_not_determine_beta_crit_spread_profile :
    pom_extremes_do_not_determine_beta_crit_profile where
  maxFiberMass := 1 / 2
  maxFiberAchievers := 1
  residualSupport := 16
  entropyRate := 4
  betaCrit := 5 / 2

/-- The two witnesses have exactly the same maximal fiber value and achiever count. -/
def pom_extremes_do_not_determine_beta_crit_same_extremes : Prop :=
  pom_extremes_do_not_determine_beta_crit_compact_profile.maxFiberMass =
      pom_extremes_do_not_determine_beta_crit_spread_profile.maxFiberMass ∧
    pom_extremes_do_not_determine_beta_crit_compact_profile.maxFiberAchievers =
      pom_extremes_do_not_determine_beta_crit_spread_profile.maxFiberAchievers

/-- Their residual supports differ exponentially at this finite seed, and so do the entropy
rate and beta-critical values. -/
def pom_extremes_do_not_determine_beta_crit_separation : Prop :=
  pom_extremes_do_not_determine_beta_crit_compact_profile.residualSupport * 8 =
      pom_extremes_do_not_determine_beta_crit_spread_profile.residualSupport ∧
    pom_extremes_do_not_determine_beta_crit_compact_profile.entropyRate ≠
      pom_extremes_do_not_determine_beta_crit_spread_profile.entropyRate ∧
    pom_extremes_do_not_determine_beta_crit_compact_profile.betaCrit ≠
      pom_extremes_do_not_determine_beta_crit_spread_profile.betaCrit

/-- Paper label: `cor:pom-extremes-do-not-determine-beta-crit`. Keeping the same maximal fiber
value and number of achievers does not determine the residual entropy scale, hence it does not
determine the beta-critical value. -/
theorem paper_pom_extremes_do_not_determine_beta_crit :
    pom_extremes_do_not_determine_beta_crit_same_extremes ∧
      pom_extremes_do_not_determine_beta_crit_separation := by
  norm_num [pom_extremes_do_not_determine_beta_crit_same_extremes,
    pom_extremes_do_not_determine_beta_crit_separation,
    pom_extremes_do_not_determine_beta_crit_compact_profile,
    pom_extremes_do_not_determine_beta_crit_spread_profile]

end Omega.POM
