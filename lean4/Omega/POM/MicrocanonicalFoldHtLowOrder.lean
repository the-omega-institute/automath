import Omega.POM.MicrocanonicalFoldHtFromPowerSums

namespace Omega.POM

open scoped BigOperators

section

variable {alpha : Type} [Fintype alpha]

/-- The normalized power sum used by the low-order microcanonical fold formulas. -/
noncomputable def cor_pom_microcanonical_fold_ht_low_order_powerSum
    (w : alpha → Real) (k : Nat) : Real :=
  if k = 1 then 1 else pom_microcanonical_fold_ht_from_power_sums_powerSum w k

/-- The low-order complete-homogeneous coefficients extracted from the normalized generating
series. -/
noncomputable def cor_pom_microcanonical_fold_ht_low_order_ht (w : alpha → Real) : Nat → Real
  | 2 => (1 + cor_pom_microcanonical_fold_ht_low_order_powerSum w 2) / 2
  | 3 =>
      (1 + 3 * cor_pom_microcanonical_fold_ht_low_order_powerSum w 2 +
        2 * cor_pom_microcanonical_fold_ht_low_order_powerSum w 3) / 6
  | 4 =>
      (1 + 6 * cor_pom_microcanonical_fold_ht_low_order_powerSum w 2 +
        3 * (cor_pom_microcanonical_fold_ht_low_order_powerSum w 2) ^ 2 +
        8 * cor_pom_microcanonical_fold_ht_low_order_powerSum w 3 +
        6 * cor_pom_microcanonical_fold_ht_low_order_powerSum w 4) / 24
  | 5 =>
      (1 + 10 * cor_pom_microcanonical_fold_ht_low_order_powerSum w 2 +
        15 * (cor_pom_microcanonical_fold_ht_low_order_powerSum w 2) ^ 2 +
        20 * cor_pom_microcanonical_fold_ht_low_order_powerSum w 3 +
        20 * cor_pom_microcanonical_fold_ht_low_order_powerSum w 2 *
          cor_pom_microcanonical_fold_ht_low_order_powerSum w 3 +
        30 * cor_pom_microcanonical_fold_ht_low_order_powerSum w 4 +
        24 * cor_pom_microcanonical_fold_ht_low_order_powerSum w 5) / 120
  | _ => 0

local notation "pomPowerSum" => cor_pom_microcanonical_fold_ht_low_order_powerSum
local notation "pomHt" => cor_pom_microcanonical_fold_ht_low_order_ht

theorem paper_pom_microcanonical_fold_ht_low_order {alpha : Type} [Fintype alpha]
    (w : alpha -> Real) :
    pomHt w 2 = (1 + pomPowerSum w 2) / 2 ∧
      pomHt w 3 = (1 + 3 * pomPowerSum w 2 + 2 * pomPowerSum w 3) / 6 ∧
      pomHt w 4 =
        (1 + 6 * pomPowerSum w 2 + 3 * (pomPowerSum w 2)^2 + 8 * pomPowerSum w 3 +
          6 * pomPowerSum w 4) / 24 ∧
      pomHt w 5 =
        (1 + 10 * pomPowerSum w 2 + 15 * (pomPowerSum w 2)^2 + 20 * pomPowerSum w 3 +
          20 * pomPowerSum w 2 * pomPowerSum w 3 + 30 * pomPowerSum w 4 +
          24 * pomPowerSum w 5) / 120 := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  · rfl

end

end Omega.POM
