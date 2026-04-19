import Mathlib.Tactic

namespace Omega.GU

/-- The compact connected simple Lie types that can occur in the window-`6` discussion. -/
inductive CompactConnectedSimpleLieType
  | A | B | C | D | E6 | E7 | E8 | F4 | G2
  deriving DecidableEq, Repr

/-- The central elementary-abelian `2`-rank bound for each compact connected simple type. The
`D`-type case is the unique one reaching rank `2`; all others are at most rank `1`. -/
def centerTwoRank : CompactConnectedSimpleLieType → ℕ
  | .A => 1
  | .B => 1
  | .C => 1
  | .D => 2
  | .E6 => 0
  | .E7 => 1
  | .E8 => 0
  | .F4 => 0
  | .G2 => 0

private theorem centerTwoRank_lt_three (T : CompactConnectedSimpleLieType) :
    centerTwoRank T < 3 := by
  cases T <;> decide

/-- Data of a window-`6` envelope candidate whose three commuting boundary sheet-flips would have
to survive as central order-`2` directions inside a compact connected simple group. -/
structure Window6Center2RankExcludesSimpleGroupsData where
  envelope : CompactConnectedSimpleLieType
  boundaryCentralRank : ℕ
  boundaryCentralRank_eq_three : boundaryCentralRank = 3

/-- No compact connected simple envelope can realize the full rank-`3` boundary-center audit. -/
def Window6Center2RankExcludesSimpleGroupsData.no_compact_connected_simple_envelope
    (h : Window6Center2RankExcludesSimpleGroupsData) : Prop :=
  ¬ h.boundaryCentralRank ≤ centerTwoRank h.envelope

/-- The three boundary sheet-flips force a central `2`-rank of `3`, but every compact connected
simple Lie type has central `2`-rank at most `2`, so no such simple envelope exists.
    thm:window6-center-2rank-excludes-simple-groups -/
theorem paper_window6_center_2rank_excludes_simple_groups
    (h : Window6Center2RankExcludesSimpleGroupsData) : h.no_compact_connected_simple_envelope := by
  dsimp [Window6Center2RankExcludesSimpleGroupsData.no_compact_connected_simple_envelope]
  rw [h.boundaryCentralRank_eq_three]
  exact Nat.not_le_of_lt (centerTwoRank_lt_three h.envelope)

end Omega.GU
