import Mathlib.Tactic
import Omega.Conclusion.ScreenRelativeBettiRenyiFlatness

namespace Omega.Conclusion

namespace ScreenFlatFiberData

/-- The `q`-collision moment of a flat fiber law. -/
def collisionMoment (D : ScreenFlatFiberData) (q : Nat) : ℚ :=
  (1 : ℚ) / ((2 : ℚ) ^ ((q - 1) * D.renyiCond q))

/-- The associated Hankel entry at position `(i, j)`. -/
def hankelEntry (D : ScreenFlatFiberData) (i j : Nat) : ℚ :=
  D.collisionMoment (i + j + 1)

/-- Left geometric factor in the rank-one decomposition. -/
def hankelLeftFactor (D : ScreenFlatFiberData) (i : Nat) : ℚ :=
  (1 : ℚ) / ((2 : ℚ) ^ (i * D.beta))

/-- Right geometric factor in the rank-one decomposition. -/
def hankelRightFactor (D : ScreenFlatFiberData) (j : Nat) : ℚ :=
  (1 : ℚ) / ((2 : ℚ) ^ (j * D.beta))

/-- The Hankel matrix factors as an outer product of two geometric sequences. -/
def hankelRankOne (D : ScreenFlatFiberData) : Prop :=
  ∀ i j : Nat, D.hankelEntry i j = D.hankelLeftFactor i * D.hankelRightFactor j

lemma collisionMoment_closed_form (D : ScreenFlatFiberData) (q : Nat) (_hq : 1 ≤ q) :
    D.collisionMoment q = (1 : ℚ) / ((2 : ℚ) ^ ((q - 1) * D.beta)) := by
  rcases paper_conclusion_relative_betti_renyi_flatness D with ⟨_, _, _, hRenyi, _⟩
  simp [collisionMoment, hRenyi q]

lemma hankel_rank_one (D : ScreenFlatFiberData) : D.hankelRankOne := by
  rcases paper_conclusion_relative_betti_renyi_flatness D with ⟨_, _, _, hRenyi, _⟩
  intro i j
  have hpowi : (2 : ℚ) ^ (i * D.beta) ≠ 0 := by positivity
  have hpowj : (2 : ℚ) ^ (j * D.beta) ≠ 0 := by positivity
  unfold hankelEntry hankelLeftFactor hankelRightFactor collisionMoment
  rw [hRenyi (i + j + 1)]
  have hsucc : i + j + 1 - 1 = i + j := by omega
  rw [hsucc, Nat.add_mul, pow_add]
  field_simp [hpowi, hpowj]

end ScreenFlatFiberData

open ScreenFlatFiberData

/-- Paper label: `thm:conclusion-screen-collision-moment-hankel-rank-one`. -/
theorem paper_conclusion_screen_collision_moment_hankel_rank_one (D : ScreenFlatFiberData) :
    (∀ q : Nat, 1 ≤ q → D.collisionMoment q = (1 : ℚ) / ((2 : ℚ) ^ ((q - 1) * D.beta))) ∧
      D.hankelRankOne := by
  exact ⟨D.collisionMoment_closed_form, D.hankel_rank_one⟩

end Omega.Conclusion
