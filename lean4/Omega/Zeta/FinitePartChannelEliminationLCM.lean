import Mathlib.Tactic

namespace Omega.Zeta

/-- Simultaneous channel elimination at level `n`: each torsion order in the finite family divides
`n`, so the corresponding component vanishes. -/
def finitePartChannelVanishing (orders : List ℕ) (n : ℕ) : Prop :=
  ∀ a, a ∈ orders → a ∣ n

/-- The minimal common annihilator suggested by the finite family of channel orders. -/
def finitePartChannelLCM (orders : List ℕ) : ℕ :=
  orders.foldr Nat.lcm 1

lemma dvd_finitePartChannelLCM {orders : List ℕ} {a : ℕ} (ha : a ∈ orders) :
    a ∣ finitePartChannelLCM orders := by
  induction orders with
  | nil =>
      cases ha
  | cons b bs ih =>
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · simp [finitePartChannelLCM]
        exact Nat.dvd_lcm_left a (finitePartChannelLCM bs)
      · exact dvd_trans (ih ha) (Nat.dvd_lcm_right b (finitePartChannelLCM bs))

lemma finitePartChannelLCM_dvd {orders : List ℕ} {n : ℕ}
    (hvanish : finitePartChannelVanishing orders n) :
    finitePartChannelLCM orders ∣ n := by
  induction orders with
  | nil =>
      simp [finitePartChannelLCM]
  | cons a as ih =>
      have ha : a ∣ n := hvanish a (by simp)
      have hrest : finitePartChannelVanishing as n := by
        intro b hb
        exact hvanish b (by simp [hb])
      have hlas : finitePartChannelLCM as ∣ n := ih hrest
      simpa [finitePartChannelLCM] using Nat.lcm_dvd ha hlas

/-- Paper-facing finite-channel elimination wrapper: simultaneous vanishing is equivalent to
componentwise vanishing, and the minimal common annihilator of the finitely many torsion orders is
their iterated `lcm`.
    cor:finite-part-channel-elimination-lcm -/
theorem paper_finite_part_channel_elimination_lcm (orders : List ℕ) :
    finitePartChannelVanishing orders (finitePartChannelLCM orders) ∧
      ∀ n, finitePartChannelVanishing orders n ↔ finitePartChannelLCM orders ∣ n := by
  refine ⟨?_, ?_⟩
  · intro a ha
    exact dvd_finitePartChannelLCM ha
  · intro n
    constructor
    · exact finitePartChannelLCM_dvd
    · intro hn a ha
      exact dvd_trans (dvd_finitePartChannelLCM ha) hn

end Omega.Zeta
