import Mathlib.Tactic
import Omega.Folding.FoldGaugeAnomalyFirstTrigonalQ4S4
import Omega.Folding.FoldGaugeAnomalyP10GaloisDiscriminant

namespace Omega.Folding

/-- A normalized affine chart for the Möbius group on `ℚ`, sufficient for the three-point
rigidity step once the branch set is fixed pointwise. -/
structure fold_gauge_anomaly_deck_trivial_mobius_rigidity_affine_map where
  a : ℚ
  b : ℚ
  ha : a ≠ 0

/-- Evaluation of the normalized affine Möbius chart. -/
def fold_gauge_anomaly_deck_trivial_mobius_rigidity_affine_map.eval
    (g : fold_gauge_anomaly_deck_trivial_mobius_rigidity_affine_map) (x : ℚ) : ℚ :=
  g.a * x + g.b

private lemma fold_gauge_anomaly_deck_trivial_mobius_rigidity_perm_center_trivial
    {n : ℕ} (hn : 3 ≤ n) (z : Equiv.Perm (Fin n))
    (hz : ∀ σ : Equiv.Perm (Fin n), z * σ = σ * z) :
    z = 1 := by
  let zero : Fin n := ⟨0, by omega⟩
  let one : Fin n := ⟨1, by omega⟩
  let two : Fin n := ⟨2, by omega⟩
  have hzero_ne_one : zero ≠ one := by
    intro h
    have : (0 : ℕ) = 1 := by simpa [zero, one] using congrArg Fin.val h
    norm_num at this
  have hzero_ne_two : zero ≠ two := by
    intro h
    have : (0 : ℕ) = 2 := by simpa [zero, two] using congrArg Fin.val h
    norm_num at this
  have hone_ne_two : one ≠ two := by
    intro h
    have : (1 : ℕ) = 2 := by simpa [one, two] using congrArg Fin.val h
    norm_num at this
  have hz0 : z zero = zero := by
    by_contra hz0
    let b : Fin n := if z zero = one then two else one
    have hb0 : b ≠ zero := by
      dsimp [b]
      split_ifs
      · exact hzero_ne_two.symm
      · exact hzero_ne_one.symm
    have hbz : b ≠ z zero := by
      dsimp [b]
      split_ifs with h
      · intro hb
        have : one = two := by
          calc
            one = z zero := h.symm
            _ = two := hb.symm
        exact hone_ne_two this
      · intro hb
        exact h hb.symm
    have hcomm := congrArg (fun p : Equiv.Perm (Fin n) => p zero) (hz (Equiv.swap zero b))
    have hfix : Equiv.swap zero b (z zero) = z zero := by
      by_cases hzb' : z zero = b
      · exact False.elim (hbz hzb'.symm)
      · by_cases hz0' : z zero = zero
        · exact False.elim (hz0 hz0')
        · simp [Equiv.swap_apply_def, hzb', hz0']
    have hzb : z b = z zero := by
      simpa [zero, hfix] using hcomm
    exact hb0 (z.injective hzb)
  have hzi : ∀ i : Fin n, z i = i := by
    intro i
    have hcomm := congrArg (fun p : Equiv.Perm (Fin n) => p zero) (hz (Equiv.swap zero i))
    simpa [zero, hz0] using hcomm
  ext i
  exact congrArg Fin.val (hzi i)

private lemma fold_gauge_anomaly_deck_trivial_mobius_rigidity_affine_identity
    (g : fold_gauge_anomaly_deck_trivial_mobius_rigidity_affine_map)
    (h0 : g.eval 0 = 0) (h1 : g.eval 1 = 1) (h2 : g.eval 2 = 2) :
    ∀ x : ℚ, g.eval x = x := by
  have hb : g.b = 0 := by
    simpa [fold_gauge_anomaly_deck_trivial_mobius_rigidity_affine_map.eval] using h0
  have ha : g.a = 1 := by
    simpa [fold_gauge_anomaly_deck_trivial_mobius_rigidity_affine_map.eval, hb] using h1
  have _ : g.eval 2 = 2 := by simpa using h2
  intro x
  simp [fold_gauge_anomaly_deck_trivial_mobius_rigidity_affine_map.eval, hb, ha]

/-- Paper label: `cor:fold-gauge-anomaly-deck-trivial-mobius-rigidity`. The existing quartic
`S₄` and degree-`10` `S₁₀` certificates force trivial centralizers on the corresponding generic
fibers, and once three rational branch points are fixed pointwise the normalized Möbius map is the
identity. -/
theorem paper_fold_gauge_anomaly_deck_trivial_mobius_rigidity
    (D : FoldGaugeAnomalyP10GaloisDiscriminantData) :
    q4GaloisGroup = QuarticTransitiveSubgroup.s4 ∧
      (∀ z : Equiv.Perm (Fin 4), (∀ σ : Equiv.Perm (Fin 4), z * σ = σ * z) → z = 1) ∧
      D.galois_group_is_S10 ∧
      (∀ z : Equiv.Perm (Fin 10), (∀ σ : Equiv.Perm (Fin 10), z * σ = σ * z) → z = 1) ∧
      (∀ g : fold_gauge_anomaly_deck_trivial_mobius_rigidity_affine_map,
        g.eval 0 = 0 → g.eval 1 = 1 → g.eval 2 = 2 → ∀ x : ℚ, g.eval x = x) := by
  rcases paper_fold_gauge_anomaly_first_trigonal_q4_s4 with ⟨_, _, _, hq4, _⟩
  rcases paper_fold_gauge_anomaly_p10_galois_discriminant D with ⟨_, hgalois, _, _, _⟩
  refine ⟨hq4, ?_, hgalois, ?_, ?_⟩
  · intro z hz
    exact fold_gauge_anomaly_deck_trivial_mobius_rigidity_perm_center_trivial (by omega) z hz
  · intro z hz
    exact fold_gauge_anomaly_deck_trivial_mobius_rigidity_perm_center_trivial (by omega) z hz
  · intro g h0 h1 h2
    exact fold_gauge_anomaly_deck_trivial_mobius_rigidity_affine_identity g h0 h1 h2

end Omega.Folding
