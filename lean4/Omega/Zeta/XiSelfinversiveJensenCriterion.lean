import Mathlib.Tactic
import Omega.Zeta.XiSelfreciprocalEscapeJensen

namespace Omega.Zeta

/-- Unit-circle purity for a finite self-inversive root-radius ledger. -/
def xi_selfinversive_jensen_criterion_unitCirclePure
    {n : ℕ} (radius : Fin n → ℝ) : Prop :=
  ∀ j : Fin n, radius j = 1

/-- Disk zero-freeness for the finite radius ledger: no recorded root lies in `|y| < 1`. -/
def xi_selfinversive_jensen_criterion_diskZeroFree
    {n : ℕ} (radius : Fin n → ℝ) : Prop :=
  ∀ j : Fin n, ¬ radius j < 1

/-- A Jensen-defect oracle for the finite radius ledger: at radius `ρ`, zero defect is exactly
the assertion that the ledger has no root in the smaller disk `|y| < ρ`. -/
def xi_selfinversive_jensen_criterion_jensenZeroCounting
    {n : ℕ} (radius : Fin n → ℝ) (jensenDefect : ℝ → ℝ) : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
    (jensenDefect ρ = 0 ↔ ∀ j : Fin n, ¬ radius j < ρ)

/-- Vanishing of the finite Jensen defect on every subunit radius. -/
def xi_selfinversive_jensen_criterion_jensenVanishes
    (jensenDefect : ℝ → ℝ) : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ρ < 1 → jensenDefect ρ = 0

/-- Concrete finite-radius wrapper for the self-inversive Jensen criterion.  It records the
three equivalent conditions from the paper: all roots lie on the unit circle, no root lies in the
open unit disk, and the Jensen defect vanishes on every subunit radius. -/
def xi_selfinversive_jensen_criterion_statement : Prop :=
  ∀ {n : ℕ} (radius : Fin n → ℝ) (jensenDefect : ℝ → ℝ),
    (∀ j : Fin n, 0 < radius j) →
    xi_selfreciprocal_escape_jensen_rootPairing radius →
    xi_selfinversive_jensen_criterion_jensenZeroCounting radius jensenDefect →
      (xi_selfinversive_jensen_criterion_unitCirclePure radius ↔
          xi_selfinversive_jensen_criterion_diskZeroFree radius) ∧
        (xi_selfinversive_jensen_criterion_diskZeroFree radius ↔
          xi_selfinversive_jensen_criterion_jensenVanishes jensenDefect) ∧
        (xi_selfinversive_jensen_criterion_unitCirclePure radius ↔
          xi_selfinversive_jensen_criterion_jensenVanishes jensenDefect)

lemma xi_selfinversive_jensen_criterion_unit_iff_diskZeroFree
    {n : ℕ} (radius : Fin n → ℝ)
    (hpair : xi_selfreciprocal_escape_jensen_rootPairing radius) :
    xi_selfinversive_jensen_criterion_unitCirclePure radius ↔
      xi_selfinversive_jensen_criterion_diskZeroFree radius := by
  constructor
  · intro hpure j hj
    rw [hpure j] at hj
    norm_num at hj
  · intro hdisk j
    have hge : (1 : ℝ) ≤ radius j := le_of_not_gt (hdisk j)
    have hnotgt : ¬ (1 : ℝ) < radius j := by
      intro hgt
      rcases hpair j with ⟨i, hi⟩
      have hinv_lt : (radius j)⁻¹ < (1 : ℝ) := by
        exact inv_lt_one_of_one_lt₀ hgt
      exact hdisk i (by simpa [hi] using hinv_lt)
    exact le_antisymm (le_of_not_gt hnotgt) hge

lemma xi_selfinversive_jensen_criterion_diskZeroFree_iff_jensenVanishes
    {n : ℕ} (radius : Fin n → ℝ) (jensenDefect : ℝ → ℝ)
    (hpositive : ∀ j : Fin n, 0 < radius j)
    (hjensen :
      xi_selfinversive_jensen_criterion_jensenZeroCounting radius jensenDefect) :
    xi_selfinversive_jensen_criterion_diskZeroFree radius ↔
      xi_selfinversive_jensen_criterion_jensenVanishes jensenDefect := by
  constructor
  · intro hdisk ρ hρ hρlt
    exact (hjensen ρ hρ hρlt).2 (fun j hlt => hdisk j (lt_trans hlt hρlt))
  · intro hvanish j hj
    have hmid : ((radius j + 1) / 2) < 1 := by linarith
    have hpos_mid : 0 < (radius j + 1) / 2 := by
      nlinarith [hpositive j]
    have hzero := hvanish ((radius j + 1) / 2) hpos_mid hmid
    have hno := (hjensen ((radius j + 1) / 2) hpos_mid hmid).1 hzero
    have hltmid : radius j < (radius j + 1) / 2 := by linarith
    exact hno j hltmid

/-- Paper label: `thm:xi-selfinversive-jensen-criterion`. -/
theorem paper_xi_selfinversive_jensen_criterion :
    xi_selfinversive_jensen_criterion_statement := by
  intro n radius jensenDefect hpositive hpair hjensen
  have hunit_disk :=
    xi_selfinversive_jensen_criterion_unit_iff_diskZeroFree radius hpair
  have hdisk_jensen :=
    xi_selfinversive_jensen_criterion_diskZeroFree_iff_jensenVanishes radius
      jensenDefect hpositive hjensen
  exact ⟨hunit_disk, hdisk_jensen, hunit_disk.trans hdisk_jensen⟩

end Omega.Zeta
