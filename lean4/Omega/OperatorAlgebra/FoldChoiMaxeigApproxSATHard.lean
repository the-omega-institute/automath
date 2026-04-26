import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic
import Omega.OperatorAlgebra.CircuitNoninjectiveNPComplete

namespace Omega.OperatorAlgebra

/-- The satisfying witness count `s = #SAT(φ)`. -/
def satWitnessCount {n : ℕ} (φ : BitVec n → Bool) : ℕ :=
  Fintype.card {w : BitVec n // φ w = true}

/-- The ambient size `N = 2^(n+1)` of the two-fiber SAT fold. -/
def satFoldAmbientSize (n : ℕ) : ℕ :=
  2 ^ (n + 1)

/-- The normalized Choi-state maximal eigenvalue in the two-fiber scalar model. -/
noncomputable def satFoldNormalizedChoiMaxEig {n : ℕ} (φ : BitVec n → Bool) : ℚ :=
  let N := satFoldAmbientSize n
  let s := satWitnessCount φ
  if hs : s = 0 then 1 / (N : ℚ)^2 else 1 / ((N : ℚ) * Nat.min s (N - s))

private theorem satWitnessCount_eq_zero_iff {n : ℕ} (φ : BitVec n → Bool) :
    satWitnessCount φ = 0 ↔ ¬ satisfiable φ := by
  constructor
  · intro hs hsat
    rcases hsat with ⟨w, hw⟩
    have hpos : 0 < satWitnessCount φ := by
      unfold satWitnessCount
      exact Fintype.card_pos_iff.mpr ⟨⟨w, hw⟩⟩
    omega
  · intro hns
    unfold satWitnessCount
    letI : IsEmpty {w : BitVec n // φ w = true} := by
      refine ⟨?_⟩
      intro x
      exact hns ⟨x.1, x.2⟩
    simpa using Fintype.card_of_isEmpty {w : BitVec n // φ w = true}

private theorem satWitnessCount_le_halfAmbient {n : ℕ} (φ : BitVec n → Bool) :
    satWitnessCount φ ≤ satFoldAmbientSize n / 2 := by
  have hcard : satWitnessCount φ ≤ Fintype.card (BitVec n) := by
    unfold satWitnessCount
    exact Fintype.card_subtype_le (fun w : BitVec n => φ w = true)
  have hbit : Fintype.card (BitVec n) = 2 ^ n := by
    simp [BitVec]
  have hhalf : satFoldAmbientSize n / 2 = 2 ^ n := by
    unfold satFoldAmbientSize
    rw [Nat.pow_succ', Nat.mul_comm, Nat.mul_div_left _ (by decide : 0 < 2)]
  rw [hhalf]
  exact hcard.trans_eq hbit

private theorem sat_case_threshold {n : ℕ} {φ : BitVec n → Bool} (hs : satWitnessCount φ ≠ 0) :
    2 / (satFoldAmbientSize n : ℚ)^2 ≤
      1 / ((satFoldAmbientSize n : ℚ) *
        Nat.min (satWitnessCount φ) (satFoldAmbientSize n - satWitnessCount φ)) := by
  have hspos : 0 < satWitnessCount φ := Nat.pos_iff_ne_zero.mpr hs
  have hsle : satWitnessCount φ ≤ satFoldAmbientSize n / 2 := satWitnessCount_le_halfAmbient φ
  have hmin :
      Nat.min (satWitnessCount φ) (satFoldAmbientSize n - satWitnessCount φ) = satWitnessCount φ := by
    apply Nat.min_eq_left
    omega
  rw [hmin]
  have hNne : (satFoldAmbientSize n : ℚ) ≠ 0 := by
    exact_mod_cast (show satFoldAmbientSize n ≠ 0 by
      unfold satFoldAmbientSize
      exact pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0))
  have hsne : (satWitnessCount φ : ℚ) ≠ 0 := by
    exact_mod_cast hs
  field_simp [hNne, hsne]
  exact_mod_cast (show 2 * satWitnessCount φ ≤ satFoldAmbientSize n by omega)

/-- Paper label: `thm:fold-choi-maxeig-approx-sat-hard`. -/
theorem paper_fold_choi_maxeig_approx_sat_hard
    (n : ℕ) (φ : BitVec n → Bool) :
    let N := satFoldAmbientSize n
    let s := satWitnessCount φ
    let lam := satFoldNormalizedChoiMaxEig φ
    ((¬ satisfiable φ) → lam = 1 / (N : ℚ)^2) ∧
      (satisfiable φ → lam = 1 / ((N : ℚ) * Nat.min s (N - s))) := by
  let N := satFoldAmbientSize n
  let s := satWitnessCount φ
  let lam := satFoldNormalizedChoiMaxEig φ
  have hs0 : s = 0 ↔ ¬ satisfiable φ := satWitnessCount_eq_zero_iff φ
  refine ⟨?_, ?_⟩
  · intro hunsat
    have hs : s = 0 := hs0.mpr hunsat
    simp [lam, satFoldNormalizedChoiMaxEig, N, s, hs]
  · intro hsat
    have hs : s ≠ 0 := by
      intro hs
      exact (hs0.mp hs) hsat
    simp [lam, satFoldNormalizedChoiMaxEig, N, s, hs]

end Omega.OperatorAlgebra
