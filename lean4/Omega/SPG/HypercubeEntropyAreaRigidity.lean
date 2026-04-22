import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.SPG.AxialCoareaInequality

namespace Omega.SPG

/-- Base-`2` entropy proxy for a finite hypercube section of size `N`. -/
noncomputable def hypercubeEntropyBase2 (N : ℕ) : ℝ :=
  Real.log (N + 1) / Real.log 2

/-- The same entropy proxy in natural-log units. -/
noncomputable def hypercubeEntropyShannon (N : ℕ) : ℝ :=
  Real.log (N + 1)

/-- Paper label: `prop:hypercube-entropy-area-rigidity`.

The axial coarea lower bound turns the total boundary budget into a cardinality bound. Taking
logarithms yields the base-`2` entropy bound, multiplying by `log 2` recovers the Shannon
normalization, zero boundary forces concentration on the empty fiber, and equality saturates the
entropy bound. -/
theorem paper_hypercube_entropy_area_rigidity (N F L : ℕ) (hcoarea : 2 * N ≤ L * F) :
    N ≤ L * F / 2 ∧
      hypercubeEntropyShannon N = Real.log 2 * hypercubeEntropyBase2 N ∧
      hypercubeEntropyBase2 N ≤ hypercubeEntropyBase2 (L * F / 2) ∧
      (F = 0 → N = 0 ∧ hypercubeEntropyShannon N = 0) ∧
      (N = L * F / 2 → hypercubeEntropyBase2 N = hypercubeEntropyBase2 (L * F / 2)) := by
  have hvol : N ≤ L * F / 2 := fiber_volume_face_bound N F L hcoarea
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hconvert : hypercubeEntropyShannon N = Real.log 2 * hypercubeEntropyBase2 N := by
    unfold hypercubeEntropyShannon hypercubeEntropyBase2
    field_simp [hlog2_pos.ne']
  have hmonolog : Real.log ((N + 1 : ℕ) : ℝ) ≤ Real.log ((L * F / 2 + 1 : ℕ) : ℝ) := by
    have hnat : N + 1 ≤ L * F / 2 + 1 := Nat.succ_le_succ hvol
    have hreal : ((N + 1 : ℕ) : ℝ) ≤ ((L * F / 2 + 1 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    exact Real.log_le_log (by positivity) hreal
  have hmono : hypercubeEntropyBase2 N ≤ hypercubeEntropyBase2 (L * F / 2) := by
    unfold hypercubeEntropyBase2
    have hmonolog' : Real.log (↑N + 1) ≤ Real.log (↑(L * F / 2) + 1) := by
      simpa [Nat.cast_add] using hmonolog
    exact div_le_div_of_nonneg_right hmonolog' hlog2_pos.le
  refine ⟨hvol, hconvert, hmono, ?_, ?_⟩
  · intro hF
    have hN : N = 0 := by
      have : 2 * N ≤ 0 := by simpa [hF] using hcoarea
      omega
    refine ⟨hN, ?_⟩
    simp [hypercubeEntropyShannon, hN]
  · intro hsat
    simp [hypercubeEntropyBase2, hsat]

end Omega.SPG
