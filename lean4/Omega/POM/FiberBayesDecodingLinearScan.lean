import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- A natural-number indexed subset of a path is independent when it contains no consecutive
vertices. -/
def natPathIndependent (A : Finset Nat) : Prop :=
  ∀ i ∈ A, i + 1 ∉ A

/-- Dynamic-programming value for the first `k` vertices of a length-`ℓ` path. -/
def pathScanValue (ℓ : Nat) (w : Fin ℓ → ℝ) : Nat → ℝ
  | 0 => 0
  | 1 => if h : 0 < ℓ then max 0 (w ⟨0, h⟩) else 0
  | k + 2 =>
      if hk : k + 1 < ℓ then
        max (pathScanValue ℓ w (k + 1)) (pathScanValue ℓ w k + w ⟨k + 1, hk⟩)
      else
        pathScanValue ℓ w (k + 1)

/-- Standard left-to-right backtracking choice corresponding to `pathScanValue`. -/
noncomputable def pathScanChoice (ℓ : Nat) (w : Fin ℓ → ℝ) : Nat → Finset Nat
  | 0 => ∅
  | 1 =>
      if h : 0 < ℓ then
        if 0 ≤ w ⟨0, h⟩ then {0} else ∅
      else
        ∅
  | k + 2 =>
      if hk : k + 1 < ℓ then
        if pathScanValue ℓ w (k + 1) ≥ pathScanValue ℓ w k + w ⟨k + 1, hk⟩ then
          pathScanChoice ℓ w (k + 1)
        else
          insert (k + 1) (pathScanChoice ℓ w k)
      else
        pathScanChoice ℓ w (k + 1)

lemma pathScanChoice_subset_range (ℓ : Nat) (w : Fin ℓ → ℝ) :
    ∀ k, k ≤ ℓ → pathScanChoice ℓ w k ⊆ Finset.range k
  | 0, _ => by simp [pathScanChoice]
  | 1, _ => by
      by_cases hℓ : 0 < ℓ
      · by_cases hw : 0 ≤ w ⟨0, hℓ⟩
        · simp [pathScanChoice, hℓ, hw]
        · simp [pathScanChoice, hℓ, hw]
      · simp [pathScanChoice, hℓ]
  | k + 2, hk => by
      have hk' : k + 1 ≤ ℓ := by omega
      by_cases hstep : k + 1 < ℓ
      · by_cases hchoose :
          pathScanValue ℓ w (k + 1) ≥ pathScanValue ℓ w k + w ⟨k + 1, hstep⟩
        · intro i hi
          have hi' : i ∈ pathScanChoice ℓ w (k + 1) := by
            simpa [pathScanChoice, hstep, hchoose] using hi
          have hsubset := pathScanChoice_subset_range ℓ w (k + 1) hk' hi'
          have hik : i < k + 1 := by simpa [Finset.mem_range] using hsubset
          simpa [Finset.mem_range] using (show i < k + 2 by omega)
        · intro i hi
          have hchoice :
              pathScanChoice ℓ w (k + 2) = insert (k + 1) (pathScanChoice ℓ w k) := by
            simp [pathScanChoice, hstep, hchoose]
          have hi' : i = k + 1 ∨ i ∈ pathScanChoice ℓ w k := by
            rw [hchoice] at hi
            exact Finset.mem_insert.mp hi
          rcases hi' with rfl | hi'
          · simpa [Finset.mem_range]
          · have hsubset := pathScanChoice_subset_range ℓ w k (by omega) hi'
            have hik : i < k := by simpa [Finset.mem_range] using hsubset
            simpa [Finset.mem_range] using (show i < k + 2 by omega)
      · intro i hi
        have hi' : i ∈ pathScanChoice ℓ w (k + 1) := by
          simpa [pathScanChoice, hstep] using hi
        have hsubset := pathScanChoice_subset_range ℓ w (k + 1) hk' hi'
        have hik : i < k + 1 := by simpa [Finset.mem_range] using hsubset
        simpa [Finset.mem_range] using (show i < k + 2 by omega)

lemma pathScanChoice_independent (ℓ : Nat) (w : Fin ℓ → ℝ) :
    ∀ k, k ≤ ℓ → natPathIndependent (pathScanChoice ℓ w k)
  | 0, _ => by simp [natPathIndependent, pathScanChoice]
  | 1, _ => by
      by_cases hℓ : 0 < ℓ
      · by_cases hw : 0 ≤ w ⟨0, hℓ⟩
        · simp [natPathIndependent, pathScanChoice, hℓ, hw]
        · simp [natPathIndependent, pathScanChoice, hℓ, hw]
      · simp [natPathIndependent, pathScanChoice, hℓ]
  | k + 2, hk => by
      have hk' : k + 1 ≤ ℓ := by omega
      by_cases hstep : k + 1 < ℓ
      · by_cases hchoose :
          pathScanValue ℓ w (k + 1) ≥ pathScanValue ℓ w k + w ⟨k + 1, hstep⟩
        · simpa [pathScanChoice, hstep, hchoose] using
            pathScanChoice_independent ℓ w (k + 1) hk'
        · have hind : natPathIndependent (pathScanChoice ℓ w k) :=
            pathScanChoice_independent ℓ w k (by omega)
          have hsubset : pathScanChoice ℓ w k ⊆ Finset.range k :=
            pathScanChoice_subset_range ℓ w k (by omega)
          intro i hi
          have hchoice :
              pathScanChoice ℓ w (k + 2) = insert (k + 1) (pathScanChoice ℓ w k) := by
            simp [pathScanChoice, hstep, hchoose]
          rw [hchoice] at hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · intro hmem
            rw [hchoice] at hmem
            have hmem' : k + 2 ∈ pathScanChoice ℓ w k := by
              simpa using hmem
            have hkmem := hsubset hmem'
            have : k + 2 < k := by
              simpa [Finset.mem_range] using hkmem
            omega
          · intro hmem
            rw [hchoice] at hmem
            rcases Finset.mem_insert.mp hmem with hEq | hmem
            · have hik : i < k := by
                simpa [Finset.mem_range] using hsubset hi
              omega
            · exact hind i hi hmem
      · simpa [pathScanChoice, hstep] using pathScanChoice_independent ℓ w (k + 1) hk'

/-- On a path component, the linear scan satisfies the standard recurrence and its backtracking
choice produces an independent subset of the first `ℓ` vertices.
    cor:pom-fiber-bayes-decoding-linear-scan -/
theorem paper_pom_fiber_bayes_decoding_linear_scan (ℓ : Nat) (w : Fin ℓ → ℝ) :
    pathScanValue ℓ w 0 = 0 ∧
      (∀ hℓ : 0 < ℓ, pathScanValue ℓ w 1 = max 0 (w ⟨0, hℓ⟩)) ∧
      (∀ k (hk : k + 2 ≤ ℓ),
        pathScanValue ℓ w (k + 2) =
          max (pathScanValue ℓ w (k + 1)) (pathScanValue ℓ w k + w ⟨k + 1, by omega⟩)) ∧
      natPathIndependent (pathScanChoice ℓ w ℓ) ∧
      pathScanChoice ℓ w ℓ ⊆ Finset.range ℓ := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · intro hℓ
    simp [pathScanValue, hℓ]
  · intro k hk
    have hstep : k + 1 < ℓ := by omega
    simp [pathScanValue, hstep]
  · exact pathScanChoice_independent ℓ w ℓ le_rfl
  · exact pathScanChoice_subset_range ℓ w ℓ le_rfl

end Omega.POM
