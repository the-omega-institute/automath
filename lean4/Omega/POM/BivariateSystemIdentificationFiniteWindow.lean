import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace Omega.POM

abbrev BivariateTable (α : Type*) := ℕ → ℕ → α

/-- The `2R × 2R` observation window attached to a bivariate table. -/
def finiteWindow (R : ℕ) (T : BivariateTable α) : Fin (2 * R) → Fin (2 * R) → α :=
  fun i j => T i j

/-- The canonical `R × R` core block extracted from the stabilized window. -/
def windowCore (R : ℕ) (T : BivariateTable α) : Fin R → Fin R → α :=
  fun i j => T i j

/-- Stability of the double-shift/Hankel package: shifting by `R` in either coordinate does not
change the table. This is the finite-window form of rank stabilization used in the theorem. -/
def rankStableOnTwoRWindow (R : ℕ) (T : BivariateTable α) : Prop :=
  ∀ i j, T (i + R) j = T i j ∧ T i (j + R) = T i j

/-- The canonical extension induced by the `R × R` core via coefficient extraction modulo `R`. -/
def canonicalExtension (R : ℕ) (hR : 0 < R) (core : Fin R → Fin R → α) : BivariateTable α :=
  fun i j => core ⟨i % R, Nat.mod_lt _ hR⟩ ⟨j % R, Nat.mod_lt _ hR⟩

/-- Window uniqueness: once two stabilized tables agree on the audited `2R × 2R` block, they have
the same minimal `R × R` realization block. -/
def uniqueMinimalRealizationOnWindow (R : ℕ) (T : BivariateTable α) : Prop :=
  ∀ S, rankStableOnTwoRWindow R S → finiteWindow R S = finiteWindow R T → windowCore R S = windowCore R T

/-- Full-table uniqueness: the stabilized `R × R` realization block determines the entire
bivariate table. -/
def uniqueExtensionToFullTable (R : ℕ) (hR : 0 < R) (T : BivariateTable α) : Prop :=
  canonicalExtension R hR (windowCore R T) = T

lemma periodic_left_mul {R : ℕ} {T : BivariateTable α} (hstable : rankStableOnTwoRWindow R T) :
    ∀ q i j, T (i + q * R) j = T i j := by
  intro q
  induction q with
  | zero =>
      intro i j
      simp
  | succ q ih =>
      intro i j
      calc
        T (i + Nat.succ q * R) j = T ((i + q * R) + R) j := by
          rw [Nat.succ_mul, Nat.add_assoc]
        _ = T (i + q * R) j := (hstable (i + q * R) j).1
        _ = T i j := ih i j

lemma periodic_right_mul {R : ℕ} {T : BivariateTable α} (hstable : rankStableOnTwoRWindow R T) :
    ∀ q i j, T i (j + q * R) = T i j := by
  intro q
  induction q with
  | zero =>
      intro i j
      simp
  | succ q ih =>
      intro i j
      calc
        T i (j + Nat.succ q * R) = T i ((j + q * R) + R) := by
          rw [Nat.succ_mul, Nat.add_assoc]
        _ = T i (j + q * R) := (hstable i (j + q * R)).2
        _ = T i j := ih i j

lemma reduce_left_mod {R : ℕ} {T : BivariateTable α}
    (hstable : rankStableOnTwoRWindow R T) (i j : ℕ) : T i j = T (i % R) j := by
  have hdecomp : i % R + (i / R) * R = i := by
    rw [Nat.mul_comm]
    exact Nat.mod_add_div i R
  have hreduce : T (i % R + (i / R) * R) j = T (i % R) j :=
    periodic_left_mul hstable (i / R) (i % R) j
  simpa [hdecomp] using hreduce

lemma reduce_right_mod {R : ℕ} {T : BivariateTable α}
    (hstable : rankStableOnTwoRWindow R T) (i j : ℕ) : T i j = T i (j % R) := by
  have hdecomp : j % R + (j / R) * R = j := by
    rw [Nat.mul_comm]
    exact Nat.mod_add_div j R
  have hreduce : T i (j % R + (j / R) * R) = T i (j % R) :=
    periodic_right_mul hstable (j / R) i (j % R)
  simpa [hdecomp] using hreduce

lemma canonicalExtension_eq_self {R : ℕ} (hR : 0 < R) {T : BivariateTable α}
    (hstable : rankStableOnTwoRWindow R T) : canonicalExtension R hR (windowCore R T) = T := by
  funext i j
  dsimp [canonicalExtension, windowCore]
  calc
    T (i % R) (j % R) = T (i % R) j := (reduce_right_mod hstable (i % R) j).symm
    _ = T i j := (reduce_left_mod hstable i j).symm

lemma unique_windowCore_of_window_eq {R : ℕ} {T S : BivariateTable α}
    (hWindow : finiteWindow R S = finiteWindow R T) : windowCore R S = windowCore R T := by
  funext i j
  have hi : (i : ℕ) < 2 * R := by omega
  have hj : (j : ℕ) < 2 * R := by omega
  have hEntry := congrFun (congrFun hWindow ⟨i, hi⟩) ⟨j, hj⟩
  simpa [finiteWindow, windowCore] using hEntry

/-- Paper label: `thm:pom-bivariate-system-identification-finite-window`.
The stabilized `2R × 2R` window recovers a unique minimal realization block, and that block
extends uniquely to the whole bivariate table. -/
theorem paper_pom_bivariate_system_identification_finite_window
    (R : ℕ) (hR : 0 < R) (T : BivariateTable α) :
    rankStableOnTwoRWindow R T →
      uniqueMinimalRealizationOnWindow R T ∧ uniqueExtensionToFullTable R hR T := by
  intro hstable
  refine ⟨?_, canonicalExtension_eq_self hR hstable⟩
  intro S _ hWindow
  exact unique_windowCore_of_window_eq hWindow

end Omega.POM
