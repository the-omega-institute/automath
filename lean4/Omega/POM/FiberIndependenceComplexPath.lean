import Mathlib.Tactic

namespace Omega.POM

/-- A concrete homotopy-type model for the independence complex of a path. -/
inductive pom_independence_complex_path_homotopyType
  | contractible
  | sphere (dimension : Int)
  deriving DecidableEq, Repr

/-- Suspension bookkeeping for the path recursion: contractible stays contractible, while a sphere
gains one dimension. -/
def pom_independence_complex_path_suspend :
    pom_independence_complex_path_homotopyType →
      pom_independence_complex_path_homotopyType
  | .contractible => .contractible
  | .sphere d => .sphere (d + 1)

/-- The three-step recursion for path independence complexes, with the audited base cases
`ℓ = 0, 1, 2`. -/
def pom_independence_complex_path_model : ℕ → pom_independence_complex_path_homotopyType
  | 0 => .sphere (-1)
  | 1 => .contractible
  | 2 => .sphere 0
  | n + 3 => pom_independence_complex_path_suspend (pom_independence_complex_path_model n)

@[simp] theorem pom_independence_complex_path_model_zero :
    pom_independence_complex_path_model 0 = .sphere (-1) := rfl

@[simp] theorem pom_independence_complex_path_model_one :
    pom_independence_complex_path_model 1 = .contractible := rfl

@[simp] theorem pom_independence_complex_path_model_two :
    pom_independence_complex_path_model 2 = .sphere 0 := rfl

@[simp] theorem pom_independence_complex_path_model_step (n : ℕ) :
    pom_independence_complex_path_model (n + 3) =
      pom_independence_complex_path_suspend (pom_independence_complex_path_model n) := rfl

private theorem pom_independence_complex_path_three_mul (k : ℕ) :
    pom_independence_complex_path_model (3 * k) = .sphere (Int.ofNat k - 1) := by
  induction k with
  | zero =>
      simp [pom_independence_complex_path_model]
  | succ k ih =>
      have hk : 3 * Nat.succ k = 3 * k + 3 := by omega
      rw [hk, pom_independence_complex_path_model_step]
      simpa [pom_independence_complex_path_suspend, ih]

private theorem pom_independence_complex_path_three_mul_add_one (k : ℕ) :
    pom_independence_complex_path_model (3 * k + 1) = .contractible := by
  induction k with
  | zero =>
      simp [pom_independence_complex_path_model]
  | succ k ih =>
      have hk : 3 * Nat.succ k + 1 = (3 * k + 1) + 3 := by omega
      rw [hk, pom_independence_complex_path_model_step]
      simpa [pom_independence_complex_path_suspend, ih]

private theorem pom_independence_complex_path_three_mul_add_two (k : ℕ) :
    pom_independence_complex_path_model (3 * k + 2) = .sphere (Int.ofNat k) := by
  induction k with
  | zero =>
      simp [pom_independence_complex_path_model]
  | succ k ih =>
      have hk : 3 * Nat.succ k + 2 = (3 * k + 2) + 3 := by omega
      rw [hk, pom_independence_complex_path_model_step]
      simpa [pom_independence_complex_path_suspend, ih]

/-- Paper label: `lem:pom-independence-complex-path`.
The path independence complex follows the three-periodic contractible-versus-sphere
classification. -/
theorem paper_pom_independence_complex_path (ell : ℕ) :
    (ell % 3 = 1 → pom_independence_complex_path_model ell = .contractible) ∧
      (ell % 3 = 0 →
        pom_independence_complex_path_model ell = .sphere (Int.ofNat (ell / 3) - 1)) ∧
      (ell % 3 = 2 →
        pom_independence_complex_path_model ell = .sphere (Int.ofNat (ell / 3))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hmod
    have hell : ell = 3 * (ell / 3) + 1 := by
      have hdiv := Nat.mod_add_div ell 3
      omega
    rw [hell]
    exact pom_independence_complex_path_three_mul_add_one (ell / 3)
  · intro hmod
    have hell : ell = 3 * (ell / 3) := by
      have hdiv := Nat.mod_add_div ell 3
      omega
    have hdiv0 : (3 * (ell / 3)) / 3 = ell / 3 := by omega
    rw [hell]
    rw [hdiv0]
    exact pom_independence_complex_path_three_mul (ell / 3)
  · intro hmod
    have hell : ell = 3 * (ell / 3) + 2 := by
      have hdiv := Nat.mod_add_div ell 3
      omega
    have hdiv2 : (3 * (ell / 3) + 2) / 3 = ell / 3 := by omega
    rw [hell]
    rw [hdiv2]
    exact pom_independence_complex_path_three_mul_add_two (ell / 3)

end Omega.POM
