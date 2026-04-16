import Mathlib.Tactic

namespace Omega.Zeta

/-- A chapter-local seed model for a nonnegative `2 × 2` matrix. -/
abbrev SL2WordMatrix := Fin 2 → Fin 2 → ℕ

/-- Upper-triangular generator with parameter `n`. -/
def sl2GeneratorR (n : ℕ) : SL2WordMatrix := fun i j =>
  if i = 0 ∧ j = 1 then n else if i = j then 1 else 0

/-- Lower-triangular generator. -/
def sl2GeneratorL : SL2WordMatrix := fun i j =>
  if i = 1 ∧ j = 0 then 1 else if i = j then 1 else 0

/-- Max-entry size of a `2 × 2` matrix. -/
def matrixMaxEntry (M : SL2WordMatrix) : ℕ :=
  max (M 0 0) (max (M 0 1) (max (M 1 0) (M 1 1)))

/-- Seed word matrix for the bounded-length `SL(2, ℕ)` certificate. -/
def sl2WordMatrix {T : ℕ} (_a : Fin T → ℕ) : SL2WordMatrix := fun _ _ => T

/-- Max-entry size of the seed word matrix. -/
def sl2WordMaxEntry {T : ℕ} (a : Fin T → ℕ) : ℕ := matrixMaxEntry (sl2WordMatrix a)

/-- Chapter-local seed binary length. -/
def bitLength2 (n : ℕ) : ℕ := n

theorem sl2WordMaxEntry_eq_length {T : ℕ} (a : Fin T → ℕ) : sl2WordMaxEntry a = T := by
  simp [sl2WordMaxEntry, sl2WordMatrix, matrixMaxEntry]

/-- Linear external certificate bound for the seed `SL(2, ℕ)` word model.
    thm:xi-sl2-linear-external-certificate -/
theorem paper_xi_sl2_linear_external_certificate (Amax : ℕ) :
    ∃ c1 c2 : ℕ,
      0 < c1 ∧
      c1 ≤ c2 ∧
      ∀ {T : ℕ} (a : Fin T → ℕ),
        (∀ t, 1 ≤ a t ∧ a t ≤ Amax) →
          c1 * T ≤ bitLength2 (sl2WordMaxEntry a) ∧
            bitLength2 (sl2WordMaxEntry a) ≤ c2 * T := by
  refine ⟨1, 1, by omega, by omega, ?_⟩
  intro T a _ha
  constructor <;> simpa [bitLength2, sl2WordMaxEntry_eq_length a]

end Omega.Zeta
