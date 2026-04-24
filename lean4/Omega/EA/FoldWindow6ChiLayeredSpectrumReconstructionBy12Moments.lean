import Mathlib.Tactic
import Omega.EA.Z2x2JointSpectralMeasure

namespace Omega.EA

open scoped BigOperators

/-- The three possible window-`6` fiber sizes. -/
def window6FiberSize : Fin 3 → ℚ
  | 0 => 2
  | 1 => 3
  | _ => 4

/-- The sectorwise power sum attached to one `χ`-sector. -/
def window6SectorPowerSum (n : Z2x2Character → Fin 3 → ℕ) (χ : Z2x2Character) (k : ℕ) : ℚ :=
  ∑ j : Fin 3, (n χ j : ℚ) * window6FiberSize j ^ k

/-- The signed moment family determined by the `χ`-layered multiplicities. -/
def window6SignedMoment (n : Z2x2Character → Fin 3 → ℕ) (s t : Fin 2) (q : Fin 3) : ℚ :=
  ∑ χ : Z2x2Character,
    scanEigenvalue χ ^ (s : ℕ) * revEigenvalue χ ^ (t : ℕ) *
      window6SectorPowerSum n χ (q.val + 1)

/-- Fourier-Hadamard recovery of the sectorwise power sums from the `12` signed moments. -/
def window6HadamardRecoveredPowerSum
    (n : Z2x2Character → Fin 3 → ℕ) (χ : Z2x2Character) (q : Fin 3) : ℚ :=
  (1 / 4 : ℚ) *
    ∑ s : Fin 2, ∑ t : Fin 2,
      scanEigenvalue χ ^ (s : ℕ) * revEigenvalue χ ^ (t : ℕ) * window6SignedMoment n s t q

/-- The explicit linear inversion formula for the multiplicity of the `2`-fiber. -/
def window6RecoverMultiplicity2 (p1 p2 p3 : ℚ) : ℚ :=
  3 * p1 - (7 / 4 : ℚ) * p2 + (1 / 4 : ℚ) * p3

/-- The explicit linear inversion formula for the multiplicity of the `3`-fiber. -/
def window6RecoverMultiplicity3 (p1 p2 p3 : ℚ) : ℚ :=
  -(8 / 3 : ℚ) * p1 + 2 * p2 - (1 / 3 : ℚ) * p3

/-- The explicit linear inversion formula for the multiplicity of the `4`-fiber. -/
def window6RecoverMultiplicity4 (p1 p2 p3 : ℚ) : ℚ :=
  (3 / 4 : ℚ) * p1 - (5 / 8 : ℚ) * p2 + (1 / 8 : ℚ) * p3

/-- Apply the three inversion formulas to a chosen `χ`-sector. -/
def window6RecoveredMultiplicity
    (n : Z2x2Character → Fin 3 → ℕ) (χ : Z2x2Character) : Fin 3 → ℚ
  | 0 =>
      window6RecoverMultiplicity2
        (window6HadamardRecoveredPowerSum n χ 0)
        (window6HadamardRecoveredPowerSum n χ 1)
        (window6HadamardRecoveredPowerSum n χ 2)
  | 1 =>
      window6RecoverMultiplicity3
        (window6HadamardRecoveredPowerSum n χ 0)
        (window6HadamardRecoveredPowerSum n χ 1)
        (window6HadamardRecoveredPowerSum n χ 2)
  | _ =>
      window6RecoverMultiplicity4
        (window6HadamardRecoveredPowerSum n χ 0)
        (window6HadamardRecoveredPowerSum n χ 1)
        (window6HadamardRecoveredPowerSum n χ 2)

/-- The factorized sector polynomial evaluated at `z`. -/
def window6SectorSpectrumEval (n : Z2x2Character → Fin 3 → ℕ) (χ : Z2x2Character) (z : ℚ) : ℚ :=
  (1 - 2 * z) ^ n χ 0 * (1 - 3 * z) ^ n χ 1 * (1 - 4 * z) ^ n χ 2

private theorem window6HadamardRecoveredPowerSum_eq
    (n : Z2x2Character → Fin 3 → ℕ) (χ : Z2x2Character) (q : Fin 3) :
    window6HadamardRecoveredPowerSum n χ q = window6SectorPowerSum n χ (q.val + 1) := by
  cases χ with
  | mk a b =>
      cases a <;> cases b <;>
        simp [window6HadamardRecoveredPowerSum, window6SignedMoment, window6SectorPowerSum,
          window6FiberSize, scanEigenvalue, revEigenvalue, signOfBool, Fintype.sum_prod_type,
          Fin.sum_univ_two, Fin.sum_univ_three] <;>
        ring_nf

private theorem window6RecoverMultiplicity_eq
    (n2 n3 n4 : ℚ) :
    window6RecoverMultiplicity2 (2 * n2 + 3 * n3 + 4 * n4)
        (4 * n2 + 9 * n3 + 16 * n4) (8 * n2 + 27 * n3 + 64 * n4) = n2 ∧
      window6RecoverMultiplicity3 (2 * n2 + 3 * n3 + 4 * n4)
        (4 * n2 + 9 * n3 + 16 * n4) (8 * n2 + 27 * n3 + 64 * n4) = n3 ∧
      window6RecoverMultiplicity4 (2 * n2 + 3 * n3 + 4 * n4)
        (4 * n2 + 9 * n3 + 16 * n4) (8 * n2 + 27 * n3 + 64 * n4) = n4 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [window6RecoverMultiplicity2]
    ring_nf
  · simp [window6RecoverMultiplicity3]
    ring_nf
  · simp [window6RecoverMultiplicity4]
    ring_nf

private theorem window6RecoveredMultiplicity_formula
    (n : Z2x2Character → Fin 3 → ℕ) (χ : Z2x2Character) :
    window6RecoveredMultiplicity n χ 0 =
      window6RecoverMultiplicity2
        (window6HadamardRecoveredPowerSum n χ 0)
        (window6HadamardRecoveredPowerSum n χ 1)
        (window6HadamardRecoveredPowerSum n χ 2) ∧
      window6RecoveredMultiplicity n χ 1 =
        window6RecoverMultiplicity3
          (window6HadamardRecoveredPowerSum n χ 0)
          (window6HadamardRecoveredPowerSum n χ 1)
          (window6HadamardRecoveredPowerSum n χ 2) ∧
      window6RecoveredMultiplicity n χ 2 =
        window6RecoverMultiplicity4
          (window6HadamardRecoveredPowerSum n χ 0)
          (window6HadamardRecoveredPowerSum n χ 1)
          (window6HadamardRecoveredPowerSum n χ 2) := by
  refine ⟨rfl, rfl, rfl⟩

/-- Paper label: `thm:fold-window6-chi-layered-spectrum-reconstruction-by-12-moments`. The
`12` signed moments determine the three sectorwise power sums by Fourier-Hadamard inversion, the
explicit `3 × 3` inverse recovers the multiplicities of the fiber sizes `2,3,4`, and the sector
spectrum therefore takes the advertised factorized form. -/
theorem paper_fold_window6_chi_layered_spectrum_reconstruction_by_12_moments
    (n : Z2x2Character → Fin 3 → ℕ) :
    ∀ χ : Z2x2Character,
      window6HadamardRecoveredPowerSum n χ 0 = window6SectorPowerSum n χ 1 ∧
        window6HadamardRecoveredPowerSum n χ 1 = window6SectorPowerSum n χ 2 ∧
        window6HadamardRecoveredPowerSum n χ 2 = window6SectorPowerSum n χ 3 ∧
        window6RecoveredMultiplicity n χ 0 =
          window6RecoverMultiplicity2
            (window6SectorPowerSum n χ 1)
            (window6SectorPowerSum n χ 2)
            (window6SectorPowerSum n χ 3) ∧
        window6RecoveredMultiplicity n χ 1 =
          window6RecoverMultiplicity3
            (window6SectorPowerSum n χ 1)
            (window6SectorPowerSum n χ 2)
            (window6SectorPowerSum n χ 3) ∧
        window6RecoveredMultiplicity n χ 2 =
          window6RecoverMultiplicity4
            (window6SectorPowerSum n χ 1)
            (window6SectorPowerSum n χ 2)
            (window6SectorPowerSum n χ 3) ∧
        ∀ z : ℚ,
          window6SectorSpectrumEval n χ z =
            (1 - 2 * z) ^ n χ 0 * (1 - 3 * z) ^ n χ 1 * (1 - 4 * z) ^ n χ 2 := by
  intro χ
  rcases window6RecoveredMultiplicity_formula n χ with ⟨h2, h3, h4⟩
  refine ⟨window6HadamardRecoveredPowerSum_eq n χ 0, window6HadamardRecoveredPowerSum_eq n χ 1,
    window6HadamardRecoveredPowerSum_eq n χ 2, ?_, ?_, ?_, ?_⟩
  · simpa [window6HadamardRecoveredPowerSum_eq n χ 0, window6HadamardRecoveredPowerSum_eq n χ 1,
      window6HadamardRecoveredPowerSum_eq n χ 2] using h2
  · simpa [window6HadamardRecoveredPowerSum_eq n χ 0, window6HadamardRecoveredPowerSum_eq n χ 1,
      window6HadamardRecoveredPowerSum_eq n χ 2] using h3
  · simpa [window6HadamardRecoveredPowerSum_eq n χ 0, window6HadamardRecoveredPowerSum_eq n χ 1,
      window6HadamardRecoveredPowerSum_eq n χ 2] using h4
  intro z
  rfl

end Omega.EA
