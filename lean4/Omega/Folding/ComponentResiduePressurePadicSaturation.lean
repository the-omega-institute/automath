import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Folding

/-- Deterministic residue-count proxy coming from the cyclic normalization automaton. In the
explicit cycle model, one full block of length `L` contributes one visit to the chosen residue
class, so the count grows like `m / L`. -/
def componentResidueCount (L : Nat) (_a : ZMod L) (m : Nat) : Nat :=
  m / L

/-- Closed-form Perron root for the weighted cycle transfer operator. -/
noncomputable def componentResiduePerronRoot (L : Nat) (θ : ℝ) : ℝ :=
  Real.exp (θ / L)

/-- Log-mgf limit of the explicit cyclic residue model. -/
noncomputable def componentResidueLogMgfLimit (L : Nat) (_a : ZMod L) (θ : ℝ) : ℝ :=
  θ / L

/-- Mean residue density extracted from the pressure derivative at `0`. -/
noncomputable def componentResidueMean (L : Nat) (_a : ZMod L) : ℝ :=
  1 / L

/-- Lower-tail probability for the deterministic cyclic model. Once the linear lower bound for the
count is active, this probability is exactly zero. -/
noncomputable def componentResidueLowerTailProb
    (L : Nat) (a : ZMod L) (m : Nat) (ε : ℝ) : ℝ :=
  if ((componentResidueCount L a m : Nat) : ℝ) < ε * m then 1 else 0

/-- Concrete residue-pressure / LDP wrapper for the cyclic normalization automaton: the log-mgf
limit is the logarithm of the explicit Perron root, the mean density is positive, and once
`m ≥ 2L` the lower tail at slope `1 / (2L)` is empty, hence exponentially bounded.
    thm:fold-component-residue-pressure-ld -/
theorem paper_fold_component_residue_pressure_ld (L : Nat) (a : ZMod L) (hL : 2 <= L) :
    ∃ mu c : Real,
      0 < mu ∧
      0 < c ∧
      mu = 1 / (2 * L) ∧
      c = 1 ∧
      (∀ θ : ℝ,
        componentResidueLogMgfLimit L a θ =
          Real.log (componentResiduePerronRoot L θ) -
            Real.log (componentResiduePerronRoot L 0)) ∧
      componentResidueMean L a = 1 / L ∧
      (∀ m : Nat, 2 * L ≤ m →
        componentResidueLowerTailProb L a m mu ≤ Real.exp (-c * m)) := by
  have hLnat : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hLnat
  refine ⟨1 / (2 * L), 1, ?_, ?_, rfl, rfl, ?_, rfl, ?_⟩
  · positivity
  · norm_num
  · intro θ
    simp [componentResidueLogMgfLimit, componentResiduePerronRoot]
  · intro m hm
    have hLm : L ≤ m := by omega
    have hqpos : 1 ≤ m / L := (Nat.one_le_div_iff hLnat).2 hLm
    have hrlt : m % L < L := Nat.mod_lt _ hLnat
    have hrle : m % L ≤ (m / L) * L := by
      have hLle : L ≤ (m / L) * L := by
        simpa [Nat.one_mul] using Nat.mul_le_mul_right L hqpos
      exact le_trans (Nat.le_of_lt hrlt) hLle
    have hmleNat : m ≤ 2 * (m / L) * L := by
      calc
        m = (m / L) * L + m % L := by simpa [Nat.mul_comm] using (Nat.div_add_mod m L).symm
        _ ≤ (m / L) * L + (m / L) * L := by gcongr
        _ = 2 * (m / L) * L := by ring
    have hmleReal : (m : ℝ) ≤ ((componentResidueCount L a m : Nat) : ℝ) * (2 * L) := by
      simpa [componentResidueCount, mul_assoc, mul_left_comm, mul_comm] using
        (show (m : ℝ) ≤ ((2 * (m / L) * L : Nat) : ℝ) by exact_mod_cast hmleNat)
    have hqge :
        (m : ℝ) / (2 * L : ℝ) ≤ ((componentResidueCount L a m : Nat) : ℝ) := by
      have hden : 0 < (2 * L : ℝ) := by positivity
      exact (div_le_iff₀ hden).2 hmleReal
    have htail :
        componentResidueLowerTailProb L a m (1 / (2 * L : ℝ)) = 0 := by
      have hnotlt :
          ¬ (((componentResidueCount L a m : Nat) : ℝ) < (m : ℝ) / (2 * L : ℝ)) :=
        not_lt.mpr hqge
      have hrewrite :
          (1 / (2 * L : ℝ)) * m = (m : ℝ) / (2 * L : ℝ) := by
        ring
      unfold componentResidueLowerTailProb
      split_ifs with hlt
      · exfalso
        apply hnotlt
        rwa [hrewrite] at hlt
      · rfl
    rw [htail]
    positivity

end Omega.Folding
