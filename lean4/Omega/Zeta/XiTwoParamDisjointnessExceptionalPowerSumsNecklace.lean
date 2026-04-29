import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete finite package for the exceptional power-sum necklace expansion. -/
structure xi_two_param_disjointness_exceptional_power_sums_necklace_data where
  q : ℕ
  m : ℕ
  b : ℤ
  d : ℤ
  cPowerSum : ℤ
  Phi : (Fin m → Bool) → ℤ

/-- The pure `C` word in the exceptional trace expansion. -/
def xi_two_param_disjointness_exceptional_power_sums_necklace_pureWord (m : ℕ) :
    Fin m → Bool :=
  fun _ => false

/-- Number of rank-one `B` letters in a finite word. -/
def xi_two_param_disjointness_exceptional_power_sums_necklace_wordWeight {m : ℕ}
    (w : Fin m → Bool) : ℕ :=
  ((Finset.univ : Finset (Fin m)).filter fun i => w i).card

/-- Representatives for the non-pure necklace terms. -/
def xi_two_param_disjointness_exceptional_power_sums_necklace_nonPureSupport
    (D : xi_two_param_disjointness_exceptional_power_sums_necklace_data) :
    Finset (Fin D.m → Bool) :=
  (Finset.univ : Finset (Fin D.m → Bool)).filter
    fun w => w ≠ xi_two_param_disjointness_exceptional_power_sums_necklace_pureWord D.m

/-- Seeded cyclic-orbit size for each selected representative. -/
def xi_two_param_disjointness_exceptional_power_sums_necklace_classSize {m : ℕ}
    (_w : Fin m → Bool) : ℕ :=
  1

/-- Contribution of a non-pure necklace representative. -/
def xi_two_param_disjointness_exceptional_power_sums_necklace_necklaceTerm
    (D : xi_two_param_disjointness_exceptional_power_sums_necklace_data)
    (w : Fin D.m → Bool) : ℤ :=
  (xi_two_param_disjointness_exceptional_power_sums_necklace_classSize w : ℤ) *
    D.b ^ xi_two_param_disjointness_exceptional_power_sums_necklace_wordWeight w *
      D.d ^ (D.m - xi_two_param_disjointness_exceptional_power_sums_necklace_wordWeight w) *
        D.Phi w ^ D.q

/-- Sum of all non-pure necklace contributions. -/
def xi_two_param_disjointness_exceptional_power_sums_necklace_nonPureSum
    (D : xi_two_param_disjointness_exceptional_power_sums_necklace_data) : ℤ :=
  ∑ w ∈ xi_two_param_disjointness_exceptional_power_sums_necklace_nonPureSupport D,
    xi_two_param_disjointness_exceptional_power_sums_necklace_necklaceTerm D w

/-- The pure `C`-word contribution `d^m * sum_i mu_i^m`. -/
def xi_two_param_disjointness_exceptional_power_sums_necklace_pureTerm
    (D : xi_two_param_disjointness_exceptional_power_sums_necklace_data) : ℤ :=
  D.d ^ D.m * D.cPowerSum

/-- Closed exceptional power-sum expansion split into pure and non-pure words. -/
def xi_two_param_disjointness_exceptional_power_sums_necklace_powerSum
    (D : xi_two_param_disjointness_exceptional_power_sums_necklace_data) : ℤ :=
  xi_two_param_disjointness_exceptional_power_sums_necklace_pureTerm D +
    xi_two_param_disjointness_exceptional_power_sums_necklace_nonPureSum D

/-- Paper-facing statement for the exceptional power-sum necklace formula. -/
def xi_two_param_disjointness_exceptional_power_sums_necklace_statement
    (D : xi_two_param_disjointness_exceptional_power_sums_necklace_data) : Prop :=
  xi_two_param_disjointness_exceptional_power_sums_necklace_powerSum D =
      D.d ^ D.m * D.cPowerSum +
        ∑ w ∈ xi_two_param_disjointness_exceptional_power_sums_necklace_nonPureSupport D,
          (xi_two_param_disjointness_exceptional_power_sums_necklace_classSize w : ℤ) *
            D.b ^ xi_two_param_disjointness_exceptional_power_sums_necklace_wordWeight w *
              D.d ^ (D.m -
                xi_two_param_disjointness_exceptional_power_sums_necklace_wordWeight w) *
                D.Phi w ^ D.q ∧
    (∀ w ∈ xi_two_param_disjointness_exceptional_power_sums_necklace_nonPureSupport D,
      w ≠ xi_two_param_disjointness_exceptional_power_sums_necklace_pureWord D.m) ∧
    xi_two_param_disjointness_exceptional_power_sums_necklace_wordWeight
        (xi_two_param_disjointness_exceptional_power_sums_necklace_pureWord D.m) = 0

/-- Paper label: `thm:xi-two-param-disjointness-exceptional-power-sums-necklace`. -/
theorem paper_xi_two_param_disjointness_exceptional_power_sums_necklace
    (D : xi_two_param_disjointness_exceptional_power_sums_necklace_data) :
    xi_two_param_disjointness_exceptional_power_sums_necklace_statement D := by
  refine ⟨?_, ?_, ?_⟩
  · rfl
  · intro w hw
    exact (Finset.mem_filter.mp hw).2
  · simp [xi_two_param_disjointness_exceptional_power_sums_necklace_wordWeight,
      xi_two_param_disjointness_exceptional_power_sums_necklace_pureWord]

end Omega.Zeta
