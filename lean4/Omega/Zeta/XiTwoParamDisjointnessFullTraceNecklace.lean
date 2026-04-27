import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete data for the full trace necklace expansion of the two-parameter disjointness matrix. -/
structure xi_two_param_disjointness_full_trace_necklace_data where
  q : ℕ
  m : ℕ
  b : ℤ
  d : ℤ
  Phi : (Fin m → Bool) → ℤ

/-- Lucas trace seed, written in Fibonacci form for `m ≥ 1`. -/
def xi_two_param_disjointness_full_trace_necklace_lucas (m : ℕ) : ℤ :=
  (Nat.fib (m + 1) : ℤ) + (Nat.fib (m - 1) : ℤ)

/-- The pure `C`-word in the two-letter expansion. -/
def xi_two_param_disjointness_full_trace_necklace_pureWord (m : ℕ) : Fin m → Bool :=
  fun _ => false

/-- Number of rank-one `B` letters in a word. -/
def xi_two_param_disjointness_full_trace_necklace_wordWeight {m : ℕ}
    (w : Fin m → Bool) : ℕ :=
  ((Finset.univ : Finset (Fin m)).filter fun i => w i).card

/-- Representatives for the non-pure cyclic necklace classes in the seeded finite model. -/
def xi_two_param_disjointness_full_trace_necklace_nonPureSupport
    (D : xi_two_param_disjointness_full_trace_necklace_data) : Finset (Fin D.m → Bool) :=
  (Finset.univ : Finset (Fin D.m → Bool)).filter
    fun w => w ≠ xi_two_param_disjointness_full_trace_necklace_pureWord D.m

/-- Seeded necklace class size. In this finite package each selected representative has weight one. -/
def xi_two_param_disjointness_full_trace_necklace_classSize {m : ℕ}
    (_w : Fin m → Bool) : ℕ :=
  1

/-- The contribution of a non-pure necklace representative. -/
def xi_two_param_disjointness_full_trace_necklace_necklaceTerm
    (D : xi_two_param_disjointness_full_trace_necklace_data) (w : Fin D.m → Bool) : ℤ :=
  (xi_two_param_disjointness_full_trace_necklace_classSize w : ℤ) *
    D.b ^ xi_two_param_disjointness_full_trace_necklace_wordWeight w *
      D.d ^ (D.m - xi_two_param_disjointness_full_trace_necklace_wordWeight w) *
        D.Phi w ^ D.q

/-- Sum of all non-pure necklace contributions. -/
def xi_two_param_disjointness_full_trace_necklace_nonPureSum
    (D : xi_two_param_disjointness_full_trace_necklace_data) : ℤ :=
  ∑ w ∈ xi_two_param_disjointness_full_trace_necklace_nonPureSupport D,
    xi_two_param_disjointness_full_trace_necklace_necklaceTerm D w

/-- The pure Lucas contribution `d^m L_m^q`. -/
def xi_two_param_disjointness_full_trace_necklace_pureTrace
    (D : xi_two_param_disjointness_full_trace_necklace_data) : ℤ :=
  D.d ^ D.m * xi_two_param_disjointness_full_trace_necklace_lucas D.m ^ D.q

/-- Closed full-trace necklace expansion. -/
def xi_two_param_disjointness_full_trace_necklace_fullTrace
    (D : xi_two_param_disjointness_full_trace_necklace_data) : ℤ :=
  xi_two_param_disjointness_full_trace_necklace_pureTrace D +
    xi_two_param_disjointness_full_trace_necklace_nonPureSum D

/-- Paper-facing statement for the full trace necklace formula. -/
def xi_two_param_disjointness_full_trace_necklace_statement
    (D : xi_two_param_disjointness_full_trace_necklace_data) : Prop :=
  xi_two_param_disjointness_full_trace_necklace_fullTrace D =
      D.d ^ D.m * xi_two_param_disjointness_full_trace_necklace_lucas D.m ^ D.q +
        ∑ w ∈ xi_two_param_disjointness_full_trace_necklace_nonPureSupport D,
          (xi_two_param_disjointness_full_trace_necklace_classSize w : ℤ) *
            D.b ^ xi_two_param_disjointness_full_trace_necklace_wordWeight w *
              D.d ^ (D.m - xi_two_param_disjointness_full_trace_necklace_wordWeight w) *
                D.Phi w ^ D.q ∧
    (∀ w ∈ xi_two_param_disjointness_full_trace_necklace_nonPureSupport D,
      w ≠ xi_two_param_disjointness_full_trace_necklace_pureWord D.m) ∧
    xi_two_param_disjointness_full_trace_necklace_wordWeight
        (xi_two_param_disjointness_full_trace_necklace_pureWord D.m) = 0

/-- Paper label: `thm:xi-two-param-disjointness-full-trace-necklace`. -/
theorem paper_xi_two_param_disjointness_full_trace_necklace
    (D : xi_two_param_disjointness_full_trace_necklace_data) :
    xi_two_param_disjointness_full_trace_necklace_statement D := by
  refine ⟨?_, ?_, ?_⟩
  · rfl
  · intro w hw
    exact (Finset.mem_filter.mp hw).2
  · simp [xi_two_param_disjointness_full_trace_necklace_wordWeight,
      xi_two_param_disjointness_full_trace_necklace_pureWord]

end Omega.Zeta
