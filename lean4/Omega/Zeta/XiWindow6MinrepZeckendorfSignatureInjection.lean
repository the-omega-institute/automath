import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- The Apéry threshold `w_r = 34 * ((13 * r) % 21)` for the window-`6` tail semigroup. -/
def xi_window6_minrep_zeckendorf_signature_injection_w (r : Fin 21) : ℕ :=
  34 * ((13 * r.1) % 21)

/-- The minimal reachable representative `D_r^min = 12 + w_r`. -/
def xi_window6_minrep_zeckendorf_signature_injection_dMin (r : Fin 21) : ℕ :=
  12 + xi_window6_minrep_zeckendorf_signature_injection_w r

/-- The explicit Zeckendorf index set from the paper table for each residue class `r mod 21`. -/
def xi_window6_minrep_zeckendorf_signature_injection_signature (r : Fin 21) : Finset ℕ :=
  match r.1 with
  | 0 => [2, 4, 6].toFinset
  | 1 => [2, 8, 10, 14].toFinset
  | 2 => [2, 4, 9, 12].toFinset
  | 3 => [2, 7, 15].toFinset
  | 4 => [2, 6, 8, 11, 13].toFinset
  | 5 => [2, 4, 8, 10].toFinset
  | 6 => [2, 12, 14].toFinset
  | 7 => [2, 4, 7, 13].toFinset
  | 8 => [2, 5, 8, 10, 15].toFinset
  | 9 => [2, 6, 9, 14].toFinset
  | 10 => [2, 4, 12].toFinset
  | 11 => [2, 7, 10, 12, 14].toFinset
  | 12 => [2, 6, 8, 10, 13].toFinset
  | 13 => [2, 4, 6, 9].toFinset
  | 14 => [2, 8, 11, 14].toFinset
  | 15 => [2, 4, 7, 10, 12].toFinset
  | 16 => [2, 7, 9, 15].toFinset
  | 17 => [2, 6, 14].toFinset
  | 18 => [2, 4, 8, 11].toFinset
  | 19 => [2, 9, 12, 14].toFinset
  | _ => [2, 4, 7, 9, 13].toFinset

/-- The Fibonacci value of a Zeckendorf signature. -/
def xi_window6_minrep_zeckendorf_signature_injection_signatureValue (S : Finset ℕ) : ℕ :=
  S.sum Nat.fib

/-- Paper label: `prop:xi-window6-minrep-zeckendorf-signature-injection`.
The `21` minimal reachable representatives admit explicit Zeckendorf signatures; each evaluates to
`D_r^min`, every signature contains index `2` but omits `3`, the indices are pairwise
nonconsecutive, and the resulting signature map is injective on residues modulo `21`. -/
theorem paper_xi_window6_minrep_zeckendorf_signature_injection :
    (∀ r : Fin 21,
      xi_window6_minrep_zeckendorf_signature_injection_signatureValue
          (xi_window6_minrep_zeckendorf_signature_injection_signature r) =
        xi_window6_minrep_zeckendorf_signature_injection_dMin r ∧
        (∀ k ∈ xi_window6_minrep_zeckendorf_signature_injection_signature r,
          k + 1 ∉ xi_window6_minrep_zeckendorf_signature_injection_signature r) ∧
        2 ∈ xi_window6_minrep_zeckendorf_signature_injection_signature r ∧
        3 ∉ xi_window6_minrep_zeckendorf_signature_injection_signature r) ∧
      Function.Injective xi_window6_minrep_zeckendorf_signature_injection_signature := by
  native_decide

end Omega.Zeta
