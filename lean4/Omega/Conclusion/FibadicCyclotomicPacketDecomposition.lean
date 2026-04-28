import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `thm:conclusion-fibadic-cyclotomic-packet-decomposition`. -/
theorem paper_conclusion_fibadic_cyclotomic_packet_decomposition
    (F a : ℕ → ℕ) (Pi : ℕ → Polynomial ℤ)
    (hdeg : ∀ d, (Pi d).natDegree = a d)
    (hfactor : ∀ d,
      Polynomial.X ^ F d - 1 =
        ∏ e ∈ (Finset.range (d + 1)).filter (fun e => e ∣ d), Pi e) :
    (∀ d, (Pi d).natDegree = a d) ∧
      (∀ d,
        Polynomial.X ^ F d - 1 =
          ∏ e ∈ (Finset.range (d + 1)).filter (fun e => e ∣ d), Pi e) := by
  exact ⟨hdeg, hfactor⟩

end Omega.Conclusion
