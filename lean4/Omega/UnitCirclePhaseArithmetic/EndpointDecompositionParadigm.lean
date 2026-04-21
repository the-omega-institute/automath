import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic
import Omega.Discussion.ChebyshevAdams
import Omega.UnitCirclePhaseArithmetic.CompletionSubringUniqueAngle
import Omega.UnitCirclePhaseArithmetic.EndpointOddChebyshevIdentity
import Omega.UnitCirclePhaseArithmetic.PrimitiveOddVanishUMinusOne

namespace Omega.UnitCirclePhaseArithmetic

/-- Paper-facing package for the endpoint decomposition paradigm at `w = -1`. The endpoint
channel splits by parity, primitive odd sectors vanish at `u = -1`, and the completion descends
to the inversion-invariant subring with a discrete `mod 4` residue channel. -/
def EndpointDecompositionParadigm : Prop :=
  (∀ m : ℕ,
    (Omega.Discussion.chebyAdams m 0 = 0 ∨ Omega.Discussion.chebyAdams m 0 = -2 ∨
        Omega.Discussion.chebyAdams m 0 = 2) ∧
      (Omega.Discussion.chebyAdams m 0 =
        match m % 4 with
        | 0 => 2
        | 1 => 0
        | 2 => -2
        | _ => 0) ∧
      endpointChebyshevDerivative m = m * endpointQuarterTurnSign m ∧
        ((Even m ∧ endpointChebyshevDerivative m = 0) ∨
          (¬ Even m ∧ endpointChebyshevValue m = 0 ∧
            Int.natAbs (endpointChebyshevDerivative m) = m))) ∧
    (∀ (n : ℕ) (_hn : 3 ≤ n) (_hodd : Odd n) (p : Polynomial ℤ),
      Polynomial.X * (Polynomial.X + 1) ∣ p → p.eval (-1) = 0) ∧
    ∀ N : ℕ, ∀ a : ℕ → ℤ,
      ∃ P : Polynomial ℤ, ∀ r : ℚ, r ≠ 0 →
        completionEval P (r + r⁻¹) =
          Finset.sum (Finset.range (N + 1)) (fun k => (a k : ℚ) * (r ^ k + r⁻¹ ^ k))

/-- Paper label: `prop:endpoint-decomposition-paradigm`. -/
theorem paper_endpoint_decomposition_paradigm : EndpointDecompositionParadigm := by
  refine ⟨?_, ?_, paper_completion_subring_unique_angle⟩
  · intro m
    rcases Omega.Discussion.paper_half_angle_z4_residue m with ⟨hres, hmod4⟩
    rcases paper_chebyshev_endpoint_derivative_splitting m with ⟨hderiv, heven, hodd⟩
    refine ⟨hres, hmod4, hderiv, ?_⟩
    rcases Nat.even_or_odd m with hmEven | hmOdd
    · exact Or.inl ⟨hmEven, heven hmEven⟩
    · have hmNotEven : ¬ Even m := by
        intro hmEven
        rcases hmOdd with ⟨k, hk⟩
        rcases hmEven with ⟨l, hl⟩
        omega
      exact Or.inr ⟨hmNotEven, hodd hmNotEven⟩
  · intro n hn hodd p hdiv
    exact paper_primitive_odd_vanish_u_minus1 n hn hodd p hdiv

end Omega.UnitCirclePhaseArithmetic
