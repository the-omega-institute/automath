import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic
import Omega.Folding.FiberWeightCountComplement

namespace Omega.Folding

open scoped ComplexConjugate

/-- The complement shift appearing in the fold reciprocity formulas. -/
def foldComplementShift (m : ℕ) : ℕ :=
  Nat.fib (m + 1) - 2

/-- The half-phase attached to the complement shift. -/
noncomputable def foldComplementPhaseAngle (m k : ℕ) : ℂ :=
  Real.pi * Complex.I * ((k * foldComplementShift m : ℝ) / (Nat.fib (m + 2) : ℝ))

/-- The phase factor relating a Fourier coefficient to its complex conjugate. -/
noncomputable def foldComplementPhaseFactor (m k : ℕ) : ℂ :=
  Complex.exp (-2 * foldComplementPhaseAngle m k)

/-- A concrete phase-normalized Fourier coefficient built from the residue-count profile and the
complement half-phase. -/
noncomputable def foldComplementFourierCoefficient (m k : ℕ) : ℂ :=
  Complex.exp (-foldComplementPhaseAngle m k) * (weightCongruenceCount m k : ℂ)

/-- Package form of the complement-induced Fourier phase locking. -/
def FoldFourierPhaseLockingByComplement (m : ℕ) : Prop :=
  ∀ k : ℕ,
    foldComplementFourierCoefficient m k =
        foldComplementPhaseFactor m k * conj (foldComplementFourierCoefficient m k) ∧
      ∃ t : ℝ,
        Complex.exp (foldComplementPhaseAngle m k) * foldComplementFourierCoefficient m k = (t : ℂ)

/-- The complement half-phase normalizes the concrete Fourier coefficient to a real number, and
equivalently the raw coefficient is locked to its complex conjugate by the complement phase.
    cor:fold-fourier-phase-locking-by-complement -/
theorem paper_fold_fourier_phase_locking_by_complement (m : ℕ) :
    FoldFourierPhaseLockingByComplement m := by
  intro k
  refine ⟨?_, ?_⟩
  · unfold foldComplementFourierCoefficient foldComplementPhaseFactor
    set θ : ℂ := foldComplementPhaseAngle m k
    have hθ : conj θ = -θ := by
      simp [θ, foldComplementPhaseAngle, mul_assoc, mul_left_comm, mul_comm]
    have hconjCoeff :
        conj (Complex.exp (-θ) * (weightCongruenceCount m k : ℂ)) =
          Complex.exp θ * (weightCongruenceCount m k : ℂ) := by
      calc
        conj (Complex.exp (-θ) * (weightCongruenceCount m k : ℂ))
            = conj (Complex.exp (-θ)) * (weightCongruenceCount m k : ℂ) := by
                simp
        _ = Complex.exp θ * (weightCongruenceCount m k : ℂ) := by
              rw [show conj (Complex.exp (-θ)) = Complex.exp θ by
                calc
                  conj (Complex.exp (-θ)) = Complex.exp (conj (-θ)) := by
                    simpa using (Complex.exp_conj (-θ)).symm
                  _ = Complex.exp θ := by simp [hθ]]
    symm
    calc
      Complex.exp (-2 * θ) * conj (Complex.exp (-θ) * (weightCongruenceCount m k : ℂ))
          = Complex.exp (-2 * θ) * (Complex.exp θ * (weightCongruenceCount m k : ℂ)) := by
              rw [hconjCoeff]
      _ = (Complex.exp (-2 * θ) * Complex.exp θ) * (weightCongruenceCount m k : ℂ) := by
            simp [mul_assoc]
      _ = Complex.exp (-2 * θ + θ) * (weightCongruenceCount m k : ℂ) := by
            rw [← Complex.exp_add]
      _ = Complex.exp (-θ) * (weightCongruenceCount m k : ℂ) := by
            congr 1
            ring
      _ = foldComplementFourierCoefficient m k := by
            simp [foldComplementFourierCoefficient, θ]
  · refine ⟨weightCongruenceCount m k, ?_⟩
    unfold foldComplementFourierCoefficient
    set θ : ℂ := foldComplementPhaseAngle m k
    calc
      Complex.exp θ * (Complex.exp (-θ) * (weightCongruenceCount m k : ℂ))
          = (Complex.exp θ * Complex.exp (-θ)) * (weightCongruenceCount m k : ℂ) := by
              simp [mul_assoc]
      _ = Complex.exp (θ + -θ) * (weightCongruenceCount m k : ℂ) := by
            rw [← Complex.exp_add]
      _ = (weightCongruenceCount m k : ℂ) := by
            simp

end Omega.Folding
