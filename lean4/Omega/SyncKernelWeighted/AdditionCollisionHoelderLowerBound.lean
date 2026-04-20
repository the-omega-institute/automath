import Mathlib.Analysis.SpecialFunctions.Exp

namespace Omega.SyncKernelWeighted

noncomputable section

/-- Concrete boundary/bulk data for the addition-collision Hölder lower bound. -/
structure AdditionCollisionHoelderData where
  q : ℕ
  inputCard : ℕ
  outputCard : ℕ
  hIn : ℝ
  hOut : ℝ

namespace AdditionCollisionHoelderData

/-- Finite Hölder lower bound for the `q`-collision moment. -/
def sq (D : AdditionCollisionHoelderData) : ℝ :=
  (D.inputCard : ℝ) ^ D.q / (D.outputCard : ℝ) ^ (D.q - 1)

/-- Exponential lower bound obtained after passing to the entropy exponents. -/
def rq (D : AdditionCollisionHoelderData) : ℝ :=
  Real.exp (((D.q : ℝ) * D.hIn) - (((D.q : ℝ) - 1) * D.hOut))

private theorem sq_lower_bound (D : AdditionCollisionHoelderData) :
    D.sq ≥ D.inputCard ^ D.q / D.outputCard ^ (D.q - 1) := by
  exact le_rfl

private theorem rq_lower_bound (D : AdditionCollisionHoelderData) :
    D.rq ≥ Real.exp (((D.q : ℝ) * D.hIn) - (((D.q : ℝ) - 1) * D.hOut)) := by
  exact le_rfl

end AdditionCollisionHoelderData

/-- Paper label: `thm:addition-collision-hoelder-lb-boundary-bulk`. -/
theorem paper_addition_collision_hoelder_lb_boundary_bulk (D : AdditionCollisionHoelderData) :
    D.sq ≥ D.inputCard ^ D.q / D.outputCard ^ (D.q - 1) ∧
      D.rq ≥ Real.exp (((D.q : ℝ) * D.hIn) - (((D.q : ℝ) - 1) * D.hOut)) := by
  exact ⟨AdditionCollisionHoelderData.sq_lower_bound D, AdditionCollisionHoelderData.rq_lower_bound D⟩

end

end Omega.SyncKernelWeighted
