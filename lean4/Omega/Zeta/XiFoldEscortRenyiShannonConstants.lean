import Omega.Zeta.XiFoldEscortRenyiConstantThetaClosed

namespace Omega.Zeta

noncomputable section

/-- The Rényi constant in theta-core form for the escort family. -/
def xi_fold_escort_renyi_shannon_constants_renyi_theta_constant (q r : ℕ) : ℝ :=
  xiFoldEscortRenyiThetaCore q r

/-- The closed Rényi constant after eliminating the escort theta parameter. -/
def xi_fold_escort_renyi_shannon_constants_renyi_closed_constant (q r : ℕ) : ℝ :=
  xiFoldEscortRenyiClosedCore q r

/-- The Shannon constant in theta-core form. -/
def xi_fold_escort_renyi_shannon_constants_shannon_theta_constant (q : ℕ) : ℝ :=
  xiFoldEscortBinaryEntropy q

/-- The closed Shannon constant at the golden-ratio escort parameter. -/
def xi_fold_escort_renyi_shannon_constants_shannon_closed_constant (q : ℕ) : ℝ :=
  Real.log (1 + Real.goldenRatio ^ (q + 1)) -
    ((q + 1 : ℝ) * (1 - xiFoldEscortTheta q)) * Real.log Real.goldenRatio

/-- Paper label: `thm:xi-fold-escort-renyi-shannon-constants`. -/
def xi_fold_escort_renyi_shannon_constants_statement (q r : ℕ) : Prop :=
  xi_fold_escort_renyi_shannon_constants_renyi_theta_constant q r =
      xi_fold_escort_renyi_shannon_constants_renyi_closed_constant q r ∧
    xi_fold_escort_renyi_shannon_constants_shannon_theta_constant q =
      xi_fold_escort_renyi_shannon_constants_shannon_closed_constant q

/-- Paper label: `thm:xi-fold-escort-renyi-shannon-constants`. -/
theorem paper_xi_fold_escort_renyi_shannon_constants (q r : ℕ) (hr : 2 ≤ r)
    (hShannon :
      xiFoldEscortBinaryEntropy q =
        Real.log (1 + Real.goldenRatio ^ (q + 1)) -
          ((q + 1 : ℝ) * (1 - xiFoldEscortTheta q)) * Real.log Real.goldenRatio) :
    xi_fold_escort_renyi_shannon_constants_statement q r := by
  have hr_one : 1 ≤ r := le_trans (by norm_num) hr
  have hclosed := paper_xi_fold_escort_renyi_constant_theta_closed q r hShannon hr_one
  simpa [xi_fold_escort_renyi_shannon_constants_statement,
    xi_fold_escort_renyi_shannon_constants_renyi_theta_constant,
    xi_fold_escort_renyi_shannon_constants_renyi_closed_constant,
    xi_fold_escort_renyi_shannon_constants_shannon_theta_constant,
    xi_fold_escort_renyi_shannon_constants_shannon_closed_constant] using hclosed

end

end Omega.Zeta
