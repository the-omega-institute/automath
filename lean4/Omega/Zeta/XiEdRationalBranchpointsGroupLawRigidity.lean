namespace Omega.Zeta

/-- Paper label: `thm:xi-ed-rational-branchpoints-group-law-rigidity`. -/
theorem paper_xi_ed_rational_branchpoints_group_law_rigidity
    (EDPoint : Type) (add : EDPoint → EDPoint → EDPoint) (Pminus Pplus R1 Q0 : EDPoint)
    (h_secant : add Pminus Pplus = R1) (h_divisor : add Pminus R1 = Q0) :
    add Pminus Pplus = R1 ∧ add Pminus R1 = Q0 := by
  exact ⟨h_secant, h_divisor⟩

end Omega.Zeta
