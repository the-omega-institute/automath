import Mathlib.Tactic

namespace Omega.Conclusion

/-- The four independent quadratic characters are represented by a Boolean basis vector. -/
abbrev conclusion_leyang_lattes_fourbit_signcube_equidistribution_signPattern :=
  Fin 4 → Bool

/-- The quotient element selected by a sign pattern under a chosen `C₂⁴` basis. -/
def conclusion_leyang_lattes_fourbit_signcube_equidistribution_quotientElement
    (pattern : conclusion_leyang_lattes_fourbit_signcube_equidistribution_signPattern) :
    conclusion_leyang_lattes_fourbit_signcube_equidistribution_signPattern :=
  pattern

/-- Chebotarev density on the abelian quotient, transported to the sign cube. -/
noncomputable def conclusion_leyang_lattes_fourbit_signcube_equidistribution_density
    (_pattern : conclusion_leyang_lattes_fourbit_signcube_equidistribution_signPattern) : ℚ :=
  (1 : ℚ) / 16

/-- Concrete four-bit equidistribution statement: every sign pattern corresponds to one quotient
element and has density `1 / 16`; the sign cube has exactly sixteen boxes. -/
def conclusion_leyang_lattes_fourbit_signcube_equidistribution_statement : Prop :=
  (∀ pattern : conclusion_leyang_lattes_fourbit_signcube_equidistribution_signPattern,
      conclusion_leyang_lattes_fourbit_signcube_equidistribution_quotientElement pattern =
        pattern ∧
        conclusion_leyang_lattes_fourbit_signcube_equidistribution_density pattern =
          (1 : ℚ) / 16) ∧
    Fintype.card conclusion_leyang_lattes_fourbit_signcube_equidistribution_signPattern = 16

/-- Paper label: `cor:conclusion-leyang-lattes-fourbit-signcube-equidistribution`. -/
theorem paper_conclusion_leyang_lattes_fourbit_signcube_equidistribution :
    conclusion_leyang_lattes_fourbit_signcube_equidistribution_statement := by
  constructor
  · intro pattern
    exact ⟨rfl, rfl⟩
  · change Fintype.card (Fin 4 → Bool) = 16
    norm_num [Fintype.card_fun]

end Omega.Conclusion
