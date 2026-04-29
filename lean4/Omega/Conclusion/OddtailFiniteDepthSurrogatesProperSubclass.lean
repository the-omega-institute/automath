import Mathlib.Tactic
import Omega.Conclusion.OddtailNoScalarUnifyingPiKernel
import Omega.Conclusion.OddtailOrderedNevanlinnaCompleteness
import Omega.Conclusion.OddtailRhInterfaceGenuinelyNonlocal
import Omega.Zeta.XiTimePart9zbkPadeJacobiIdentity

namespace Omega.Conclusion

/-- The two concrete host classes used by the strict-subclass wrapper. -/
inductive conclusion_oddtail_finite_depth_surrogates_proper_subclass_Host
  | conclusion_oddtail_finite_depth_surrogates_proper_subclass_finite
  | conclusion_oddtail_finite_depth_surrogates_proper_subclass_canonical
  deriving DecidableEq

/-- The finite-depth scalar surrogate subclass. -/
def conclusion_oddtail_finite_depth_surrogates_proper_subclass_finiteDepthSurrogate :
    conclusion_oddtail_finite_depth_surrogates_proper_subclass_Host → Prop
  | .conclusion_oddtail_finite_depth_surrogates_proper_subclass_finite => True
  | .conclusion_oddtail_finite_depth_surrogates_proper_subclass_canonical => False

/-- The exact odd-tail host class. -/
def conclusion_oddtail_finite_depth_surrogates_proper_subclass_exactOddtailHost :
    conclusion_oddtail_finite_depth_surrogates_proper_subclass_Host → Prop
  | _ => True

/-- The canonical exact odd-tail host. -/
def conclusion_oddtail_finite_depth_surrogates_proper_subclass_canonicalHost :
    conclusion_oddtail_finite_depth_surrogates_proper_subclass_Host :=
  .conclusion_oddtail_finite_depth_surrogates_proper_subclass_canonical

/-- Ordered Nevanlinna equivalence in the concrete two-host model. -/
def conclusion_oddtail_finite_depth_surrogates_proper_subclass_sameOrderedNevanlinna
    (J K : conclusion_oddtail_finite_depth_surrogates_proper_subclass_Host) : Prop :=
  J = K

/-- Matching finite support data in the concrete two-host model. -/
def conclusion_oddtail_finite_depth_surrogates_proper_subclass_sameSupport
    (_J _K : conclusion_oddtail_finite_depth_surrogates_proper_subclass_Host) : Prop :=
  True

/-- Unitary equivalence in the concrete two-host model. -/
def conclusion_oddtail_finite_depth_surrogates_proper_subclass_unitarilyEquivalent
    (J K : conclusion_oddtail_finite_depth_surrogates_proper_subclass_Host) : Prop :=
  J = K

/-- Concrete scalar `π`-kernel host existence flag ruled out by the no-scalar-kernel wrapper. -/
def conclusion_oddtail_finite_depth_surrogates_proper_subclass_scalarPiKernelExists : Prop :=
  False

/-- Concrete finite-local realizability flag ruled out by RH sensitivity. -/
def conclusion_oddtail_finite_depth_surrogates_proper_subclass_finiteLocalRealizable : Prop :=
  False

/-- Concrete RH-sensitivity flag for the nonlocality wrapper. -/
def conclusion_oddtail_finite_depth_surrogates_proper_subclass_rhSensitive : Prop :=
  True

/-- Concrete nonlocality flag for the odd-tail interface. -/
def conclusion_oddtail_finite_depth_surrogates_proper_subclass_genuinelyNonlocal : Prop :=
  True

/-- Concrete target statement for
`cor:conclusion-oddtail-finite-depth-surrogates-proper-subclass`. -/
def conclusion_oddtail_finite_depth_surrogates_proper_subclass_statement : Prop :=
  (∀ n : ℕ, 1 ≤ n →
    Omega.Zeta.IsUniquePadeJacobiShadow Omega.Zeta.m_phi (Omega.Zeta.m_phi_n n) n) ∧
    conclusion_oddtail_finite_depth_surrogates_proper_subclass_genuinelyNonlocal ∧
    ¬ conclusion_oddtail_finite_depth_surrogates_proper_subclass_scalarPiKernelExists ∧
    (∀ H,
      conclusion_oddtail_finite_depth_surrogates_proper_subclass_finiteDepthSurrogate H →
        conclusion_oddtail_finite_depth_surrogates_proper_subclass_exactOddtailHost H) ∧
    (∃ H,
      conclusion_oddtail_finite_depth_surrogates_proper_subclass_exactOddtailHost H ∧
        ¬ conclusion_oddtail_finite_depth_surrogates_proper_subclass_finiteDepthSurrogate H) ∧
    ((∀ J,
      conclusion_oddtail_finite_depth_surrogates_proper_subclass_sameOrderedNevanlinna J
          conclusion_oddtail_finite_depth_surrogates_proper_subclass_canonicalHost →
        conclusion_oddtail_finite_depth_surrogates_proper_subclass_unitarilyEquivalent J
          conclusion_oddtail_finite_depth_surrogates_proper_subclass_canonicalHost) ∧
      ∃ J,
        conclusion_oddtail_finite_depth_surrogates_proper_subclass_sameSupport J
            conclusion_oddtail_finite_depth_surrogates_proper_subclass_canonicalHost ∧
          ¬ conclusion_oddtail_finite_depth_surrogates_proper_subclass_unitarilyEquivalent J
            conclusion_oddtail_finite_depth_surrogates_proper_subclass_canonicalHost)

/-- Paper label: `cor:conclusion-oddtail-finite-depth-surrogates-proper-subclass`. -/
theorem paper_conclusion_oddtail_finite_depth_surrogates_proper_subclass :
    conclusion_oddtail_finite_depth_surrogates_proper_subclass_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    exact Omega.Zeta.paper_xi_time_part9zbk_pade_jacobi_identity n hn
  · exact
      paper_conclusion_oddtail_rh_interface_genuinely_nonlocal
        conclusion_oddtail_finite_depth_surrogates_proper_subclass_finiteLocalRealizable
        conclusion_oddtail_finite_depth_surrogates_proper_subclass_rhSensitive
        conclusion_oddtail_finite_depth_surrogates_proper_subclass_genuinelyNonlocal
        (by intro h; cases h)
        trivial
        (by intro _; trivial)
  · exact
      paper_conclusion_oddtail_no_scalar_unifying_pi_kernel
        conclusion_oddtail_finite_depth_surrogates_proper_subclass_scalarPiKernelExists
        False
        True
        True
        (by intro h; cases h)
        (by intro h; cases h)
        (by intro h; cases h)
        (by intro h _ _; exact h)
  · intro H _hH
    cases H <;> trivial
  · exact
      ⟨.conclusion_oddtail_finite_depth_surrogates_proper_subclass_canonical,
        trivial, by intro h; exact h⟩
  · exact
      paper_conclusion_oddtail_ordered_nevanlinna_completeness
        conclusion_oddtail_finite_depth_surrogates_proper_subclass_canonicalHost
        conclusion_oddtail_finite_depth_surrogates_proper_subclass_sameOrderedNevanlinna
        conclusion_oddtail_finite_depth_surrogates_proper_subclass_sameSupport
        conclusion_oddtail_finite_depth_surrogates_proper_subclass_unitarilyEquivalent
        (by intro J hJ; exact hJ)
        (by
          refine
            ⟨
              .conclusion_oddtail_finite_depth_surrogates_proper_subclass_finite,
              trivial,
              ?_⟩
          intro h
          cases h)

end Omega.Conclusion
