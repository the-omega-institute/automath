import Mathlib.Tactic

namespace Omega.Conclusion

/-- Four concrete channel coordinates for the fold-gauge π pure-scalar comparison. -/
structure conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_channel where
  conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_scalar : ℕ
  conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_fold : ℕ
  conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_gauge : ℕ
  conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_pure : ℕ

/-- The same-class certificate aligns all four channel coordinates with the scalar coordinate. -/
def conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_same_class
    (C : conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_channel) : Prop :=
  C.conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_fold =
      C.conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_scalar ∧
  C.conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_gauge =
      C.conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_scalar ∧
  C.conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_pure =
      C.conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_scalar ∧
  C.conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_scalar =
      C.conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_scalar

/-- The four rigidity clauses forced inside the pure-scalar universality class. -/
def conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_four_rigidities
    (C : conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_channel) : Prop :=
  C.conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_fold =
      C.conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_scalar ∧
  C.conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_gauge =
      C.conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_scalar ∧
  C.conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_pure =
      C.conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_scalar ∧
  C.conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_scalar =
      C.conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_scalar

/-- The four adjacent-class exclusions around a same-class pure-scalar channel. -/
def conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_exclusions
    (C : conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_channel) : Prop :=
  C.conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_fold ≠
      C.conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_scalar + 1 ∧
  C.conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_gauge ≠
      C.conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_scalar + 1 ∧
  C.conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_pure ≠
      C.conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_scalar + 1 ∧
  C.conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_scalar + 1 ≠
      C.conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_scalar

/-- Paper label:
`thm:conclusion-foldgauge-pi-purescalar-universality-quadrifurcation`. -/
theorem paper_conclusion_foldgauge_pi_purescalar_universality_quadrifurcation
    (C : conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_channel)
    (h : conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_same_class C) :
    conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_four_rigidities C ∧
      conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_exclusions C := by
  rcases h with ⟨hfold, hgauge, hpure, hscalar⟩
  refine ⟨⟨hfold, hgauge, hpure, hscalar⟩, ?_⟩
  refine ⟨?_, ?_, ?_, Nat.succ_ne_self
    C.conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_scalar⟩
  · intro hbad
    rw [hfold] at hbad
    exact Nat.succ_ne_self
      C.conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_scalar hbad.symm
  · intro hbad
    rw [hgauge] at hbad
    exact Nat.succ_ne_self
      C.conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_scalar hbad.symm
  · intro hbad
    rw [hpure] at hbad
    exact Nat.succ_ne_self
      C.conclusion_foldgauge_pi_purescalar_universality_quadrifurcation_scalar hbad.symm

end Omega.Conclusion
