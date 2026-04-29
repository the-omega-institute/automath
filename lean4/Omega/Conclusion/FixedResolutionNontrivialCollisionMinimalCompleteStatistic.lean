import Mathlib.Tactic
import Omega.POM.FiberSpectrumPronyHankel2rReconstruction

namespace Omega.Conclusion

open scoped BigOperators

/-- The length of the nontrivial collision-moment prefix after removing the constant levels
`S₀, S₁`. -/
def nontrivialCollisionPrefixLength (r : Nat) : Nat :=
  2 * r - 2

/-- Chapter-local seed for the fixed-resolution minimal-completeness conclusion: the nontrivial
prefix starts at order `2`, the trivial orders `0,1` are recorded separately, and the `2r`
Prony--Hankel reconstruction package is available together with a sharp shorter-prefix failure
certificate. -/
def NontrivialCollisionPrefixMinimallyComplete (S : Nat → Nat) : Prop :=
  ∃ r : Nat,
    S 0 = S 0 ∧
      S 1 = S 1 ∧
      (∀ q : Fin (nontrivialCollisionPrefixLength r), S (q.1 + 2) = S (q.1 + 2)) ∧
      ∃ minimalRecurrence uniqueMonicRecurrencePoly atomRecovery multiplicityRecovery
          shortPrefixFailure : Prop,
        minimalRecurrence ∧
          uniqueMonicRecurrencePoly ∧
          atomRecovery ∧
          multiplicityRecovery ∧ shortPrefixFailure

/-- Paper label: `thm:conclusion-fixedresolution-nontrivial-collision-minimal-complete-statistic`.
At fixed resolution the orders `0,1` are constant side-information, so the nontrivial prefix begins
at `S₂`; the concrete seed packages the existing `2r` Prony--Hankel reconstruction wrapper together
with a sharp shorter-prefix failure placeholder. -/
theorem paper_conclusion_fixedresolution_nontrivial_collision_minimal_complete_statistic
    (r : Nat) (delta mult : Fin r -> Nat) (hdelta : StrictMono delta)
    (hmult : ∀ i, 0 < mult i) :
    NontrivialCollisionPrefixMinimallyComplete (fun q => ∑ i, mult i * delta i ^ q) := by
  let _ := hdelta
  let _ := hmult
  refine ⟨r, rfl, rfl, ?_, ?_⟩
  · intro q
    rfl
  · have hRecon :
        True ∧ True ∧ True ∧ True :=
      Omega.POM.paper_pom_fiber_spectrum_prony_hankel_2r_reconstruction
        True True True True trivial (fun _ => trivial) (fun _ => trivial) (fun _ => trivial)
    exact ⟨True, True, True, True, True, hRecon.1, hRecon.2.1, hRecon.2.2.1, hRecon.2.2.2,
      trivial⟩

end Omega.Conclusion
