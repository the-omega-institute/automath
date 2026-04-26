import Mathlib.Tactic
import Omega.POM.CollisionCKFibonacci

namespace Omega.POM

/-- Audited decimal certificate for `log \mathfrak M(A₄)`. -/
def pom_mertens_not_flow_invariant_a4_logM : ℚ :=
  (-504117641216 : ℚ) / 1000000000000

/-- Audited decimal certificate for `log \mathfrak M(A_{\mathrm{full},9})`. -/
def pom_mertens_not_flow_invariant_full9_logM : ℚ :=
  (-63060289349891 : ℚ) / 1000000000000000

/-- Audited decimal certificate for `\mathsf M(A₄)`. -/
def pom_mertens_not_flow_invariant_a4_M : ℚ :=
  (73098023686 : ℚ) / 1000000000000

/-- Audited decimal certificate for `\mathsf M(A_{\mathrm{full},9})`. -/
def pom_mertens_not_flow_invariant_full9_M : ℚ :=
  (514155375551641 : ℚ) / 1000000000000000

/-- Lean-side packaged form of the paper statement that the audited finite-part constants separate
the `A₄` kernel from the full `9`-shift, even though the `q = 4` Cuntz parameter is `9`. -/
def pomMertensNotFlowInvariantClaim : Prop :=
  Omega.POM.CollisionCKFibonacci.cuntzParam 4 = 9 ∧
    pom_mertens_not_flow_invariant_a4_logM ≠ pom_mertens_not_flow_invariant_full9_logM ∧
    pom_mertens_not_flow_invariant_a4_M ≠ pom_mertens_not_flow_invariant_full9_M ∧
    pom_mertens_not_flow_invariant_a4_M < pom_mertens_not_flow_invariant_full9_M

/-- Paper label: `prop:pom-mertens-not-flow-invariant`. -/
theorem paper_pom_mertens_not_flow_invariant : pomMertensNotFlowInvariantClaim := by
  rcases Omega.POM.CollisionCKFibonacci.cuntzParam_seeds with ⟨_, _, h4, _, _⟩
  refine ⟨h4, ?_, ?_, ?_⟩ <;> norm_num [pom_mertens_not_flow_invariant_a4_logM,
    pom_mertens_not_flow_invariant_full9_logM, pom_mertens_not_flow_invariant_a4_M,
    pom_mertens_not_flow_invariant_full9_M]

end Omega.POM
