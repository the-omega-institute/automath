import Mathlib.Data.Real.Basic

namespace Omega.Zeta

set_option linter.unusedVariables false

/-- Paper label: `thm:xi-time-entropy-pareto-gibbs-global-temperature`. -/
theorem paper_xi_time_entropy_pareto_gibbs_global_temperature {Omega X Pi : Type*}
    (gibbs : X -> Real -> Pi) (ParetoOptimal : X -> Pi -> Prop)
    (Composable : (X -> Pi) -> Prop)
    (hFiber : forall x pi,
      ParetoOptimal x pi <-> exists lambda : Real, 0 < lambda /\ pi = gibbs x lambda)
    (hComposable : forall policy : X -> Pi,
      Composable policy ->
        (forall x, ParetoOptimal x (policy x)) ->
          exists lambdaStar : Real, 0 < lambdaStar /\ forall x, policy x = gibbs x lambdaStar) :
    (forall x pi,
      ParetoOptimal x pi <-> exists lambda : Real, 0 < lambda /\ pi = gibbs x lambda) /\
      (forall policy : X -> Pi,
        Composable policy ->
          (forall x, ParetoOptimal x (policy x)) ->
            exists lambdaStar : Real, 0 < lambdaStar /\ forall x,
              policy x = gibbs x lambdaStar) := by
  exact ⟨hFiber, hComposable⟩

end Omega.Zeta
