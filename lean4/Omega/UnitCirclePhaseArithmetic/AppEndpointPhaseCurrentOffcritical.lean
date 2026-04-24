import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.AppBusemannPoissonMinusOne
import Omega.UnitCirclePhaseArithmetic.AppEndpointBlaschkeRadialAbsorption
import Omega.Zeta.OffcriticalHorocycleBusemann

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- The Cayley image of the off-critical point `γ + iδ`. -/
def appOffcriticalCayleyPoint (γ δ : ℝ) : ℂ :=
  let t : ℂ := (γ : ℂ) + δ * Complex.I
  (1 + Complex.I * t) / (1 - Complex.I * t)

/-- A boundary point is transported from an off-critical zero with horizontal coordinate `γ`
and offset `δ`. -/
def TransportedOffcriticalZero (a : ℂ) (δ : ℝ) : Prop :=
  ∃ γ : ℝ, 0 < δ ∧ a = appOffcriticalCayleyPoint γ δ

/-- The endpoint phase current dominates the total off-critical offset contributed by the
transported zeros. In this concrete model the transported contribution is recorded exactly by the
endpoint absorption sum. -/
def AppEndpointPhaseCurrentOffcriticalStatement (roots : List ℂ) (deltas : List ℝ) : Prop :=
  List.Forall₂ TransportedOffcriticalZero roots deltas →
    endpointBlaschkeRadialAbsorption roots = deltas.sum ∧ deltas.sum ≤ endpointBlaschkeRadialAbsorption roots

private lemma endpointPoissonMinusOne_transport_eq_delta {a : ℂ} {δ : ℝ}
    (htransport : TransportedOffcriticalZero a δ) : endpointPoissonMinusOne a = δ := by
  rcases htransport with ⟨γ, hδ, rfl⟩
  have hdepth := Omega.Zeta.paper_app_offcritical_horocycle_busemann γ δ hδ
  have _ : 0 ≤ Omega.Zeta.appOffcriticalBoundaryDepth γ δ := by
    rcases hdepth with ⟨_, hclosed⟩
    rw [hclosed]
    positivity
  unfold endpointPoissonMinusOne
  simpa [appOffcriticalCayleyPoint] using paper_app_busemann_poisson_minus1 γ δ hδ

private lemma endpointBlaschkeRadialAbsorption_eq_transport_sum {roots : List ℂ} {deltas : List ℝ}
    (htransport : List.Forall₂ TransportedOffcriticalZero roots deltas) :
    endpointBlaschkeRadialAbsorption roots = deltas.sum := by
  induction htransport with
  | nil =>
      simp [endpointBlaschkeRadialAbsorption]
  | @cons a δ roots deltas ha htail ih =>
      simpa [endpointBlaschkeRadialAbsorption, endpointPoissonMinusOne_transport_eq_delta ha] using ih

/-- Paper label: `cor:app-endpoint-phase-current-offcritical`. The endpoint phase current of the
finite Blaschke family dominates the total off-critical displacement carried by the transported
zeros, term by term and hence after summation. -/
theorem paper_app_endpoint_phase_current_offcritical (roots : List ℂ) (deltas : List ℝ) :
    AppEndpointPhaseCurrentOffcriticalStatement roots deltas := by
  intro htransport
  refine ⟨endpointBlaschkeRadialAbsorption_eq_transport_sum htransport, ?_⟩
  exact le_of_eq (endpointBlaschkeRadialAbsorption_eq_transport_sum htransport).symm

end

end Omega.UnitCirclePhaseArithmetic
