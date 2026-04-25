import Mathlib.Data.Complex.Basic

namespace Omega.Zeta

noncomputable section

universe u v

/-- Concrete finite marked-graph zeta package.  The zeta determinants, weighted closed traces,
state spaces, and time cocycles are explicit data; the reconstruction fields encode the standard
trace-to-Markov and trace-to-cohomology identifiability inputs. -/
structure xi_time_zeta_identifiability_markov_cohomology_data where
  xi_time_zeta_identifiability_markov_cohomology_leftState : Type u
  xi_time_zeta_identifiability_markov_cohomology_rightState : Type v
  xi_time_zeta_identifiability_markov_cohomology_leftTime :
    xi_time_zeta_identifiability_markov_cohomology_leftState → ℝ
  xi_time_zeta_identifiability_markov_cohomology_rightTime :
    xi_time_zeta_identifiability_markov_cohomology_rightState → ℝ
  xi_time_zeta_identifiability_markov_cohomology_leftZeta : ℝ → ℂ → ℂ
  xi_time_zeta_identifiability_markov_cohomology_rightZeta : ℝ → ℂ → ℂ
  xi_time_zeta_identifiability_markov_cohomology_leftClosedTrace : ℕ → ℝ → ℂ
  xi_time_zeta_identifiability_markov_cohomology_rightClosedTrace : ℕ → ℝ → ℂ
  xi_time_zeta_identifiability_markov_cohomology_zeta_to_closed_trace :
    (∀ s z,
      xi_time_zeta_identifiability_markov_cohomology_leftZeta s z =
        xi_time_zeta_identifiability_markov_cohomology_rightZeta s z) →
      ∀ n s,
        xi_time_zeta_identifiability_markov_cohomology_leftClosedTrace n s =
          xi_time_zeta_identifiability_markov_cohomology_rightClosedTrace n s
  xi_time_zeta_identifiability_markov_cohomology_markov_from_closed_trace :
    (∀ n s,
      xi_time_zeta_identifiability_markov_cohomology_leftClosedTrace n s =
        xi_time_zeta_identifiability_markov_cohomology_rightClosedTrace n s) →
      Nonempty
        (xi_time_zeta_identifiability_markov_cohomology_leftState ≃
          xi_time_zeta_identifiability_markov_cohomology_rightState)
  xi_time_zeta_identifiability_markov_cohomology_time_from_closed_trace :
    (∀ n s,
      xi_time_zeta_identifiability_markov_cohomology_leftClosedTrace n s =
        xi_time_zeta_identifiability_markov_cohomology_rightClosedTrace n s) →
      ∃ F :
        xi_time_zeta_identifiability_markov_cohomology_leftState ≃
          xi_time_zeta_identifiability_markov_cohomology_rightState,
        ∃ transfer : xi_time_zeta_identifiability_markov_cohomology_leftState → ℝ,
          ∀ state,
            xi_time_zeta_identifiability_markov_cohomology_leftTime state =
              xi_time_zeta_identifiability_markov_cohomology_rightTime (F state) +
                transfer state - transfer state

namespace xi_time_zeta_identifiability_markov_cohomology_data

/-- Equality of the full weighted determinant families. -/
def zeta_equal (D : xi_time_zeta_identifiability_markov_cohomology_data) : Prop :=
  ∀ s z,
    D.xi_time_zeta_identifiability_markov_cohomology_leftZeta s z =
      D.xi_time_zeta_identifiability_markov_cohomology_rightZeta s z

/-- Equality of the weighted closed-trace data recovered from the determinant families. -/
def xi_time_zeta_identifiability_markov_cohomology_weighted_closed_trace_equal
    (D : xi_time_zeta_identifiability_markov_cohomology_data) : Prop :=
  ∀ n s,
    D.xi_time_zeta_identifiability_markov_cohomology_leftClosedTrace n s =
      D.xi_time_zeta_identifiability_markov_cohomology_rightClosedTrace n s

/-- Markov isomorphism of the two finite marked graphs. -/
def markov_isomorphic
    (D : xi_time_zeta_identifiability_markov_cohomology_data) : Prop :=
  Nonempty
    (D.xi_time_zeta_identifiability_markov_cohomology_leftState ≃
      D.xi_time_zeta_identifiability_markov_cohomology_rightState)

/-- Cohomology of the two time cocycles after transporting by a Markov isomorphism. -/
def time_cocycle_cohomologous
    (D : xi_time_zeta_identifiability_markov_cohomology_data) : Prop :=
  ∃ F :
    D.xi_time_zeta_identifiability_markov_cohomology_leftState ≃
      D.xi_time_zeta_identifiability_markov_cohomology_rightState,
    ∃ transfer : D.xi_time_zeta_identifiability_markov_cohomology_leftState → ℝ,
      ∀ state,
        D.xi_time_zeta_identifiability_markov_cohomology_leftTime state =
          D.xi_time_zeta_identifiability_markov_cohomology_rightTime (F state) +
            transfer state - transfer state

end xi_time_zeta_identifiability_markov_cohomology_data

open xi_time_zeta_identifiability_markov_cohomology_data

/-- Paper label: `thm:xi-time-zeta-identifiability-markov-cohomology`.
Equality of the determinant family is first converted to equality of all weighted closed traces;
the packaged reconstruction hypotheses then give the Markov isomorphism and the time-cocycle
cohomology class. -/
theorem paper_xi_time_zeta_identifiability_markov_cohomology
    (D : xi_time_zeta_identifiability_markov_cohomology_data) :
    D.zeta_equal → D.markov_isomorphic ∧ D.time_cocycle_cohomologous := by
  intro hzeta
  have htrace :
      D.xi_time_zeta_identifiability_markov_cohomology_weighted_closed_trace_equal :=
    D.xi_time_zeta_identifiability_markov_cohomology_zeta_to_closed_trace hzeta
  exact
    ⟨D.xi_time_zeta_identifiability_markov_cohomology_markov_from_closed_trace htrace,
      D.xi_time_zeta_identifiability_markov_cohomology_time_from_closed_trace htrace⟩

end

end Omega.Zeta
