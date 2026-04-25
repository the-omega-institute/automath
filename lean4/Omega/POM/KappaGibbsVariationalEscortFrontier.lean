import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- Finite probability simplex on a chapter-local state space. -/
def pom_kappa_gibbs_variational_escort_frontier_simplex
    {State : Type*} [Fintype State] (π : State → ℝ) : Prop :=
  (∀ x, 0 ≤ π x) ∧ ∑ x, π x = 1

/-- Finite KL divergence on a chapter-local state space. -/
def pom_kappa_gibbs_variational_escort_frontier_klDiv
    {State : Type*} [Fintype State] (π ρ : State → ℝ) : ℝ :=
  ∑ x, π x * Real.log (π x / ρ x)

/-- Finite expectation of the observable entering the escort tilt. -/
def pom_kappa_gibbs_variational_escort_frontier_kappa
    {State : Type*} [Fintype State] (π : State → ℝ) (observable : State → ℝ) : ℝ :=
  ∑ x, π x * observable x

/-- Escort partition function `Z(q) = Σ_x w(x) e^{q m(x)}`. -/
def pom_kappa_gibbs_variational_escort_frontier_partition
    {State : Type*} [Fintype State] (baseLaw : State → ℝ) (observable : State → ℝ) (q : ℝ) : ℝ :=
  ∑ x, baseLaw x * Real.exp (q * observable x)

/-- Finite escort optimizer `w_{m,q}`. -/
def pom_kappa_gibbs_variational_escort_frontier_escortLaw
    {State : Type*} [Fintype State] (baseLaw : State → ℝ) (observable : State → ℝ) (q : ℝ) :
    State → ℝ :=
  fun x =>
    baseLaw x * Real.exp (q * observable x) /
      pom_kappa_gibbs_variational_escort_frontier_partition baseLaw observable q

/-- Frontier value `F_m(q) = log Z(q)`. -/
def pom_kappa_gibbs_variational_escort_frontier_frontier
    {State : Type*} [Fintype State] (baseLaw : State → ℝ) (observable : State → ℝ) (q : ℝ) : ℝ :=
  Real.log (pom_kappa_gibbs_variational_escort_frontier_partition baseLaw observable q)

/-- Variational objective written in escort-frontier form. -/
def pom_kappa_gibbs_variational_escort_frontier_variationalObjective
    {State : Type*} [Fintype State]
    (baseLaw : State → ℝ) (observable : State → ℝ) (q : ℝ) (π : State → ℝ) : ℝ :=
  pom_kappa_gibbs_variational_escort_frontier_frontier baseLaw observable q -
    pom_kappa_gibbs_variational_escort_frontier_klDiv π
      (pom_kappa_gibbs_variational_escort_frontier_escortLaw baseLaw observable q)

/-- Concrete finite-state data for the escort frontier package. The input is the base law, the
observable, the tilt parameter, and the standard KL nonnegativity/equality facts for the resulting
escort law. -/
structure pom_kappa_gibbs_variational_escort_frontier_data where
  State : Type
  pom_kappa_gibbs_variational_escort_frontier_instFintype : Fintype State
  pom_kappa_gibbs_variational_escort_frontier_instNonempty : Nonempty State
  pom_kappa_gibbs_variational_escort_frontier_instDecidableEq : DecidableEq State
  pom_kappa_gibbs_variational_escort_frontier_baseLaw : State → ℝ
  pom_kappa_gibbs_variational_escort_frontier_observable : State → ℝ
  pom_kappa_gibbs_variational_escort_frontier_q : ℝ
  pom_kappa_gibbs_variational_escort_frontier_baseLaw_pos :
    ∀ x, 0 < pom_kappa_gibbs_variational_escort_frontier_baseLaw x
  pom_kappa_gibbs_variational_escort_frontier_baseLaw_simplex :
    pom_kappa_gibbs_variational_escort_frontier_simplex
      pom_kappa_gibbs_variational_escort_frontier_baseLaw
  pom_kappa_gibbs_variational_escort_frontier_escort_simplex :
    pom_kappa_gibbs_variational_escort_frontier_simplex
      (pom_kappa_gibbs_variational_escort_frontier_escortLaw
        pom_kappa_gibbs_variational_escort_frontier_baseLaw
        pom_kappa_gibbs_variational_escort_frontier_observable
        pom_kappa_gibbs_variational_escort_frontier_q)
  pom_kappa_gibbs_variational_escort_frontier_kl_nonneg :
    ∀ π,
      pom_kappa_gibbs_variational_escort_frontier_simplex π →
        0 ≤ pom_kappa_gibbs_variational_escort_frontier_klDiv π
          (pom_kappa_gibbs_variational_escort_frontier_escortLaw
            pom_kappa_gibbs_variational_escort_frontier_baseLaw
            pom_kappa_gibbs_variational_escort_frontier_observable
            pom_kappa_gibbs_variational_escort_frontier_q)
  pom_kappa_gibbs_variational_escort_frontier_kl_eq_zero_iff :
    ∀ π,
      pom_kappa_gibbs_variational_escort_frontier_simplex π →
        (pom_kappa_gibbs_variational_escort_frontier_klDiv π
            (pom_kappa_gibbs_variational_escort_frontier_escortLaw
              pom_kappa_gibbs_variational_escort_frontier_baseLaw
              pom_kappa_gibbs_variational_escort_frontier_observable
              pom_kappa_gibbs_variational_escort_frontier_q) = 0 ↔
          π =
            pom_kappa_gibbs_variational_escort_frontier_escortLaw
              pom_kappa_gibbs_variational_escort_frontier_baseLaw
              pom_kappa_gibbs_variational_escort_frontier_observable
              pom_kappa_gibbs_variational_escort_frontier_q)

namespace pom_kappa_gibbs_variational_escort_frontier_data

attribute [instance] pom_kappa_gibbs_variational_escort_frontier_instFintype
attribute [instance] pom_kappa_gibbs_variational_escort_frontier_instNonempty
attribute [instance] pom_kappa_gibbs_variational_escort_frontier_instDecidableEq

variable (D : pom_kappa_gibbs_variational_escort_frontier_data)

private lemma pom_kappa_gibbs_variational_escort_frontier_partition_pos :
    0 <
      pom_kappa_gibbs_variational_escort_frontier_partition
        D.pom_kappa_gibbs_variational_escort_frontier_baseLaw
        D.pom_kappa_gibbs_variational_escort_frontier_observable
        D.pom_kappa_gibbs_variational_escort_frontier_q := by
  classical
  obtain ⟨x₀⟩ := inferInstanceAs (Nonempty D.State)
  have hterm_pos :
      0 <
        D.pom_kappa_gibbs_variational_escort_frontier_baseLaw x₀ *
          Real.exp
            (D.pom_kappa_gibbs_variational_escort_frontier_q *
              D.pom_kappa_gibbs_variational_escort_frontier_observable x₀) := by
    exact mul_pos
      (D.pom_kappa_gibbs_variational_escort_frontier_baseLaw_pos x₀)
      (Real.exp_pos _)
  have hterm_le :
      D.pom_kappa_gibbs_variational_escort_frontier_baseLaw x₀ *
          Real.exp
            (D.pom_kappa_gibbs_variational_escort_frontier_q *
              D.pom_kappa_gibbs_variational_escort_frontier_observable x₀) ≤
        pom_kappa_gibbs_variational_escort_frontier_partition
          D.pom_kappa_gibbs_variational_escort_frontier_baseLaw
          D.pom_kappa_gibbs_variational_escort_frontier_observable
          D.pom_kappa_gibbs_variational_escort_frontier_q := by
    classical
    have hsingle :=
      Finset.single_le_sum
        (f := fun x : D.State =>
          D.pom_kappa_gibbs_variational_escort_frontier_baseLaw x *
            Real.exp
              (D.pom_kappa_gibbs_variational_escort_frontier_q *
                D.pom_kappa_gibbs_variational_escort_frontier_observable x))
        (fun x _ => mul_nonneg
          (le_of_lt (D.pom_kappa_gibbs_variational_escort_frontier_baseLaw_pos x))
          (le_of_lt (Real.exp_pos _)))
        (Finset.mem_univ x₀)
    simpa [pom_kappa_gibbs_variational_escort_frontier_partition] using hsingle
  exact lt_of_lt_of_le hterm_pos hterm_le

/-- Paper-facing statement for the finite-state escort frontier. -/
def pom_kappa_gibbs_variational_escort_frontier_holds : Prop :=
  (∀ π,
    pom_kappa_gibbs_variational_escort_frontier_simplex π →
      pom_kappa_gibbs_variational_escort_frontier_variationalObjective
          D.pom_kappa_gibbs_variational_escort_frontier_baseLaw
          D.pom_kappa_gibbs_variational_escort_frontier_observable
          D.pom_kappa_gibbs_variational_escort_frontier_q π =
        pom_kappa_gibbs_variational_escort_frontier_frontier
            D.pom_kappa_gibbs_variational_escort_frontier_baseLaw
            D.pom_kappa_gibbs_variational_escort_frontier_observable
            D.pom_kappa_gibbs_variational_escort_frontier_q -
          pom_kappa_gibbs_variational_escort_frontier_klDiv π
            (pom_kappa_gibbs_variational_escort_frontier_escortLaw
              D.pom_kappa_gibbs_variational_escort_frontier_baseLaw
              D.pom_kappa_gibbs_variational_escort_frontier_observable
              D.pom_kappa_gibbs_variational_escort_frontier_q)) ∧
    (∀ π,
      pom_kappa_gibbs_variational_escort_frontier_simplex π →
        pom_kappa_gibbs_variational_escort_frontier_variationalObjective
            D.pom_kappa_gibbs_variational_escort_frontier_baseLaw
            D.pom_kappa_gibbs_variational_escort_frontier_observable
            D.pom_kappa_gibbs_variational_escort_frontier_q π ≤
          pom_kappa_gibbs_variational_escort_frontier_frontier
            D.pom_kappa_gibbs_variational_escort_frontier_baseLaw
            D.pom_kappa_gibbs_variational_escort_frontier_observable
            D.pom_kappa_gibbs_variational_escort_frontier_q) ∧
    pom_kappa_gibbs_variational_escort_frontier_variationalObjective
        D.pom_kappa_gibbs_variational_escort_frontier_baseLaw
        D.pom_kappa_gibbs_variational_escort_frontier_observable
        D.pom_kappa_gibbs_variational_escort_frontier_q
        (pom_kappa_gibbs_variational_escort_frontier_escortLaw
          D.pom_kappa_gibbs_variational_escort_frontier_baseLaw
          D.pom_kappa_gibbs_variational_escort_frontier_observable
          D.pom_kappa_gibbs_variational_escort_frontier_q) =
      pom_kappa_gibbs_variational_escort_frontier_frontier
        D.pom_kappa_gibbs_variational_escort_frontier_baseLaw
        D.pom_kappa_gibbs_variational_escort_frontier_observable
        D.pom_kappa_gibbs_variational_escort_frontier_q ∧
    (∀ π,
      pom_kappa_gibbs_variational_escort_frontier_simplex π →
        pom_kappa_gibbs_variational_escort_frontier_variationalObjective
            D.pom_kappa_gibbs_variational_escort_frontier_baseLaw
            D.pom_kappa_gibbs_variational_escort_frontier_observable
            D.pom_kappa_gibbs_variational_escort_frontier_q π =
          pom_kappa_gibbs_variational_escort_frontier_frontier
            D.pom_kappa_gibbs_variational_escort_frontier_baseLaw
            D.pom_kappa_gibbs_variational_escort_frontier_observable
            D.pom_kappa_gibbs_variational_escort_frontier_q →
          π =
            pom_kappa_gibbs_variational_escort_frontier_escortLaw
              D.pom_kappa_gibbs_variational_escort_frontier_baseLaw
              D.pom_kappa_gibbs_variational_escort_frontier_observable
              D.pom_kappa_gibbs_variational_escort_frontier_q)

end pom_kappa_gibbs_variational_escort_frontier_data

open pom_kappa_gibbs_variational_escort_frontier_data

/-- Paper label: `thm:pom-kappa-gibbs-variational-escort-frontier`. For the finite tilted law
`w_{m,q}(x) ∝ w(x) e^{q m(x)}`, the objective `q E_π[m] - D_KL(π || w)` is exactly
`F_m(q) - D_KL(π || w_{m,q})`, so the escort optimizer attains the frontier and is the unique
maximizer. -/
theorem paper_pom_kappa_gibbs_variational_escort_frontier
    (D : pom_kappa_gibbs_variational_escort_frontier_data) :
    D.pom_kappa_gibbs_variational_escort_frontier_holds := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro π hπ
    rfl
  · intro π hπ
    unfold pom_kappa_gibbs_variational_escort_frontier_variationalObjective
    have hkl :=
      D.pom_kappa_gibbs_variational_escort_frontier_kl_nonneg π hπ
    linarith
  · have hiff :
        pom_kappa_gibbs_variational_escort_frontier_klDiv
            (pom_kappa_gibbs_variational_escort_frontier_escortLaw
              D.pom_kappa_gibbs_variational_escort_frontier_baseLaw
              D.pom_kappa_gibbs_variational_escort_frontier_observable
              D.pom_kappa_gibbs_variational_escort_frontier_q)
            (pom_kappa_gibbs_variational_escort_frontier_escortLaw
              D.pom_kappa_gibbs_variational_escort_frontier_baseLaw
              D.pom_kappa_gibbs_variational_escort_frontier_observable
              D.pom_kappa_gibbs_variational_escort_frontier_q) = 0 := by
      have hbase :=
        D.pom_kappa_gibbs_variational_escort_frontier_kl_eq_zero_iff
          (pom_kappa_gibbs_variational_escort_frontier_escortLaw
            D.pom_kappa_gibbs_variational_escort_frontier_baseLaw
            D.pom_kappa_gibbs_variational_escort_frontier_observable
            D.pom_kappa_gibbs_variational_escort_frontier_q)
          D.pom_kappa_gibbs_variational_escort_frontier_escort_simplex
      exact hbase.mpr rfl
    unfold pom_kappa_gibbs_variational_escort_frontier_variationalObjective
    simp [hiff]
  · intro π hπ hEq
    unfold pom_kappa_gibbs_variational_escort_frontier_variationalObjective at hEq
    have hkl_zero :
        pom_kappa_gibbs_variational_escort_frontier_klDiv π
          (pom_kappa_gibbs_variational_escort_frontier_escortLaw
            D.pom_kappa_gibbs_variational_escort_frontier_baseLaw
            D.pom_kappa_gibbs_variational_escort_frontier_observable
            D.pom_kappa_gibbs_variational_escort_frontier_q) = 0 := by
      linarith
    exact
      (D.pom_kappa_gibbs_variational_escort_frontier_kl_eq_zero_iff π hπ).mp hkl_zero

end

end Omega.POM
