import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Zeta.DephysicalizedEpsSoundDominatesTv

namespace Omega.Zeta

/-- A feasible certificate budget for two Boolean readouts is witnessed by a finite bad-event set
outside of which the readouts agree. -/
def dephys_budget_distance_dominates_tv_rewrite {State : Type*} [Fintype State]
    (x y : State → Bool) (ε : ℝ) : Prop :=
  ∃ bad : Finset State,
    (∀ ω, ω ∉ bad → x ω = y ω) ∧
      (bad.card : ℝ) / Fintype.card State ≤ ε

lemma dephys_budget_distance_dominates_tv_rewrite_compose {State : Type*} [Fintype State]
    [Nonempty State] [DecidableEq State] {x y z : State → Bool} {ε δ : ℝ}
    (hxy : dephys_budget_distance_dominates_tv_rewrite x y ε)
    (hyz : dephys_budget_distance_dominates_tv_rewrite y z δ) :
    dephys_budget_distance_dominates_tv_rewrite x z (ε + δ) := by
  rcases hxy with ⟨s, hsagree, hsbound⟩
  rcases hyz with ⟨t, htagree, htbound⟩
  refine ⟨s ∪ t, ?_, ?_⟩
  · intro ω hω
    have hsω : ω ∉ s := by
      intro hs
      exact hω (Finset.mem_union.mpr (Or.inl hs))
    have htω : ω ∉ t := by
      intro ht
      exact hω (Finset.mem_union.mpr (Or.inr ht))
    rw [hsagree ω hsω, htagree ω htω]
  · have hcard_pos : 0 < (Fintype.card State : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty State›
    calc
      ((s ∪ t).card : ℝ) / Fintype.card State ≤ ((s.card + t.card : ℕ) : ℝ) / Fintype.card State := by
        exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_union_le s t) hcard_pos.le
      _ = (s.card : ℝ) / Fintype.card State + (t.card : ℝ) / Fintype.card State := by
        rw [Nat.cast_add, add_div]
      _ ≤ ε + δ := add_le_add hsbound htbound

/-- Finite certificate chains and their total budgets. -/
inductive dephys_budget_distance_dominates_tv_certificateChain {State : Type*} [Fintype State] :
    (State → Bool) → (State → Bool) → ℝ → Prop
  | direct {x y : State → Bool} {ε : ℝ} :
      dephys_budget_distance_dominates_tv_rewrite x y ε →
        dephys_budget_distance_dominates_tv_certificateChain x y ε
  | comp {x y z : State → Bool} {ε δ : ℝ} :
      dephys_budget_distance_dominates_tv_certificateChain x y ε →
        dephys_budget_distance_dominates_tv_certificateChain y z δ →
          dephys_budget_distance_dominates_tv_certificateChain x z (ε + δ)

/-- The feasible budget set consists of all total budgets of finite certificate chains. -/
def dephys_budget_distance_dominates_tv_budgetSet {State : Type*} [Fintype State]
    (x y : State → Bool) : Set ℝ :=
  {ε | dephys_budget_distance_dominates_tv_certificateChain x y ε}

/-- Minimal feasible certificate budget, when at least one finite certificate chain exists. -/
noncomputable def dephys_budget_distance_dominates_tv_distance {State : Type*} [Fintype State]
    (x y : State → Bool) : ℝ :=
  by
    classical
    exact
      if h : (dephys_budget_distance_dominates_tv_budgetSet x y).Nonempty then
        sInf (dephys_budget_distance_dominates_tv_budgetSet x y)
      else
        0

lemma dephys_budget_distance_dominates_tv_chain_rewrite {State : Type*} [Fintype State]
    [Nonempty State] [DecidableEq State] {x y : State → Bool} {ε : ℝ}
    (h : dephys_budget_distance_dominates_tv_certificateChain x y ε) :
    dephys_budget_distance_dominates_tv_rewrite x y ε := by
  induction h with
  | direct hrewrite =>
      exact hrewrite
  | comp hxy hyz ihxy ihyz =>
      exact dephys_budget_distance_dominates_tv_rewrite_compose ihxy ihyz

lemma dephys_budget_distance_dominates_tv_bound_of_chain {State : Type*} [Fintype State]
    [Nonempty State] [DecidableEq State] {x y : State → Bool} {ε : ℝ}
    (h : dephys_budget_distance_dominates_tv_certificateChain x y ε) :
    dephys_eps_sound_dominates_tv_totalVariation x y ≤ ε := by
  rcases dephys_budget_distance_dominates_tv_chain_rewrite h with ⟨bad, hagree, hbad⟩
  exact paper_dephys_eps_sound_dominates_tv x y bad ε hagree hbad

/-- The total variation is bounded by every feasible certificate-chain budget, hence also by the
infimum of all such budgets whenever that budget set is nonempty.
    cor:dephys-budget-distance-dominates-tv -/
def dephys_budget_distance_dominates_tv_statement : Prop :=
  ∀ {State : Type*} [Fintype State] [Nonempty State] [DecidableEq State] (x y : State → Bool),
    (dephys_budget_distance_dominates_tv_budgetSet x y).Nonempty →
      dephys_eps_sound_dominates_tv_totalVariation x y ≤
          dephys_budget_distance_dominates_tv_distance x y ∧
        ∀ ε, dephys_budget_distance_dominates_tv_certificateChain x y ε →
          dephys_eps_sound_dominates_tv_totalVariation x y ≤ ε

theorem paper_dephys_budget_distance_dominates_tv :
    dephys_budget_distance_dominates_tv_statement := by
  classical
  intro State _ _ _ x y hnonempty
  refine ⟨?_, ?_⟩
  · simp [dephys_budget_distance_dominates_tv_distance, dif_pos hnonempty]
    exact le_csInf hnonempty (fun ε hε =>
      dephys_budget_distance_dominates_tv_bound_of_chain hε)
  · intro ε hε
    exact dephys_budget_distance_dominates_tv_bound_of_chain hε

end Omega.Zeta
