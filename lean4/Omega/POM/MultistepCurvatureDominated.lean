import Mathlib.Tactic

namespace Omega.POM

/-- Concrete inverse-system maps for the multi-step curvature domination audit. -/
structure pom_multistep_curvature_dominated_system where
  pom_multistep_curvature_dominated_tau : ℕ → ℕ → ℕ → ℕ
  pom_multistep_curvature_dominated_pi : ℕ → ℕ → ℕ → ℕ
  pom_multistep_curvature_dominated_Fold : ℕ → ℕ → ℕ
  pom_multistep_curvature_dominated_curvature : ℕ → ℕ

/-- Identity law for the target transition maps. -/
def pom_multistep_curvature_dominated_tau_identity
    (S : pom_multistep_curvature_dominated_system) : Prop :=
  ∀ k x, S.pom_multistep_curvature_dominated_tau k k x = x

/-- Identity law for the inverse-system projection maps. -/
def pom_multistep_curvature_dominated_pi_identity
    (S : pom_multistep_curvature_dominated_system) : Prop :=
  ∀ k x, S.pom_multistep_curvature_dominated_pi k k x = x

/-- Functoriality of the target transition maps. -/
def pom_multistep_curvature_dominated_tau_comp
    (S : pom_multistep_curvature_dominated_system) : Prop :=
  ∀ a b c x, a ≤ b → b ≤ c →
    S.pom_multistep_curvature_dominated_tau b c
        (S.pom_multistep_curvature_dominated_tau a b x) =
      S.pom_multistep_curvature_dominated_tau a c x

/-- Functoriality of the inverse-system projection maps. -/
def pom_multistep_curvature_dominated_pi_comp
    (S : pom_multistep_curvature_dominated_system) : Prop :=
  ∀ a b c x, a ≤ b → b ≤ c →
    S.pom_multistep_curvature_dominated_pi b c
        (S.pom_multistep_curvature_dominated_pi a b x) =
      S.pom_multistep_curvature_dominated_pi a c x

/-- A vanishing one-step curvature indicator makes the corresponding square commute. -/
def pom_multistep_curvature_dominated_one_step
    (S : pom_multistep_curvature_dominated_system) : Prop :=
  ∀ k x, S.pom_multistep_curvature_dominated_curvature k = 0 →
    S.pom_multistep_curvature_dominated_Fold (k + 1)
        (S.pom_multistep_curvature_dominated_pi k (k + 1) x) =
      S.pom_multistep_curvature_dominated_tau k (k + 1)
        (S.pom_multistep_curvature_dominated_Fold k x)

/-- Paper-facing concrete statement: zero one-step curvature on every edge of `m..n` forces
the composed square from level `m` to level `n` to commute. -/
def pom_multistep_curvature_dominated_statement : Prop :=
  ∀ (S : pom_multistep_curvature_dominated_system) (m n : ℕ), m ≤ n →
    pom_multistep_curvature_dominated_pi_identity S →
    pom_multistep_curvature_dominated_tau_identity S →
    pom_multistep_curvature_dominated_pi_comp S →
    pom_multistep_curvature_dominated_tau_comp S →
    pom_multistep_curvature_dominated_one_step S →
    (∀ k, m ≤ k → k < n → S.pom_multistep_curvature_dominated_curvature k = 0) →
      ∀ x,
        S.pom_multistep_curvature_dominated_Fold n
            (S.pom_multistep_curvature_dominated_pi m n x) =
          S.pom_multistep_curvature_dominated_tau m n
            (S.pom_multistep_curvature_dominated_Fold m x)

/-- Paper label: `lem:pom-multistep-curvature-dominated`. -/
theorem paper_pom_multistep_curvature_dominated :
    pom_multistep_curvature_dominated_statement := by
  intro S m n hmn hπid hτid hπcomp hτcomp hstep
  refine Nat.le_induction (m := m)
    (P := fun n _ =>
      (∀ k, m ≤ k → k < n → S.pom_multistep_curvature_dominated_curvature k = 0) →
        ∀ x,
          S.pom_multistep_curvature_dominated_Fold n
              (S.pom_multistep_curvature_dominated_pi m n x) =
            S.pom_multistep_curvature_dominated_tau m n
              (S.pom_multistep_curvature_dominated_Fold m x)) ?base ?step n hmn
  · intro _ x
    simp [hπid m x, hτid m (S.pom_multistep_curvature_dominated_Fold m x)]
  · intro n hmn ih hzero x
    have hzero_prev :
        ∀ k, m ≤ k → k < n → S.pom_multistep_curvature_dominated_curvature k = 0 := by
      intro k hmk hkn
      exact hzero k hmk (Nat.lt_trans hkn (Nat.lt_succ_self n))
    calc
      S.pom_multistep_curvature_dominated_Fold (n + 1)
          (S.pom_multistep_curvature_dominated_pi m (n + 1) x)
          =
        S.pom_multistep_curvature_dominated_Fold (n + 1)
          (S.pom_multistep_curvature_dominated_pi n (n + 1)
            (S.pom_multistep_curvature_dominated_pi m n x)) := by
            rw [hπcomp m n (n + 1) x hmn (Nat.le_succ n)]
      _ =
        S.pom_multistep_curvature_dominated_tau n (n + 1)
          (S.pom_multistep_curvature_dominated_Fold n
            (S.pom_multistep_curvature_dominated_pi m n x)) := by
            exact hstep n (S.pom_multistep_curvature_dominated_pi m n x)
              (hzero n hmn (Nat.lt_succ_self n))
      _ =
        S.pom_multistep_curvature_dominated_tau n (n + 1)
          (S.pom_multistep_curvature_dominated_tau m n
            (S.pom_multistep_curvature_dominated_Fold m x)) := by
            rw [ih hzero_prev x]
      _ =
        S.pom_multistep_curvature_dominated_tau m (n + 1)
          (S.pom_multistep_curvature_dominated_Fold m x) := by
            exact hτcomp m n (n + 1)
              (S.pom_multistep_curvature_dominated_Fold m x) hmn (Nat.le_succ n)

end Omega.POM
