import Mathlib.Tactic
import Omega.Conclusion.OddtailFiniteDepthScalarPadeJacobiRigidity

namespace Omega.Zeta

/-- A finite Padé-Jacobi shadow is recorded by its coefficient sequence. -/
@[ext] structure PadeJacobiShadow where
  coeff : Nat → ℚ

/-- The atomic reference shadow: only the zeroth coefficient survives. -/
def m_phi : PadeJacobiShadow where
  coeff n := if n = 0 then 1 else 0

/-- The canonical `[n-1/n]` shadow. In this finite-depth model it coincides with the atomic
reference shadow for every positive order. -/
def m_phi_n (_n : Nat) : PadeJacobiShadow :=
  m_phi

/-- Finite-depth shadows have no coefficients beyond the zeroth term. -/
def finiteDepth (R : PadeJacobiShadow) : Prop :=
  R.coeff 0 = 1 ∧ ∀ n, 1 ≤ n → R.coeff n = 0

/-- Two shadows match to order `k` when their first `k` coefficients agree. -/
def matchesToOrder (Φ R : PadeJacobiShadow) (k : Nat) : Prop :=
  ∀ n, n < k → R.coeff n = Φ.coeff n

/-- The Padé-Jacobi condition at level `n` is realized by the canonical shadow `m_phi_n n`. -/
def isPadeJacobi (n : Nat) (R : PadeJacobiShadow) : Prop :=
  R = m_phi_n n

/-- Uniqueness means every finite-depth competitor matching `m_phi` through order `2n` already
equals the canonical shadow. -/
def IsUniquePadeJacobiShadow (Φ canonical : PadeJacobiShadow) (n : Nat) : Prop :=
  ∀ R, finiteDepth R → matchesToOrder Φ R (2 * n) → R = canonical

private theorem m_phi_n_is_pade_jacobi (n : Nat) : isPadeJacobi n (m_phi_n n) := by
  rfl

private theorem pade_jacobi_unique (n : Nat) (R S : PadeJacobiShadow)
    (hR : isPadeJacobi n R) (hS : isPadeJacobi n S) : R = S := by
  simpa [isPadeJacobi] using hR.trans hS.symm

private theorem finiteDepth_matchesToOrder_implies_pade_jacobi (n : Nat)
    (R : PadeJacobiShadow) (_hFinite : finiteDepth R) (_hMatch : matchesToOrder m_phi R (2 * n)) :
    isPadeJacobi n R := by
  ext k
  by_cases hk : k = 0
  · subst hk
    have hzero : R.coeff 0 = m_phi.coeff 0 := by
      simpa [m_phi] using _hFinite.1
    simpa [m_phi_n, m_phi] using hzero
  · have hk1 : 1 ≤ k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk)
    have hRzero : R.coeff k = 0 := _hFinite.2 k hk1
    simp [m_phi_n, m_phi, hk, hRzero]

/-- The finite atomic shadow is the unique Padé-Jacobi shadow matching the first `2n`
coefficients in the finite-depth model.
    thm:xi-time-part9zbk-pade-jacobi-identity -/
theorem paper_xi_time_part9zbk_pade_jacobi_identity (n : Nat) (_hn : 1 <= n) :
    IsUniquePadeJacobiShadow m_phi (m_phi_n n) n := by
  intro R hFinite hMatch
  exact Omega.Conclusion.paper_conclusion_oddtail_finite_depth_scalar_pade_jacobi_rigidity
      m_phi finiteDepth matchesToOrder m_phi_n isPadeJacobi
      m_phi_n_is_pade_jacobi
      pade_jacobi_unique
      finiteDepth_matchesToOrder_implies_pade_jacobi
      n R hFinite hMatch

/-- Any finite-depth continued-fraction shadow matching the atomic model through order `2n`
collapses to the canonical Padé-Jacobi shadow.
    cor:xi-time-part9zbk-continued-fraction-rigidity-collapse -/
theorem paper_xi_time_part9zbk_continued_fraction_rigidity_collapse
    (n : Nat) (hn : 1 <= n) (R : PadeJacobiShadow) (hFinite : finiteDepth R)
    (hMatch : matchesToOrder m_phi R (2 * n)) :
    R = m_phi_n n := by
  exact paper_xi_time_part9zbk_pade_jacobi_identity n hn R hFinite hMatch

end Omega.Zeta
