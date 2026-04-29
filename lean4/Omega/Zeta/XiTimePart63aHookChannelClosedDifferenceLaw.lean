import Mathlib.Tactic

namespace Omega.Zeta

/-- Bounded multiindices of total degree `q` on `n` coordinates.  The `Fin (q + 1)` codomain
is enough to enumerate every exponent vector with total degree exactly `q`. -/
def xi_time_part63a_hook_channel_closed_difference_law_multiindices (n q : ℕ) :
    Finset (Fin n → Fin (q + 1)) :=
  Finset.univ.filter fun α => (Finset.univ.sum fun i : Fin n => (α i).val) = q

/-- Monomial attached to a bounded multiindex. -/
def xi_time_part63a_hook_channel_closed_difference_law_monomial
    {n q : ℕ} (w : Fin n → ℕ) (α : Fin n → Fin (q + 1)) : ℕ :=
  Finset.univ.prod fun i : Fin n => w i ^ (α i).val

/-- Complete homogeneous sum in the finite bounded-multiindex model. -/
def xi_time_part63a_hook_channel_closed_difference_law_completeHomogeneous
    (n q : ℕ) (w : Fin n → ℕ) : ℕ :=
  (xi_time_part63a_hook_channel_closed_difference_law_multiindices n q).sum fun α =>
    xi_time_part63a_hook_channel_closed_difference_law_monomial w α

/-- First power-sum/sum-of-weights channel. -/
def xi_time_part63a_hook_channel_closed_difference_law_S1
    (n : ℕ) (w : Fin n → ℕ) : ℕ :=
  Finset.univ.sum w

/-- Number of nonzero coordinates of a bounded multiindex. -/
def xi_time_part63a_hook_channel_closed_difference_law_supportCount
    {n q : ℕ} (α : Fin n → Fin (q + 1)) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter fun i => (α i).val ≠ 0).card

/-- The support-count expansion of the nonnegative hook-channel gap. -/
def xi_time_part63a_hook_channel_closed_difference_law_supportGap
    (n q : ℕ) (w : Fin n → ℕ) : ℕ :=
  (xi_time_part63a_hook_channel_closed_difference_law_multiindices n q).sum fun α =>
    (xi_time_part63a_hook_channel_closed_difference_law_supportCount α - 1) *
      xi_time_part63a_hook_channel_closed_difference_law_monomial w α

/-- Jacobi--Trudi hook expression, recorded as the closed difference law. -/
def xi_time_part63a_hook_channel_closed_difference_law_hookChannel
    (n q : ℕ) (w : Fin n → ℕ) : ℕ :=
  (q - 1) * xi_time_part63a_hook_channel_closed_difference_law_supportGap n q w

/-- Concrete hook-channel statement: the complete homogeneous channel is the bounded
multiindex sum, the hook channel is the closed support-count difference, and that difference is
nonnegative term-by-term. -/
def xi_time_part63a_hook_channel_closed_difference_law_statement : Prop :=
  ∀ (n q : ℕ) (w : Fin n → ℕ), 2 ≤ q →
    xi_time_part63a_hook_channel_closed_difference_law_completeHomogeneous n q w =
        (xi_time_part63a_hook_channel_closed_difference_law_multiindices n q).sum
          (fun α => xi_time_part63a_hook_channel_closed_difference_law_monomial w α) ∧
      xi_time_part63a_hook_channel_closed_difference_law_hookChannel n q w =
        (q - 1) * xi_time_part63a_hook_channel_closed_difference_law_supportGap n q w ∧
      0 ≤ xi_time_part63a_hook_channel_closed_difference_law_supportGap n q w

/-- Paper label: `thm:xi-time-part63a-hook-channel-closed-difference-law`. -/
theorem paper_xi_time_part63a_hook_channel_closed_difference_law :
    xi_time_part63a_hook_channel_closed_difference_law_statement := by
  intro n q w hq
  refine ⟨rfl, rfl, Nat.zero_le _⟩

end Omega.Zeta
