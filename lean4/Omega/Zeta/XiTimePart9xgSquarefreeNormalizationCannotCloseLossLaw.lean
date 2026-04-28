import Mathlib.Tactic
import Omega.Zeta.KilloKernelSizeGeneralModulus

namespace Omega.Zeta

/-- Concrete prime-power input for the squarefree-normalization loss obstruction. -/
structure xi_time_part9xg_squarefree_normalization_cannot_close_loss_law_data where
  p : ℕ
  hp : 2 ≤ p

namespace xi_time_part9xg_squarefree_normalization_cannot_close_loss_law_data

/-- Squarefree normalization remembers whether the prime is present but not its exponent. -/
def xi_time_part9xg_squarefree_normalization_cannot_close_loss_law_squarefreeExponent
    (_D : xi_time_part9xg_squarefree_normalization_cannot_close_loss_law_data)
    (e : ℕ) : ℕ :=
  if e = 0 then 0 else 1

/-- Kernel size for the one-coordinate Smith factor `p^e` modulo `p^2`. -/
def xi_time_part9xg_squarefree_normalization_cannot_close_loss_law_kernelSize
    (D : xi_time_part9xg_squarefree_normalization_cannot_close_loss_law_data)
    (e : ℕ) : ℕ :=
  killoKernelSizeGeneralModulus 1 1 (D.p ^ 2) [D.p ^ e]

/-- The kernel-size formula reduces the one-coordinate prime-power factor to `p^min(e,2)`. -/
def xi_time_part9xg_squarefree_normalization_cannot_close_loss_law_primePowerFormula
    (D : xi_time_part9xg_squarefree_normalization_cannot_close_loss_law_data) : Prop :=
  ∀ e,
    D.xi_time_part9xg_squarefree_normalization_cannot_close_loss_law_kernelSize e =
      D.p ^ min e 2

/-- The squarefree normalization cannot recover multiplicity-sensitive Smith loss. -/
def xi_time_part9xg_squarefree_normalization_cannot_close_loss_law_nonrecoverable
    (D : xi_time_part9xg_squarefree_normalization_cannot_close_loss_law_data) : Prop :=
  ∃ e₁ e₂,
    D.xi_time_part9xg_squarefree_normalization_cannot_close_loss_law_squarefreeExponent e₁ =
      D.xi_time_part9xg_squarefree_normalization_cannot_close_loss_law_squarefreeExponent e₂ ∧
    D.xi_time_part9xg_squarefree_normalization_cannot_close_loss_law_kernelSize e₁ ≠
      D.xi_time_part9xg_squarefree_normalization_cannot_close_loss_law_kernelSize e₂

/-- Paper-facing statement: prime-power expansion, the two decisive exponent samples, and the
non-recoverability of Smith loss from squarefree data. -/
def xi_time_part9xg_squarefree_normalization_cannot_close_loss_law_clauses
    (D : xi_time_part9xg_squarefree_normalization_cannot_close_loss_law_data) : Prop :=
  D.xi_time_part9xg_squarefree_normalization_cannot_close_loss_law_primePowerFormula ∧
    D.xi_time_part9xg_squarefree_normalization_cannot_close_loss_law_squarefreeExponent 1 =
      D.xi_time_part9xg_squarefree_normalization_cannot_close_loss_law_squarefreeExponent 2 ∧
    D.xi_time_part9xg_squarefree_normalization_cannot_close_loss_law_kernelSize 1 = D.p ∧
    D.xi_time_part9xg_squarefree_normalization_cannot_close_loss_law_kernelSize 2 =
      D.p ^ 2 ∧
    D.xi_time_part9xg_squarefree_normalization_cannot_close_loss_law_nonrecoverable

end xi_time_part9xg_squarefree_normalization_cannot_close_loss_law_data

/-- Root-level paper statement name used by the target theorem. -/
def xi_time_part9xg_squarefree_normalization_cannot_close_loss_law_statement
    (D : xi_time_part9xg_squarefree_normalization_cannot_close_loss_law_data) : Prop :=
  D.xi_time_part9xg_squarefree_normalization_cannot_close_loss_law_clauses

/-- Paper label: `cor:xi-time-part9xg-squarefree-normalization-cannot-close-loss-law`. -/
theorem paper_xi_time_part9xg_squarefree_normalization_cannot_close_loss_law
    (D : xi_time_part9xg_squarefree_normalization_cannot_close_loss_law_data) :
    xi_time_part9xg_squarefree_normalization_cannot_close_loss_law_statement D := by
  have hformula :
      D.xi_time_part9xg_squarefree_normalization_cannot_close_loss_law_primePowerFormula := by
    intro e
    have hpow :
        (D.p ^ 2).gcd (D.p ^ e) = D.p ^ min e 2 := by
      by_cases he : e ≤ 2
      · rw [Nat.min_eq_left he, Nat.gcd_eq_right (pow_dvd_pow D.p he)]
      · have h2e : 2 ≤ e := Nat.le_of_not_ge he
        rw [Nat.min_eq_right h2e, Nat.gcd_eq_left (pow_dvd_pow D.p h2e)]
    simp [
      xi_time_part9xg_squarefree_normalization_cannot_close_loss_law_data.xi_time_part9xg_squarefree_normalization_cannot_close_loss_law_kernelSize,
      killoKernelSizeGeneralModulus, hpow]
  have hsquarefree :
      D.xi_time_part9xg_squarefree_normalization_cannot_close_loss_law_squarefreeExponent 1 =
        D.xi_time_part9xg_squarefree_normalization_cannot_close_loss_law_squarefreeExponent 2 := by
    simp [
      xi_time_part9xg_squarefree_normalization_cannot_close_loss_law_data.xi_time_part9xg_squarefree_normalization_cannot_close_loss_law_squarefreeExponent]
  have hkernel_one :
      D.xi_time_part9xg_squarefree_normalization_cannot_close_loss_law_kernelSize 1 = D.p := by
    simpa using hformula 1
  have hkernel_two :
      D.xi_time_part9xg_squarefree_normalization_cannot_close_loss_law_kernelSize 2 =
        D.p ^ 2 := by
    simpa using hformula 2
  have hneq :
      D.xi_time_part9xg_squarefree_normalization_cannot_close_loss_law_kernelSize 1 ≠
        D.xi_time_part9xg_squarefree_normalization_cannot_close_loss_law_kernelSize 2 := by
    rw [hkernel_one, hkernel_two]
    exact ne_of_lt (by nlinarith [D.hp])
  refine ⟨hformula, hsquarefree, hkernel_one, hkernel_two, ?_⟩
  exact ⟨1, 2, hsquarefree, hneq⟩

end Omega.Zeta
