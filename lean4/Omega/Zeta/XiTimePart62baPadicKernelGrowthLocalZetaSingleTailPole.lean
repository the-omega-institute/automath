import Mathlib.Tactic
import Omega.Zeta.XiSmithLossMinimalBranchRegister

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part62ba-padic-kernel-growth-local-zeta-single-tail-pole`. -/
theorem paper_xi_time_part62ba_padic_kernel_growth_local_zeta_single_tail_pole
    (p n m E : Nat) (smithExponents : Multiset Nat)
    (hE : forall v, v ∈ smithExponents -> v <= E) :
    (forall k : Nat, E <= k ->
      smithFiberCardinality p n m k smithExponents =
        smithFiberCardinality p n m E smithExponents * (p ^ (n - m)) ^ (k - E)) ∧
    (forall k : Nat, E <= k ->
      smithFiberCardinality p n m (k + 1) smithExponents =
        smithFiberCardinality p n m k smithExponents * p ^ (n - m)) := by
  have hEntropyE : smithEntropy smithExponents E = smithExponents.sum :=
    smithEntropy_eq_sum_of_all_le smithExponents E hE
  refine ⟨?_, ?_⟩
  · intro k hk
    have hEntropyk : smithEntropy smithExponents k = smithExponents.sum :=
      smithEntropy_eq_sum_of_all_le smithExponents k
        (fun v hv => le_trans (hE v hv) hk)
    unfold smithFiberCardinality
    rw [hEntropyk, hEntropyE]
    have hmul : k * (n - m) = E * (n - m) + (n - m) * (k - E) := by
      calc
        k * (n - m) = ((k - E) + E) * (n - m) := by rw [Nat.sub_add_cancel hk]
        _ = (k - E) * (n - m) + E * (n - m) := by rw [Nat.add_mul]
        _ = E * (n - m) + (n - m) * (k - E) := by
          rw [Nat.add_comm, Nat.mul_comm (k - E) (n - m)]
    have hexp :
        k * (n - m) + smithExponents.sum =
          E * (n - m) + smithExponents.sum + (n - m) * (k - E) := by
      rw [hmul]
      omega
    rw [hexp, Nat.pow_add, Nat.pow_mul]
  · intro k hk
    have hEntropyk : smithEntropy smithExponents k = smithExponents.sum :=
      smithEntropy_eq_sum_of_all_le smithExponents k
        (fun v hv => le_trans (hE v hv) hk)
    have hEntropysucc : smithEntropy smithExponents (k + 1) = smithExponents.sum :=
      smithEntropy_eq_sum_of_all_le smithExponents (k + 1)
        (fun v hv => le_trans (hE v hv) (Nat.le_succ_of_le hk))
    unfold smithFiberCardinality
    rw [hEntropysucc, hEntropyk]
    have hexp :
        (k + 1) * (n - m) + smithExponents.sum =
          k * (n - m) + smithExponents.sum + (n - m) := by
      rw [Nat.succ_mul]
      omega
    rw [hexp, Nat.pow_add]

end Omega.Zeta
