import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Tactic
import Omega.SyncKernelWeighted.WittDworkCongruence
import Omega.SyncKernelWeighted.WittUnitRootLimit

namespace Omega.SyncKernelWeighted

open Polynomial

/-- Paper label: `thm:witt-dwork-zp-integrality`. The prime-power Dwork congruence gives
coefficientwise `p^k`-divisibility of the Frobenius defect, and at Frobenius-fixed points the
evaluated prime-power tower is `p`-adically Cauchy. -/
theorem paper_witt_dwork_zp_integrality
    (p : ℕ) (hp : Nat.Prime p) (a : ℕ → Polynomial ℤ)
    (hcongr :
      ∀ k : ℕ, ∃ q : Polynomial ℤ,
        ((p ^ k : ℤ)) • q = a (p ^ k) - Polynomial.expand ℤ p (a (p ^ (k - 1))))
    (u : ℤ) (hu : u ^ p = u) :
    (∀ k j,
      ((p ^ k : ℤ) ∣ (a (p ^ k) - Polynomial.expand ℤ p (a (p ^ (k - 1)))).coeff j)) ∧
      (∀ s r, s ≤ r → ((p ^ (s + 1) : ℤ) ∣ (a (p ^ r)).eval u - (a (p ^ s)).eval u)) := by
  refine ⟨?_, ?_⟩
  · intro k j
    rcases hcongr k with ⟨q, hq⟩
    exact paper_witt_dwork_congruence p k hp a q hq j
  · have hstep :
        ∀ v : ℤ, v ^ p = v → ∀ k, 1 ≤ k → ((p ^ k : ℤ) ∣ (a (p ^ k)).eval v - (a (p ^ (k - 1))).eval v) := by
      intro v hv k hk
      rcases hcongr k with ⟨q, hq⟩
      refine ⟨q.eval v, ?_⟩
      have heval := congrArg (fun f : Polynomial ℤ => f.eval v) hq
      calc
        (a (p ^ k)).eval v - (a (p ^ (k - 1))).eval v
            = (a (p ^ k) - Polynomial.expand ℤ p (a (p ^ (k - 1)))).eval v := by
                rw [Polynomial.eval_sub, Polynomial.expand_eval, hv]
        _ = (((p ^ k : ℤ) • q).eval v) := by
              simpa using heval.symm
        _ = (p ^ k : ℤ) * q.eval v := by
              simp [smul_eq_C_mul]
    simpa using paper_witt_unit_root_limit p hp (fun v k => (a (p ^ k)).eval v) hstep u hu

end Omega.SyncKernelWeighted
