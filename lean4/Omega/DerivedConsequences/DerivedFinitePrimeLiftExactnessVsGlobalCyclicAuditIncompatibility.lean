import Mathlib.Data.Finite.Defs
import Mathlib.Tactic
import Omega.Zeta.DerivedMinimalCyclicAuditAxisZhatPrimeUnlocking
import Omega.Zeta.LocalizedFinitePrimeAuditCylinderFactorization

namespace Omega.DerivedConsequences

open Omega.Zeta

noncomputable section

/-- Paper label: `thm:derived-finite-prime-lift-exactness-vs-global-cyclic-audit-incompatibility`.
Finite-prime exactness says any audit constant on the fibers of one fixed truncation factors
through the corresponding finite quotient. The global cyclic audit register still surjects onto
its `\hat{\mathbf Z}` model, so such a factorization is incompatible with any surjective audit
into an infinite `\hat{\mathbf Z}`-type target. -/
theorem paper_derived_finite_prime_lift_exactness_vs_global_cyclic_audit_incompatibility
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p n m : ι → ℕ)
    (hp : ∀ i, 0 < p i)
    (D : DerivedMinimalCyclicAuditAxisZhatPrimeUnlockingData)
    [Infinite D.ZhatModel] :
    (∀ {A : Type*} (F : AuditDomain p n m → A),
      (∀ x y, auditTruncation p n m x = auditTruncation p n m y → F x = F y) →
        ∃ Fbar : AuditQuotient p n → A, F = Fbar ∘ auditTruncation p n m) ∧
    Function.Surjective D.registerToZhat ∧
    (∀ G : AuditDomain p n m → D.Register,
      (∀ x y, auditTruncation p n m x = auditTruncation p n m y → G x = G y) →
        Function.Surjective G → False) := by
  have haxis := paper_derived_minimal_cyclic_audit_axis_zhat_prime_unlocking D
  refine ⟨?_, ?_, ?_⟩
  · intro A F hF
    exact paper_xi_localized_finite_prime_audit_cylinder_factorization p n m F hF
  · exact Function.RightInverse.surjective D.zhat_right_inv
  · intro G hG hsurjG
    rcases paper_xi_localized_finite_prime_audit_cylinder_factorization p n m G hG with
      ⟨Gbar, hGbar⟩
    have hsurjZhat :
        Function.Surjective (fun q : AuditQuotient p n => D.registerToZhat (Gbar q)) := by
      intro z
      rcases (Function.RightInverse.surjective D.zhat_right_inv) z with ⟨r, hr⟩
      rcases hsurjG r with ⟨x, hx⟩
      have hxbar : Gbar (auditTruncation p n m x) = G x := by
        exact (congrFun hGbar x).symm
      refine ⟨auditTruncation p n m x, ?_⟩
      calc
        D.registerToZhat (Gbar (auditTruncation p n m x))
            = D.registerToZhat (G x) := congrArg D.registerToZhat hxbar
        _ = z := by simpa [hx] using hr
    let _ : Finite ι := Finite.of_fintype ι
    let _ : ∀ i : ι, NeZero (p i ^ n i) := fun i => ⟨Nat.ne_of_gt (pow_pos (hp i) _)⟩
    let _ : ∀ i : ι, Finite (ZMod (p i ^ n i)) := fun i => Finite.of_fintype (ZMod (p i ^ n i))
    let _ : Finite (AuditQuotient p n) := by
      dsimp [AuditQuotient]
      infer_instance
    let _ : Finite D.ZhatModel :=
      Finite.of_surjective (fun q : AuditQuotient p n => D.registerToZhat (Gbar q)) hsurjZhat
    exact not_finite D.ZhatModel

end

end Omega.DerivedConsequences
