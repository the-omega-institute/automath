import Mathlib.Data.Fintype.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

section ConcreteFactorization

variable {ι A : Type*} [Fintype ι] [DecidableEq ι]

/-- The higher-precision finite product. -/
abbrev AuditDomain (p n m : ι → ℕ) := ∀ i, ZMod (p i ^ (n i + m i))

/-- The finite cylinder quotient read at precision `n`. -/
abbrev AuditQuotient (p n : ι → ℕ) := ∀ i, ZMod (p i ^ n i)

/-- Coordinatewise truncation from precision `n_i + m_i` to precision `n_i`. -/
noncomputable def auditTruncation (p n m : ι → ℕ) : AuditDomain p n m → AuditQuotient p n :=
  fun x i =>
    ZMod.castHom (show p i ^ n i ∣ p i ^ (n i + m i) by
      exact pow_dvd_pow _ (Nat.le_add_right _ _)) (ZMod (p i ^ n i)) (x i)

/-- Any finite audit that is constant on the fibers of a finite truncation factors through the
corresponding finite cylinder quotient. This is the concrete finite-product form of the prime-audit
factorization principle.
    thm:xi-localized-finite-prime-audit-cylinder-factorization -/
theorem paper_xi_localized_finite_prime_audit_cylinder_factorization
    (p n m : ι → ℕ) (F : AuditDomain p n m → A)
    (hF : ∀ x y, auditTruncation p n m x = auditTruncation p n m y → F x = F y) :
    ∃ Fbar : AuditQuotient p n → A, F = Fbar ∘ auditTruncation p n m := by
  classical
  let sec : AuditQuotient p n → AuditDomain p n m := fun q i =>
    Classical.choose <|
      (ZMod.castHom_surjective
        (show p i ^ n i ∣ p i ^ (n i + m i) by
          exact pow_dvd_pow _ (Nat.le_add_right _ _))) (q i)
  let Fbar : AuditQuotient p n → A := fun q => F (sec q)
  refine ⟨Fbar, ?_⟩
  funext x
  apply hF
  funext i
  have hsec :=
    Classical.choose_spec <|
      (ZMod.castHom_surjective
        (show p i ^ n i ∣ p i ^ (n i + m i) by
          exact pow_dvd_pow _ (Nat.le_add_right _ _))) (auditTruncation p n m x i)
  simpa [auditTruncation, sec] using hsec.symm

end ConcreteFactorization

end

end Omega.Zeta
