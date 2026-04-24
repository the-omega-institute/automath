import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete certificate tower with refinement maps, verifier equivalence, and a target type for
deterministic semantics. -/
structure TypedCertificateInverseLimitRigidityData where
  Cert : ℕ → Type
  SemVal : Type
  refine : ∀ {m n : ℕ}, m ≤ n → Cert n → Cert m
  refine_id : ∀ (n : ℕ) (c : Cert n), refine (Nat.le_refl n) c = c
  refine_comp :
    ∀ {ℓ m n : ℕ} (hℓm : ℓ ≤ m) (hmn : m ≤ n) (c : Cert n),
      refine hℓm (refine hmn c) = refine (Nat.le_trans hℓm hmn) c
  verifierEq : ∀ n : ℕ, Cert n → Cert n → Prop
  verifierEq_sound : ∀ (n : ℕ) {c c' : Cert n}, verifierEq n c c' → c = c'

namespace TypedCertificateInverseLimitRigidityData

/-- Compatible families in the certificate tower. -/
def InverseLimit (D : TypedCertificateInverseLimitRigidityData) :=
  {x : ∀ n : ℕ, D.Cert n // ∀ m n : ℕ, (h : m ≤ n) → D.refine h (x n) = x m}

/-- The refinement maps satisfy the inverse-system identities. -/
def isInverseSystem (D : TypedCertificateInverseLimitRigidityData) : Prop :=
  (∀ (n : ℕ) (c : D.Cert n), D.refine (Nat.le_refl n) c = c) ∧
    ∀ ⦃ℓ m n : ℕ⦄ (hℓm : ℓ ≤ m) (hmn : m ≤ n) (c : D.Cert n),
      D.refine hℓm (D.refine hmn c) = D.refine (Nat.le_trans hℓm hmn) c

/-- Pointwise verifier equivalence already pins down a compatible family uniquely. -/
def inverseLimitUniqueModEq (D : TypedCertificateInverseLimitRigidityData) : Prop :=
  ∀ x y : D.InverseLimit, (∀ n : ℕ, D.verifierEq n (x.1 n) (y.1 n)) → x = y

/-- Every refinement-compatible deterministic semantics factors through the inverse limit. -/
def everyCompatibleDeterministicSemanticsFactors
    (D : TypedCertificateInverseLimitRigidityData) : Prop :=
  ∀ σ : ∀ n : ℕ, D.Cert n → D.SemVal,
    (∀ ⦃m n : ℕ⦄ (h : m ≤ n) (c : D.Cert n), σ m (D.refine h c) = σ n c) →
    (∀ (n : ℕ) {c c' : D.Cert n}, D.verifierEq n c c' → σ n c = σ n c') →
    ∃ φ : D.InverseLimit → D.SemVal, ∀ x : D.InverseLimit, ∀ n : ℕ, φ x = σ n (x.1 n)

lemma isInverseSystem_holds (D : TypedCertificateInverseLimitRigidityData) : D.isInverseSystem := by
  refine ⟨D.refine_id, ?_⟩
  intro ℓ m n hℓm hmn c
  exact D.refine_comp hℓm hmn c

lemma inverseLimitUniqueModEq_holds (D : TypedCertificateInverseLimitRigidityData) :
    D.inverseLimitUniqueModEq := by
  intro x y hxy
  apply Subtype.ext
  funext n
  exact D.verifierEq_sound n (hxy n)

lemma everyCompatibleDeterministicSemanticsFactors_holds
    (D : TypedCertificateInverseLimitRigidityData) :
    D.everyCompatibleDeterministicSemanticsFactors := by
  intro σ hσ _hInv
  refine ⟨fun x => σ 0 (x.1 0), ?_⟩
  intro x n
  calc
    σ 0 (x.1 0) = σ 0 (D.refine (Nat.zero_le n) (x.1 n)) := by
      rw [(x.2 0 n (Nat.zero_le n)).symm]
    _ = σ n (x.1 n) := hσ (Nat.zero_le n) (x.1 n)

end TypedCertificateInverseLimitRigidityData

open TypedCertificateInverseLimitRigidityData

/-- Paper label: `prop:conclusion-typed-certificate-inverse-limit-rigidity`. The bundled
certificate tower is an inverse system, compatible families are unique modulo verifier equality,
and every compatible deterministic semantics factors through the inverse limit. -/
theorem paper_conclusion_typed_certificate_inverse_limit_rigidity
    (D : TypedCertificateInverseLimitRigidityData) :
    D.isInverseSystem ∧ D.inverseLimitUniqueModEq ∧
      D.everyCompatibleDeterministicSemanticsFactors := by
  exact ⟨D.isInverseSystem_holds, D.inverseLimitUniqueModEq_holds,
    D.everyCompatibleDeterministicSemanticsFactors_holds⟩

end Omega.Conclusion
