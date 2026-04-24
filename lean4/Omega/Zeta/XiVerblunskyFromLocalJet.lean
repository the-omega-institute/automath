import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Agreement of two coefficient streams on the prefix `0, …, N`. -/
def xiPrefixAgree (f g : ℕ → ℝ) (N : ℕ) : Prop :=
  ∀ k ≤ N, f k = g k

/-- Concrete local jet input: the local logarithmic-derivative data `ℓ_k`, the Carathéodory
coefficients `c_k`, and the first three coefficient identities used in the explicit formulas. -/
structure XiVerblunskyLocalJetData where
  ell : ℕ → ℝ
  coeff : ℕ → ℝ
  coeff_zero : coeff 0 = -ell 1
  coeff_one : coeff 1 = -ell 2
  coeff_two : coeff 2 = ell 2 - ell 3
  coeff_zero_pos : 0 < coeff 0

/-- Schur/Verblunsky coefficients generated from the Carathéodory coefficients. -/
def xiVerblunskyFromCoeffs (coeff : ℕ → ℝ) : ℕ → ℝ
  | 0 => coeff 1 / coeff 0
  | 1 => (coeff 0 * coeff 2 - coeff 1 ^ 2) / (coeff 0 ^ 2 - coeff 1 ^ 2)
  | n + 2 => (xiVerblunskyFromCoeffs coeff (n + 1) + coeff (n + 3)) / (1 + coeff (n + 2) ^ 2)

/-- The same recursion, written directly in terms of the local jet variables. -/
def xiVerblunskyFromJet (ell : ℕ → ℝ) : ℕ → ℝ
  | 0 => ell 2 / ell 1
  | 1 => (-ell 1 * ell 2 + ell 1 * ell 3 - ell 2 ^ 2) / (ell 1 ^ 2 - ell 2 ^ 2)
  | n + 2 => (xiVerblunskyFromJet ell (n + 1) + ell (n + 4)) / (1 + ell (n + 3) ^ 2)

/-- The Carathéodory-side coefficient depends only on the first `n + 2` moments. -/
def XiVerblunskyCoeffDependsOnPrefix (D : XiVerblunskyLocalJetData) (n : ℕ) : Prop :=
  ∀ coeff' : ℕ → ℝ, xiPrefixAgree coeff' D.coeff (n + 1) →
    xiVerblunskyFromCoeffs coeff' n = xiVerblunskyFromCoeffs D.coeff n

/-- The jet-side coefficient depends only on the first `n + 3` jet coordinates. -/
def XiVerblunskyJetDependsOnPrefix (D : XiVerblunskyLocalJetData) (n : ℕ) : Prop :=
  ∀ ell' : ℕ → ℝ, xiPrefixAgree ell' D.ell (n + 2) →
    xiVerblunskyFromJet ell' n = xiVerblunskyFromJet D.ell n

/-- Concrete paper-facing package for the local-jet determination of the Verblunsky prefix. -/
def XiVerblunskyFromLocalJetStatement (D : XiVerblunskyLocalJetData) : Prop :=
  0 < D.coeff 0 ∧
    xiVerblunskyFromCoeffs D.coeff 0 = D.coeff 1 / D.coeff 0 ∧
    xiVerblunskyFromCoeffs D.coeff 1 =
      (D.coeff 0 * D.coeff 2 - D.coeff 1 ^ 2) / (D.coeff 0 ^ 2 - D.coeff 1 ^ 2) ∧
    xiVerblunskyFromJet D.ell 0 = D.ell 2 / D.ell 1 ∧
    xiVerblunskyFromJet D.ell 1 =
      (-D.ell 1 * D.ell 2 + D.ell 1 * D.ell 3 - D.ell 2 ^ 2) / (D.ell 1 ^ 2 - D.ell 2 ^ 2) ∧
    xiVerblunskyFromCoeffs D.coeff 0 = xiVerblunskyFromJet D.ell 0 ∧
    xiVerblunskyFromCoeffs D.coeff 1 = xiVerblunskyFromJet D.ell 1 ∧
    (∀ n, XiVerblunskyCoeffDependsOnPrefix D n ∧ XiVerblunskyJetDependsOnPrefix D n)

lemma xiVerblunskyFromCoeffs_prefix (coeff coeff' : ℕ → ℝ) :
    ∀ n, xiPrefixAgree coeff' coeff (n + 1) →
      xiVerblunskyFromCoeffs coeff' n = xiVerblunskyFromCoeffs coeff n
  | 0, h => by
      simp [xiVerblunskyFromCoeffs, h 0 (by omega), h 1 (by omega)]
  | 1, h => by
      simp [xiVerblunskyFromCoeffs, h 0 (by omega), h 1 (by omega), h 2 (by omega)]
  | n + 2, h => by
      have hprev : xiPrefixAgree coeff' coeff (n + 2) := by
        intro k hk
        exact h k (by omega)
      have ih := xiVerblunskyFromCoeffs_prefix coeff coeff' (n + 1) hprev
      simp [xiVerblunskyFromCoeffs, ih, h (n + 2) (by omega), h (n + 3) (by omega)]

lemma xiVerblunskyFromJet_prefix (ell ell' : ℕ → ℝ) :
    ∀ n, xiPrefixAgree ell' ell (n + 2) →
      xiVerblunskyFromJet ell' n = xiVerblunskyFromJet ell n
  | 0, h => by
      simp [xiVerblunskyFromJet, h 1 (by omega), h 2 (by omega)]
  | 1, h => by
      simp [xiVerblunskyFromJet, h 1 (by omega), h 2 (by omega), h 3 (by omega)]
  | n + 2, h => by
      have hprev : xiPrefixAgree ell' ell (n + 3) := by
        intro k hk
        exact h k (by omega)
      have ih := xiVerblunskyFromJet_prefix ell ell' (n + 1) hprev
      simp [xiVerblunskyFromJet, ih, h (n + 3) (by omega), h (n + 4) (by omega)]

/-- Paper label: `thm:xi-verblunsky-from-local-jet`. The first two Verblunsky coefficients have
the stated closed forms, and each later recursive coefficient depends only on finitely many
Carathéodory coefficients or local jet entries. -/
theorem paper_xi_verblunsky_from_local_jet (D : XiVerblunskyLocalJetData) :
    XiVerblunskyFromLocalJetStatement D := by
  have hell1_ne : D.ell 1 ≠ 0 := by
    intro hell1_zero
    have hcoeff_zero : D.coeff 0 = 0 := by
      rw [D.coeff_zero, hell1_zero, neg_zero]
    linarith [D.coeff_zero_pos]
  have halpha0 :
      xiVerblunskyFromCoeffs D.coeff 0 = xiVerblunskyFromJet D.ell 0 := by
    unfold xiVerblunskyFromCoeffs xiVerblunskyFromJet
    rw [D.coeff_one, D.coeff_zero]
    field_simp [hell1_ne]
  have hnum :
      (-D.ell 1) * (D.ell 2 - D.ell 3) - (-D.ell 2) ^ 2 =
        -D.ell 1 * D.ell 2 + D.ell 1 * D.ell 3 - D.ell 2 ^ 2 := by
    ring
  have hden : (-D.ell 1) ^ 2 - (-D.ell 2) ^ 2 = D.ell 1 ^ 2 - D.ell 2 ^ 2 := by
    ring
  have halpha1 :
      xiVerblunskyFromCoeffs D.coeff 1 = xiVerblunskyFromJet D.ell 1 := by
    unfold xiVerblunskyFromCoeffs xiVerblunskyFromJet
    rw [D.coeff_zero, D.coeff_one, D.coeff_two, hnum, hden]
  refine ⟨D.coeff_zero_pos, rfl, rfl, rfl, rfl, halpha0, halpha1, ?_⟩
  intro n
  refine ⟨?_, ?_⟩
  · intro coeff' hprefix
    exact xiVerblunskyFromCoeffs_prefix D.coeff coeff' n hprefix
  · intro ell' hprefix
    exact xiVerblunskyFromJet_prefix D.ell ell' n hprefix

end

end Omega.Zeta
