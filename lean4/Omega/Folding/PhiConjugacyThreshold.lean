import Omega.Folding.PhiSlidingBlockCode
import Mathlib.Tactic

namespace Omega.Folding

open Classical

/-- Identity local rule on one-symbol windows. -/
def phiOneWindow : (Fin 1 → Bool) → Bool := fun w => w ⟨0, by decide⟩

/-- The associated width-one sliding block code is the identity. -/
theorem slideBlockCode_phiOneWindow (s : ℤ → Bool) :
    slideBlockCode 1 phiOneWindow s = s := by
  funext t
  simp [slideBlockCode, phiOneWindow]

/-- The two constant binary sequences singled out by the `m = 2` degeneration. -/
def constZero : ℤ → Bool := fun _ => false

/-- The two constant binary sequences singled out by the `m = 2` degeneration. -/
def constOne : ℤ → Bool := fun _ => true

/-- Lightweight seed family matching the paper's threshold pattern:
for `m ≥ 3` it stabilizes to an invertible shift-equivariant code, while at `m = 2`
the two constant sequences collapse and every other sequence is fixed. -/
noncomputable def PhiConjugacySeed (m : ℕ) : (ℤ → Bool) → (ℤ → Bool) :=
  fun s =>
    if 3 ≤ m then
      slideBlockCode 1 phiOneWindow s
    else if m = 2 then
      if s = constZero ∨ s = constOne then constZero else s
    else
      s

/-- Identity inverse on the stabilized side of the threshold. -/
def PsiConjugacySeed (_m : ℕ) : (ℤ → Bool) → (ℤ → Bool) := fun y => y

theorem PhiConjugacySeed_eq_id {m : ℕ} (hm : 3 ≤ m) :
    PhiConjugacySeed m = fun s => s := by
  funext s
  simp [PhiConjugacySeed, hm, slideBlockCode_phiOneWindow]

set_option maxHeartbeats 400000 in
/-- Paper-facing seed for the conjugacy threshold pattern:
above the threshold the code is invertible and shift-equivariant, while at `m = 2`
the two constant sequences form the unique collapsed pair.
    thm:Phi_m-conjugacy-threshold -/
theorem paper_Phi_m_conjugacy_threshold :
    (∀ m : ℕ, 3 ≤ m →
      (∀ s : ℤ → Bool, PhiConjugacySeed m (shiftSeq s) = shiftSeq (PhiConjugacySeed m s)) ∧
      Function.LeftInverse (PsiConjugacySeed m) (PhiConjugacySeed m) ∧
      Function.RightInverse (PsiConjugacySeed m) (PhiConjugacySeed m) ∧
      m - 1 < m) ∧
    PhiConjugacySeed 2 constZero = PhiConjugacySeed 2 constOne ∧
    (∀ s : ℤ → Bool, s ≠ constZero → s ≠ constOne → PhiConjugacySeed 2 s = s) := by
  refine ⟨?_, ?_, ?_⟩
  · intro m hm
    have hPhi : PhiConjugacySeed m = fun s => s := PhiConjugacySeed_eq_id hm
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s
      simp [hPhi]
    · intro s
      simp [PsiConjugacySeed, hPhi]
    · intro s
      simp [PsiConjugacySeed, hPhi]
    · omega
  · simp [PhiConjugacySeed]
  · intro s hz ho
    have hne : ¬ (s = constZero ∨ s = constOne) := by
      simp [hz, ho]
    simp [PhiConjugacySeed, hne]

/-- Lowercase paper-label wrapper for the stabilized inverse and the `m = 2` collapse.
    thm:Phi_m-conjugacy-threshold -/
theorem paper_phi_m_conjugacy_threshold :
    (∀ m : ℕ, 3 ≤ m →
      Function.LeftInverse (PsiConjugacySeed m) (PhiConjugacySeed m) ∧
      Function.RightInverse (PsiConjugacySeed m) (PhiConjugacySeed m)) ∧
    PhiConjugacySeed 2 constZero = PhiConjugacySeed 2 constOne := by
  refine ⟨?_, ?_⟩
  · intro m hm
    have hPhi : PhiConjugacySeed m = fun s => s := PhiConjugacySeed_eq_id hm
    constructor
    · intro s
      simp [PsiConjugacySeed, hPhi]
    · intro s
      simp [PsiConjugacySeed, hPhi]
  · simp [PhiConjugacySeed]

universe u v w

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the exact local inverse rules for `Phi_m` in the rigidity
    reconstruction section.
    thm:Phi-m-conjugacy-threshold -/
theorem paper_resolution_folding_phi_m_conjugacy_threshold
    {X : Type u} {Y : Type v} {Window : Type w}
    (Φ : X → Y) (Ψ : Window → Y → X)
    (localRule : Window → Prop)
    (hLocal : ∀ r, localRule r)
    (hInv : ∀ r, Function.LeftInverse (Ψ r) Φ ∧ Function.RightInverse (Ψ r) Φ) :
    ∀ r, localRule r ∧ Function.LeftInverse (Ψ r) Φ ∧ Function.RightInverse (Ψ r) Φ := by
  intro r
  exact ⟨hLocal r, (hInv r).1, (hInv r).2⟩

end Omega.Folding
