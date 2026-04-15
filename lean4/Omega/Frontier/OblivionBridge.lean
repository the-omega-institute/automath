import Omega.Folding.Defect

namespace Omega.Frontier

/-- Projection-only discretization shadow used by the oblivion bridge.
    This is the strict 1-functor part of the candidate bridge. -/
def discretizeProjMap (h : m ≤ n) : X n → X m :=
  X.restrictLE h

@[simp] theorem discretizeProjMap_apply (h : m ≤ n) (x : X n) :
    discretizeProjMap h x = X.restrictLE h x :=
  rfl

@[simp] theorem discretizeProj_id (x : X n) :
    discretizeProjMap (Nat.le_refl n) x = x := by
  simp [discretizeProjMap]

/-- Projection-only discretization is strictly functorial on coordinate restriction maps.
    This is the certified strict part of the oblivion bridge.
    thm:oblivion-bridge-projection-functorial -/
theorem discretizeProj_comp (h₁ : m ≤ n) (h₂ : n ≤ k) (x : X k) :
    discretizeProjMap h₁ (discretizeProjMap h₂ x) =
      discretizeProjMap (Nat.le_trans h₁ h₂) x := by
  simpa [discretizeProjMap] using X.restrict_functorial h₁ h₂ x

/-- Function-level version of the strict projection functoriality. -/
theorem discretize_proj_functorial (h₁ : m ≤ n) (h₂ : n ≤ k) :
    discretizeProjMap h₁ ∘ discretizeProjMap h₂ =
      discretizeProjMap (Nat.le_trans h₁ h₂) := by
  funext x
  exact discretizeProj_comp h₁ h₂ x

/-- The bridge is not strictly monoidal at finite resolution; its coherence datum is the
    carry defect cocycle already formalized in `globalDefect_compose`.
    thm:oblivion-bridge-defect-two-cell -/
theorem discretizeProj_defect_two_cell (hmk : m ≤ k) (hkn : k ≤ n) (ω : Word n) :
    globalDefect (Nat.le_trans hmk hkn) ω =
      xorWord
        (globalDefect hmk (restrictWord hkn ω))
        (restrictWord hmk (globalDefect hkn ω)) :=
  globalDefect_compose hmk hkn ω

/-- Adjacent-scale form of the defect two-cell, useful for bridge diagrams. -/
theorem discretizeProj_poincare_band (hmn : m + 1 ≤ n) (ω : Word n) :
    globalDefect (Nat.le_trans (Nat.le_succ m) hmn) ω =
      xorWord
        (globalDefect (Nat.le_succ m) (restrictWord hmn ω))
        (restrictWord (Nat.le_succ m) (globalDefect hmn ω)) :=
  globalDefect_poincare_band hmn ω

/-- Compact package for the current certified bridge surface:
    strict projection functoriality plus the defect-bearing coherence law.
    thm:oblivion-bridge-projection-package -/
theorem paper_oblivion_bridge_projection_package
    (h₁ : m₁ ≤ m₂) (h₂ : m₂ ≤ m₃) (x : X m₃) (ω : Word m₃) :
    discretizeProjMap h₁ (discretizeProjMap h₂ x) =
        discretizeProjMap (Nat.le_trans h₁ h₂) x ∧
      globalDefect (Nat.le_trans h₁ h₂) ω =
        xorWord
          (globalDefect h₁ (restrictWord h₂ ω))
          (restrictWord h₁ (globalDefect h₂ ω)) := by
  exact ⟨discretizeProj_comp h₁ h₂ x, discretizeProj_defect_two_cell h₁ h₂ ω⟩

end Omega.Frontier
