import Mathlib.Tactic

namespace Omega.GU

open Finset

abbrev Weight := ℤ × ℤ × ℤ

def zeroWeight : Weight := (0, 0, 0)

def H12 : Set Weight := {w | w.2.2 = 0}
def H13 : Set Weight := {w | w.2.1 = 0}
def H23 : Set Weight := {w | w.1 = 0}

def phiB2_12 : Finset Weight :=
  {(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (1, 1, 0), (1, -1, 0), (-1, 1, 0),
    (-1, -1, 0)}

def phiB2_13 : Finset Weight :=
  {(1, 0, 0), (-1, 0, 0), (0, 0, 1), (0, 0, -1), (1, 0, 1), (1, 0, -1), (-1, 0, 1),
    (-1, 0, -1)}

def phiB2_23 : Finset Weight :=
  {(0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1), (0, 1, 1), (0, 1, -1), (0, -1, 1),
    (0, -1, -1)}

def phiC2_12 : Finset Weight :=
  {(2, 0, 0), (-2, 0, 0), (0, 2, 0), (0, -2, 0), (1, 1, 0), (1, -1, 0), (-1, 1, 0),
    (-1, -1, 0)}

def phiC2_13 : Finset Weight :=
  {(2, 0, 0), (-2, 0, 0), (0, 0, 2), (0, 0, -2), (1, 0, 1), (1, 0, -1), (-1, 0, 1),
    (-1, 0, -1)}

def phiC2_23 : Finset Weight :=
  {(0, 2, 0), (0, -2, 0), (0, 0, 2), (0, 0, -2), (0, 1, 1), (0, 1, -1), (0, -1, 1),
    (0, -1, -1)}

def b3VisibleSupport : Finset Weight :=
  insert zeroWeight (phiB2_12 ∪ phiB2_13 ∪ phiB2_23)

def c3VisibleSupport : Finset Weight :=
  insert zeroWeight (phiC2_12 ∪ phiC2_13 ∪ phiC2_23)

/-- Paper wrapper for the exact three-plane Levi decomposition of the nonzero
    window-6 B₃/C₃ visible supports.
    thm:window6-b3c3-visible-support-three-levi-planes -/
def paper_window6_b3c3_visible_support_three_levi_planes : Prop :=
  (b3VisibleSupport.erase zeroWeight = phiB2_12 ∪ phiB2_13 ∪ phiB2_23) ∧
  (c3VisibleSupport.erase zeroWeight = phiC2_12 ∪ phiC2_13 ∪ phiC2_23) ∧
  (∀ w ∈ b3VisibleSupport.erase zeroWeight ∪ c3VisibleSupport.erase zeroWeight,
    w ∈ H12 ∨ w ∈ H13 ∨ w ∈ H23) ∧
  (∀ w ∈ b3VisibleSupport ∪ c3VisibleSupport, w.1 * w.2.1 * w.2.2 = 0)

theorem paper_window6_b3c3_visible_support_three_levi_planes_proof :
    paper_window6_b3c3_visible_support_three_levi_planes := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · intro w hw
    simp [H12, H13, H23, b3VisibleSupport, c3VisibleSupport, phiB2_12, phiB2_13, phiB2_23,
      phiC2_12, phiC2_13, phiC2_23, zeroWeight] at hw ⊢
    aesop
  · intro w hw
    simp [b3VisibleSupport, c3VisibleSupport, phiB2_12, phiB2_13, phiB2_23, phiC2_12,
      phiC2_13, phiC2_23, zeroWeight] at hw ⊢
    aesop

end Omega.GU
