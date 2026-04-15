import Omega.SPG.Cylinder

namespace Omega.SPG

/-- The one-sided shift on binary sequences. -/
def shift (x : OmegaInfinity) : OmegaInfinity :=
  fun t => x (t + 1)

/-- The symbolic coding induced by a time-indexed binary readout. -/
def symbolicCode {X : Type} (readout : X → ℕ → Bool) : X → OmegaInfinity :=
  fun x t => readout x t

@[simp] theorem shift_apply (x : OmegaInfinity) (t : Nat) :
    shift x t = x (t + 1) :=
  rfl

@[simp] theorem symbolicCode_apply {X : Type} (readout : X → ℕ → Bool) (x : X) (t : Nat) :
    symbolicCode readout x t = readout x t :=
  rfl

set_option maxHeartbeats 400000 in
/-- Paper-facing seed for the symbolic-factor package in the ETDS preliminaries section.
    prop:symbolic-factor -/
theorem paper_scan_projection_address_symbolic_factor_seeds
    {X : Type} (T : X → X) (readout : X → ℕ → Bool)
    (hshift : ∀ x t, readout (T x) t = readout x (t + 1)) :
    (∀ x, symbolicCode readout (T x) = shift (symbolicCode readout x)) ∧
      (∀ {m : Nat} (w : Word m),
        {x : X | prefixWord (symbolicCode readout x) m = w} =
          symbolicCode readout ⁻¹' cylinderWord w) ∧
      (∀ {m : Nat} (A : Set (Word m)),
        {x : X | prefixWord (symbolicCode readout x) m ∈ A} =
          symbolicCode readout ⁻¹' fromWordSet A) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    funext t
    exact hshift x t
  · intro m w
    rfl
  · intro m A
    rfl

/-- Wrapper theorem matching the publication label.
    prop:symbolic-factor -/
theorem paper_scan_projection_address_symbolic_factor_package
    {X : Type} (T : X → X) (readout : X → ℕ → Bool)
    (hshift : ∀ x t, readout (T x) t = readout x (t + 1)) :
    (∀ x, symbolicCode readout (T x) = shift (symbolicCode readout x)) ∧
      (∀ {m : Nat} (w : Word m),
        {x : X | prefixWord (symbolicCode readout x) m = w} =
          symbolicCode readout ⁻¹' cylinderWord w) ∧
      (∀ {m : Nat} (A : Set (Word m)),
        {x : X | prefixWord (symbolicCode readout x) m ∈ A} =
          symbolicCode readout ⁻¹' fromWordSet A) :=
  paper_scan_projection_address_symbolic_factor_seeds T readout hshift

end Omega.SPG
