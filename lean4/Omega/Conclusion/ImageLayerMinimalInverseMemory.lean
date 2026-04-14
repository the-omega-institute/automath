import Mathlib.Tactic

namespace Omega.Conclusion

/-- Synchronisation depth at window size `m`.
    thm:conclusion-image-layer-minimal-inverse-memory -/
def dSync (m : ℕ) : ℕ := m - 1

/-- Closed form.
    thm:conclusion-image-layer-minimal-inverse-memory -/
theorem dSync_eq (m : ℕ) : dSync m = m - 1 := rfl

/-- Strict monotonicity of `dSync` from `m ≥ 3`.
    thm:conclusion-image-layer-minimal-inverse-memory -/
theorem dSync_strict_mono {m n : ℕ} (hm : 3 ≤ m) (hmn : m < n) :
    dSync m < dSync n := by
  unfold dSync; omega

/-- Minimal memory is exactly `m - 1` once it is sandwiched between `m - 1` and
    `m - 1`.
    thm:conclusion-image-layer-minimal-inverse-memory -/
theorem minMemory_eq_of_bounded (m memMin : ℕ) (_hm : 3 ≤ m)
    (hUpper : memMin ≤ m - 1) (hLower : m - 1 ≤ memMin) :
    memMin = m - 1 := by
  omega

/-- Same as above, expressed in terms of `dSync m`.
    thm:conclusion-image-layer-minimal-inverse-memory -/
theorem minMemory_eq_dSync (m memMin : ℕ) (_hm : 3 ≤ m)
    (hUpper : memMin ≤ dSync m) (hLower : dSync m ≤ memMin) :
    memMin = dSync m :=
  le_antisymm hUpper hLower

/-- Lower-bound contradiction: if the memory budget is at most `m - 2`, the
    required synchronisation depth `dSync m = m - 1` strictly exceeds it.
    thm:conclusion-image-layer-minimal-inverse-memory -/
theorem dSync_exceeds_insufficient_memory (m memMin : ℕ)
    (hm : 3 ≤ m) (hSmall : memMin ≤ m - 2) :
    dSync m > memMin := by
  unfold dSync; omega

/-- Paper package: image-layer minimal inverse memory scaffolding.
    thm:conclusion-image-layer-minimal-inverse-memory -/
theorem paper_image_layer_minimal_inverse_memory :
    (∀ m : ℕ, dSync m = m - 1) ∧
    (∀ m n : ℕ, 3 ≤ m → m < n → dSync m < dSync n) ∧
    (∀ (m memMin : ℕ), 3 ≤ m → memMin ≤ m - 1 → m - 1 ≤ memMin → memMin = m - 1) ∧
    (∀ (m memMin : ℕ), 3 ≤ m → memMin ≤ m - 2 → dSync m > memMin) ∧
    (∀ (m memMin : ℕ), 3 ≤ m → memMin ≤ dSync m → dSync m ≤ memMin → memMin = dSync m) :=
  ⟨dSync_eq,
   fun _ _ => dSync_strict_mono,
   minMemory_eq_of_bounded,
   dSync_exceeds_insufficient_memory,
   minMemory_eq_dSync⟩

end Omega.Conclusion
