import Mathlib
import Omega.Conclusion.ScreenKolmogorovDeficitExactSplitting

namespace Omega.Conclusion

/-- Support size of an `F₂` kernel coordinate. -/
def screenCoordinateComplexity {r : Nat} (v : Fin r → ZMod 2) : Nat :=
  Fintype.card {i : Fin r // v i ≠ 0}

/-- Maximum coordinate support size over the `r`-bit kernel coordinate space. -/
def screenMaxConditionalComplexity (r : Nat) : Nat :=
  (Finset.univ : Finset (Fin r → ZMod 2)).sup screenCoordinateComplexity

/-- The all-ones coordinate in the `r`-bit kernel space. -/
def fullScreenCoordinate (r : Nat) : Fin r → ZMod 2 := fun _ => 1

lemma screenCoordinateComplexity_le_rank (r : Nat) (v : Fin r → ZMod 2) :
    screenCoordinateComplexity v ≤ r := by
  classical
  simpa [screenCoordinateComplexity] using
    (Fintype.card_le_of_injective (fun i : {j : Fin r // v j ≠ 0} => i.1)
      (fun a b h => Subtype.ext h))

@[simp] lemma screenCoordinateComplexity_fullScreenCoordinate (r : Nat) :
    screenCoordinateComplexity (fullScreenCoordinate r) = r := by
  classical
  simp [screenCoordinateComplexity, fullScreenCoordinate]

lemma screenMaxConditionalComplexity_eq_rank (r : Nat) :
    screenMaxConditionalComplexity r = r := by
  classical
  apply le_antisymm
  · refine Finset.sup_le ?_
    intro v hv
    exact screenCoordinateComplexity_le_rank r v
  · calc
      r = screenCoordinateComplexity (fullScreenCoordinate r) := by simp
      _ ≤ screenMaxConditionalComplexity r := by
        simpa [screenMaxConditionalComplexity] using
          (Finset.le_sup
            (s := (Finset.univ : Finset (Fin r → ZMod 2)))
            (f := screenCoordinateComplexity)
            (by simp : fullScreenCoordinate r ∈ (Finset.univ : Finset (Fin r → ZMod 2))))

/-- Paper-facing corollary: the kernel-coordinate rank extracted from the exact screen splitting
matches the largest coordinate complexity available in the fiber model.
    cor:conclusion-screen-max-conditional-complexity-equals-rank -/
theorem paper_conclusion_screen_max_conditional_complexity_equals_rank {V W : Type}
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] (f : V →ₗ[ZMod 2] W) :
    ∃ r : Nat,
      Nonempty (V ≃ₗ[ZMod 2] (LinearMap.range f × (Fin r → ZMod 2))) ∧
        screenMaxConditionalComplexity r = r := by
  rcases paper_conclusion_screen_kolmogorov_deficit_exact_splitting f with ⟨r, _, hEquiv⟩
  exact ⟨r, hEquiv, screenMaxConditionalComplexity_eq_rank r⟩

end Omega.Conclusion
