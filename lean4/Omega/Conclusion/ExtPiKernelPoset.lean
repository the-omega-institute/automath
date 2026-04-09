import Mathlib.Tactic

namespace Omega.Conclusion

/-- `KernelSubset f g` holds when the kernel of `f` is contained in the
    kernel of `g`, i.e. every `f`-equivalent pair is `g`-equivalent.
    thm:conclusion-extpi-kernel-poset-classification -/
def KernelSubset {A B C : Type*} (f : A → B) (g : A → C) : Prop :=
  ∀ x y : A, f x = f y → g x = g y

/-- Reflexivity.
    thm:conclusion-extpi-kernel-poset-classification -/
theorem kernelSubset_refl {A B : Type*} (f : A → B) :
    KernelSubset f f := fun _ _ h => h

/-- Transitivity.
    thm:conclusion-extpi-kernel-poset-classification -/
theorem kernelSubset_trans {A B C D : Type*}
    (f : A → B) (g : A → C) (h : A → D)
    (h1 : KernelSubset f g) (h2 : KernelSubset g h) :
    KernelSubset f h := fun x y hxy => h2 x y (h1 x y hxy)

/-- If `g` factors through `f`, then the kernel of `f` is contained in the
    kernel of `g`.
    thm:conclusion-extpi-kernel-poset-classification -/
theorem kernelSubset_of_comp {A B C : Type*}
    (f : A → B) (g : A → C) (h : B → C) (hfg : g = h ∘ f) :
    KernelSubset f g := by
  intros x y hxy
  rw [hfg]
  simp [Function.comp, hxy]

/-- Uniqueness of the factorisation map: if `f` is surjective, any two maps
    `h₁, h₂ : B → C` with `g = hᵢ ∘ f` agree on all of `B`.
    thm:conclusion-extpi-kernel-poset-classification -/
theorem comp_unique_of_surjective {A B C : Type*}
    (f : A → B) (g : A → C) (hf : Function.Surjective f)
    (h₁ h₂ : B → C) (h1 : g = h₁ ∘ f) (h2 : g = h₂ ∘ f) :
    h₁ = h₂ := by
  funext b
  obtain ⟨a, ha⟩ := hf b
  subst ha
  have e1 : h₁ (f a) = g a := by rw [h1]; rfl
  have e2 : g a = h₂ (f a) := by rw [h2]; rfl
  exact e1.trans e2

/-- Existence of the factorisation map: if `f` is surjective and the kernel
    of `f` is contained in the kernel of `g`, then `g` factors through `f`.
    thm:conclusion-extpi-kernel-poset-classification -/
theorem exists_comp_of_kernelSubset {A B C : Type*}
    (f : A → B) (g : A → C) (hf : Function.Surjective f)
    (hker : KernelSubset f g) :
    ∃ h : B → C, g = h ∘ f := by
  classical
  refine ⟨fun b => g (Classical.choose (hf b)), ?_⟩
  funext a
  simp only [Function.comp]
  have hch : f (Classical.choose (hf (f a))) = f a :=
    Classical.choose_spec (hf (f a))
  exact hker _ _ hch.symm

/-- Paper package: Ext(π) kernel-poset classification.
    thm:conclusion-extpi-kernel-poset-classification -/
theorem paper_conclusion_extpi_kernel_poset_classification :
    (∀ {A B : Type} (f : A → B), KernelSubset f f) ∧
    (∀ {A B C D : Type} (f : A → B) (g : A → C) (h : A → D),
      KernelSubset f g → KernelSubset g h → KernelSubset f h) ∧
    (∀ {A B C : Type} (f : A → B) (g : A → C) (h : B → C),
      g = h ∘ f → KernelSubset f g) ∧
    (∀ {A B C : Type} (f : A → B) (g : A → C),
      Function.Surjective f →
      ∀ (h₁ h₂ : B → C), g = h₁ ∘ f → g = h₂ ∘ f → h₁ = h₂) ∧
    (∀ {A B C : Type} (f : A → B) (g : A → C),
      Function.Surjective f → KernelSubset f g → ∃ h : B → C, g = h ∘ f) :=
  ⟨kernelSubset_refl, kernelSubset_trans, kernelSubset_of_comp,
   comp_unique_of_surjective, exists_comp_of_kernelSubset⟩

end Omega.Conclusion
