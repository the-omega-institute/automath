import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- A rank-`r` free abelian screen kernel written in a chosen basis. -/
abbrev conclusion_screen_kernel_solenoid_bicompletion_screen_kernel (r : ℕ) := Fin r → ℤ

/-- The profinite completion is modeled coordinatewise in the chosen basis. -/
abbrev conclusion_screen_kernel_solenoid_bicompletion_profinite_factor (r : ℕ) := Fin r → ℤ

/-- A concrete fundamental-domain coordinate on the real torus `ℝ/ℤ`. -/
abbrev conclusion_screen_kernel_solenoid_bicompletion_torus_coordinate :=
  {x : ℝ // 0 ≤ x ∧ x < 1}

/-- The connected torus factor `T^r`. -/
abbrev conclusion_screen_kernel_solenoid_bicompletion_torus (r : ℕ) :=
  Fin r → conclusion_screen_kernel_solenoid_bicompletion_torus_coordinate

/-- After choosing a basis, the bicompletion quotient is represented by its torus coordinate and
its profinite ledger coordinate. -/
abbrev conclusion_screen_kernel_solenoid_bicompletion_solenoid (r : ℕ) :=
  conclusion_screen_kernel_solenoid_bicompletion_torus r ×
    conclusion_screen_kernel_solenoid_bicompletion_profinite_factor r

/-- Zero in the torus factor. -/
def conclusion_screen_kernel_solenoid_bicompletion_zero_torus (r : ℕ) :
    conclusion_screen_kernel_solenoid_bicompletion_torus r :=
  fun _ => ⟨0, by constructor <;> norm_num⟩

/-- First-coordinate projection of the bicompletion quotient. -/
def conclusion_screen_kernel_solenoid_bicompletion_projection (r : ℕ) :
    conclusion_screen_kernel_solenoid_bicompletion_solenoid r →
      conclusion_screen_kernel_solenoid_bicompletion_torus r :=
  Prod.fst

/-- Inclusion of the profinite factor as the kernel of the torus projection. -/
def conclusion_screen_kernel_solenoid_bicompletion_kernel_embedding (r : ℕ) :
    conclusion_screen_kernel_solenoid_bicompletion_profinite_factor r →
      conclusion_screen_kernel_solenoid_bicompletion_solenoid r :=
  fun z => (conclusion_screen_kernel_solenoid_bicompletion_zero_torus r, z)

/-- Coordinate relabeling on the torus factor, expressing basis-independence under permutation of a
chosen basis. -/
def conclusion_screen_kernel_solenoid_bicompletion_torus_basis_change {r : ℕ}
    (σ : Equiv.Perm (Fin r)) :
    conclusion_screen_kernel_solenoid_bicompletion_torus r ≃
      conclusion_screen_kernel_solenoid_bicompletion_torus r where
  toFun x := x ∘ σ
  invFun x := x ∘ σ.symm
  left_inv x := by
    funext i
    simp
  right_inv x := by
    funext i
    simp

/-- Coordinate relabeling on the profinite factor. -/
def conclusion_screen_kernel_solenoid_bicompletion_profinite_basis_change {r : ℕ}
    (σ : Equiv.Perm (Fin r)) :
    conclusion_screen_kernel_solenoid_bicompletion_profinite_factor r ≃
      conclusion_screen_kernel_solenoid_bicompletion_profinite_factor r where
  toFun z := z ∘ σ
  invFun z := z ∘ σ.symm
  left_inv z := by
    funext i
    simp
  right_inv z := by
    funext i
    simp

/-- Coordinate relabeling on the whole solenoid. -/
def conclusion_screen_kernel_solenoid_bicompletion_basis_change {r : ℕ}
    (σ : Equiv.Perm (Fin r)) :
    conclusion_screen_kernel_solenoid_bicompletion_solenoid r ≃
      conclusion_screen_kernel_solenoid_bicompletion_solenoid r where
  toFun s :=
    (conclusion_screen_kernel_solenoid_bicompletion_torus_basis_change σ s.1,
      conclusion_screen_kernel_solenoid_bicompletion_profinite_basis_change σ s.2)
  invFun s :=
    (conclusion_screen_kernel_solenoid_bicompletion_torus_basis_change σ.symm s.1,
      conclusion_screen_kernel_solenoid_bicompletion_profinite_basis_change σ.symm s.2)
  left_inv s := by
    rcases s with ⟨t, z⟩
    ext <;> simp [conclusion_screen_kernel_solenoid_bicompletion_torus_basis_change,
      conclusion_screen_kernel_solenoid_bicompletion_profinite_basis_change]
  right_inv s := by
    rcases s with ⟨t, z⟩
    ext <;> simp [conclusion_screen_kernel_solenoid_bicompletion_torus_basis_change,
      conclusion_screen_kernel_solenoid_bicompletion_profinite_basis_change]

/-- Paper label: `thm:conclusion-screen-kernel-solenoid-bicompletion`. In the chosen-basis model of
the free abelian screen kernel, the bicompletion quotient splits into a torus factor and a
profinite factor, projection to the torus is surjective with kernel the profinite factor, and the
construction is independent of the chosen basis up to coordinate permutation. -/
def conclusion_screen_kernel_solenoid_bicompletion_statement : Prop :=
  ∀ r : ℕ,
    let π := conclusion_screen_kernel_solenoid_bicompletion_projection r
    let ι := conclusion_screen_kernel_solenoid_bicompletion_kernel_embedding r
    Function.Surjective π ∧
      Function.Injective ι ∧
      (∀ z, π (ι z) = conclusion_screen_kernel_solenoid_bicompletion_zero_torus r) ∧
      (∀ s,
        π s = conclusion_screen_kernel_solenoid_bicompletion_zero_torus r ↔
          ∃ z, s = ι z) ∧
      Nonempty
        (conclusion_screen_kernel_solenoid_bicompletion_screen_kernel r ≃
          conclusion_screen_kernel_solenoid_bicompletion_profinite_factor r) ∧
      Nonempty
        (conclusion_screen_kernel_solenoid_bicompletion_solenoid r ≃
          (conclusion_screen_kernel_solenoid_bicompletion_torus r ×
            conclusion_screen_kernel_solenoid_bicompletion_profinite_factor r)) ∧
      (∀ σ : Equiv.Perm (Fin r), ∀ s,
        π (conclusion_screen_kernel_solenoid_bicompletion_basis_change σ s) =
          conclusion_screen_kernel_solenoid_bicompletion_torus_basis_change σ (π s))

theorem paper_conclusion_screen_kernel_solenoid_bicompletion :
    conclusion_screen_kernel_solenoid_bicompletion_statement := by
  intro r
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    exact ⟨(t, 0), rfl⟩
  · intro z z' hzz'
    exact congrArg Prod.snd hzz'
  · intro z
    rfl
  · intro s
    rcases s with ⟨t, z⟩
    constructor
    · intro ht
      refine ⟨z, ?_⟩
      cases ht
      rfl
    · rintro ⟨z', hz'⟩
      simpa [conclusion_screen_kernel_solenoid_bicompletion_projection,
        conclusion_screen_kernel_solenoid_bicompletion_kernel_embedding] using
        congrArg Prod.fst hz'
  · exact ⟨Equiv.refl _⟩
  · exact ⟨Equiv.refl _⟩
  · intro σ s
    rfl

end Omega.Conclusion
