import Mathlib.Tactic
import Omega.POM.S5GaloisArithmetic

namespace Omega.POM

/-- Paper label: `cor:pom-a4t-charpoly-stabilizer-s4`. -/
theorem paper_pom_a4t_charpoly_stabilizer_s4 :
    Nonempty ({σ : Equiv.Perm (Fin 5) // σ 0 = 0} ≃ Equiv.Perm (Fin 4)) ∧
      Nat.factorial 5 / 5 = Nat.factorial 4 := by
  let nonzeroEquiv : Fin 4 ≃ {x : Fin 5 // x ≠ 0} :=
    Equiv.ofBijective (fun i : Fin 4 => ⟨i.succ, by simp⟩) ⟨
      (by
        intro i j hij
        have hsucc : i.succ = j.succ := congrArg Subtype.val hij
        exact Fin.succ_injective 4 hsucc),
      (by
        intro x
        refine ⟨Fin.pred x.1 x.2, ?_⟩
        apply Subtype.ext
        simp)⟩
  let stabilizerEquiv :
      {σ : Equiv.Perm (Fin 5) // σ 0 = 0} ≃
        {σ : Equiv.Perm (Fin 5) // ∀ a, ¬a ≠ 0 → σ a = a} := {
    toFun := fun σ => ⟨σ.1, fun a ha => by
      have hazero : a = 0 := by simpa using ha
      simpa [hazero] using σ.2⟩
    invFun := fun σ => ⟨σ.1, by simpa using σ.2 0 (by simp)⟩
    left_inv := fun σ => by
      ext a
      rfl
    right_inv := fun σ => by
      ext a
      rfl }
  refine ⟨?_, by norm_num⟩
  exact ⟨stabilizerEquiv.trans
    ((Equiv.Perm.subtypeEquivSubtypePerm (fun x : Fin 5 => x ≠ 0)).symm.trans
      nonzeroEquiv.permCongr.symm)⟩

end Omega.POM
