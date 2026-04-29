import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-- The one-dimensional kernel count for multiplication by a natural scalar on `ZMod N`. -/
theorem xi_integer_ellipse_mod_kernel_dirichlet_zeta_zmod_kernel_card (a N : ℕ) [NeZero N] :
    Fintype.card {x : ZMod N // (a : ZMod N) * x = 0} = Nat.gcd a N := by
  classical
  let f : ZMod N →+ ZMod N := nsmulAddMonoidHom (α := ZMod N) a
  have hker :
      Fintype.card f.ker = Nat.gcd a N := by
    have h :=
      IsAddCyclic.card_nsmulAddMonoidHom_ker (G := ZMod N) a
    simpa [f, ZMod.card, Nat.card_eq_fintype_card, Nat.gcd_comm] using h
  exact (Fintype.card_congr (Equiv.subtypeEquivRight (fun x : ZMod N => by
    simp [f, AddMonoidHom.mem_ker, nsmul_eq_mul]))).trans hker

/-- The diagonal product kernel count for the integer axis-aligned ellipse modulo `N`. -/
theorem paper_xi_integer_ellipse_mod_kernel_dirichlet_zeta (a b N : ℕ) [NeZero N] :
    Fintype.card {xy : ZMod N × ZMod N //
      (a : ZMod N) * xy.1 = 0 ∧ (b : ZMod N) * xy.2 = 0} =
    Nat.gcd a N * Nat.gcd b N := by
  classical
  let e :
      {xy : ZMod N × ZMod N //
        (a : ZMod N) * xy.1 = 0 ∧ (b : ZMod N) * xy.2 = 0} ≃
      {x : ZMod N // (a : ZMod N) * x = 0} ×
        {y : ZMod N // (b : ZMod N) * y = 0} :=
    { toFun := fun xy => (⟨xy.1.1, xy.2.1⟩, ⟨xy.1.2, xy.2.2⟩)
      invFun := fun xy => ⟨(xy.1.1, xy.2.1), ⟨xy.1.2, xy.2.2⟩⟩
      left_inv := by
        intro xy
        cases xy with
        | mk xy h =>
          cases xy
          rfl
      right_inv := by
        intro xy
        cases xy with
        | mk x y =>
          cases x
          cases y
          rfl }
  calc
    Fintype.card {xy : ZMod N × ZMod N //
        (a : ZMod N) * xy.1 = 0 ∧ (b : ZMod N) * xy.2 = 0} =
        Fintype.card ({x : ZMod N // (a : ZMod N) * x = 0} ×
          {y : ZMod N // (b : ZMod N) * y = 0}) := Fintype.card_congr e
    _ = Fintype.card {x : ZMod N // (a : ZMod N) * x = 0} *
        Fintype.card {y : ZMod N // (b : ZMod N) * y = 0} := Fintype.card_prod _ _
    _ = Nat.gcd a N * Nat.gcd b N := by
      rw [xi_integer_ellipse_mod_kernel_dirichlet_zeta_zmod_kernel_card,
        xi_integer_ellipse_mod_kernel_dirichlet_zeta_zmod_kernel_card]
