import Omega.GU.BdryChiTwistedBinaryLabelExistence
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic

namespace Omega.GU

private theorem perm_fin_pretransitive {d : ℕ} (s0 : Fin d) :
    IsTransitiveAction (Equiv.Perm (Fin d)) (Fin d) := by
  change MulAction.IsPretransitive (Equiv.Perm (Fin d)) (Fin d)
  rw [MulAction.isPretransitive_iff_base (G := Equiv.Perm (Fin d)) (X := Fin d) s0]
  intro x
  refine ⟨Equiv.swap s0 x, by simp⟩

/-- The empty `Fin 0` action already has a vacuous sign-twisted label. -/
theorem chiTwistedBinaryLabelExists_perm_fin_zero :
    chiTwistedBinaryLabelExists (Equiv.Perm (Fin 0)) (Fin 0) Equiv.Perm.sign := by
  refine ⟨(fun i => nomatch i), ?_⟩
  intro g s
  exact Fin.elim0 s

/-- The singleton `Fin 1` action also has a sign-twisted label, since every permutation is
trivial. -/
theorem chiTwistedBinaryLabelExists_perm_fin_one :
    chiTwistedBinaryLabelExists (Equiv.Perm (Fin 1)) (Fin 1) Equiv.Perm.sign := by
  refine ⟨fun _ => 1, ?_⟩
  intro g s
  have hg : g = 1 := by
    have hg0 : g 0 = 0 := by
      apply Fin.ext
      omega
    ext x
    fin_cases x
    simp [hg0]
  simp [hg]

private theorem sign_stabilizer_trivial_fin_two :
    stabilizerChiTrivial (Equiv.Perm (Fin 2)) (Fin 2) Equiv.Perm.sign 0 := by
  intro g hg
  have hg0 : g 0 = 0 := by simpa using hg
  have hg1 : g 1 = 1 := by
    apply Fin.ext
    have hne : (g 1 : Fin 2) ≠ 0 := by
      intro h01
      have : (1 : Fin 2) = 0 := g.injective (by simpa [hg0] using h01)
      omega
    omega
  have hg' : g = 1 := by
    ext i
    fin_cases i <;> simp [hg0, hg1]
  simp [hg']

/-- The `d = 2` case from the paper statement is formalizable exactly as claimed. -/
theorem chiTwistedBinaryLabelExists_perm_fin_two :
    chiTwistedBinaryLabelExists (Equiv.Perm (Fin 2)) (Fin 2) Equiv.Perm.sign := by
  refine (paper_bdry_chi_twisted_binary_label_existence
    (Equiv.Perm (Fin 2)) (Fin 2) Equiv.Perm.sign 0 (perm_fin_pretransitive 0)).2 ?_
  exact sign_stabilizer_trivial_fin_two

/-- For the natural `S₂`-action, the sign-twisted binary label is unique up to global sign. -/
theorem paper_bdry_symmetric_group_sign_twisted_label_d2_unique
    (p q : Fin 2 → ℤˣ)
    (hp : chiTwistedBinaryLabel (Equiv.Perm (Fin 2)) (Fin 2) Equiv.Perm.sign p)
    (hq : chiTwistedBinaryLabel (Equiv.Perm (Fin 2)) (Fin 2) Equiv.Perm.sign q) :
    q = p ∨ q = fun i => (-1 : ℤˣ) * p i := by
  let u : ℤˣ := q 0 * (p 0)⁻¹
  have hu : ∀ i : Fin 2, q i = u * p i := by
    intro i
    let g : Equiv.Perm (Fin 2) := Equiv.swap 0 i
    have hpi : p i = Equiv.Perm.sign g * p 0 := by
      simpa [g] using hp g 0
    have hqi : q i = Equiv.Perm.sign g * q 0 := by
      simpa [g] using hq g 0
    calc
      q i = Equiv.Perm.sign g * q 0 := hqi
      _ = Equiv.Perm.sign g * (u * p 0) := by
        simp [u, mul_assoc]
      _ = u * (Equiv.Perm.sign g * p 0) := by
        simp [mul_assoc, mul_left_comm, mul_comm]
      _ = u * p i := by rw [hpi]
  rcases Int.units_eq_one_or u with hu1 | hu1
  · left
    apply funext
    intro i
    simpa [hu1] using hu i
  · right
    apply funext
    intro i
    simpa [hu1, mul_assoc] using hu i

/-- Paper-facing `d = 2` package: existence together with uniqueness up to global sign. -/
theorem paper_bdry_symmetric_group_sign_twisted_label_d2 :
    chiTwistedBinaryLabelExists (Equiv.Perm (Fin 2)) (Fin 2) Equiv.Perm.sign ∧
      ∀ p q : Fin 2 → ℤˣ,
        chiTwistedBinaryLabel (Equiv.Perm (Fin 2)) (Fin 2) Equiv.Perm.sign p →
          chiTwistedBinaryLabel (Equiv.Perm (Fin 2)) (Fin 2) Equiv.Perm.sign q →
            q = p ∨ q = fun i => (-1 : ℤˣ) * p i := by
  refine ⟨chiTwistedBinaryLabelExists_perm_fin_two, ?_⟩
  intro p q hp hq
  exact paper_bdry_symmetric_group_sign_twisted_label_d2_unique p q hp hq

end Omega.GU
