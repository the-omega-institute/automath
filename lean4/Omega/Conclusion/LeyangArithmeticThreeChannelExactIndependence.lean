import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

noncomputable section

/-- Event density for the finite uniform law on a Frobenius factor. -/
def conclusion_leyang_arithmetic_three_channel_exact_independence_eventDensity
    {α : Type*} [Fintype α] (A : Finset α) : ℝ :=
  (A.card : ℝ) / Fintype.card α

/-- Uniform expectation on a finite Frobenius factor. -/
def conclusion_leyang_arithmetic_three_channel_exact_independence_expectation
    {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  𝔼 a, f a

/-- Paper label: `thm:conclusion-leyang-arithmetic-three-channel-exact-independence`. The finite
uniform model on `S₁₀ × S₃ × S₁₉` factors exactly across the three Frobenius coordinates, so both
event densities for conjugacy-invariant subsets and tensor expectations of class functions split
as products of the marginals. -/
theorem paper_conclusion_leyang_arithmetic_three_channel_exact_independence :
    (∀ A : Finset (Equiv.Perm (Fin 10)), ∀ B : Finset (Equiv.Perm (Fin 3)),
        ∀ C : Finset (Equiv.Perm (Fin 19)),
      (∀ σ τ : Equiv.Perm (Fin 10), σ ∈ A → τ * σ * τ⁻¹ ∈ A) →
        (∀ σ τ : Equiv.Perm (Fin 3), σ ∈ B → τ * σ * τ⁻¹ ∈ B) →
        (∀ σ τ : Equiv.Perm (Fin 19), σ ∈ C → τ * σ * τ⁻¹ ∈ C) →
        conclusion_leyang_arithmetic_three_channel_exact_independence_eventDensity
            (A.product (B.product C)) =
          conclusion_leyang_arithmetic_three_channel_exact_independence_eventDensity A *
            conclusion_leyang_arithmetic_three_channel_exact_independence_eventDensity B *
              conclusion_leyang_arithmetic_three_channel_exact_independence_eventDensity C) ∧
      ∀ f : Equiv.Perm (Fin 10) → ℝ, ∀ g : Equiv.Perm (Fin 3) → ℝ, ∀ h : Equiv.Perm (Fin 19) → ℝ,
        conclusion_leyang_arithmetic_three_channel_exact_independence_expectation
            (fun x : Equiv.Perm (Fin 10) × (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 19)) =>
              f x.1 * g x.2.1 * h x.2.2) =
          conclusion_leyang_arithmetic_three_channel_exact_independence_expectation f *
            conclusion_leyang_arithmetic_three_channel_exact_independence_expectation g *
              conclusion_leyang_arithmetic_three_channel_exact_independence_expectation h := by
  refine ⟨?_, ?_⟩
  · intro A B C _hA _hB _hC
    simp [conclusion_leyang_arithmetic_three_channel_exact_independence_eventDensity,
      Finset.card_product, Fintype.card_prod, Fintype.card_perm, div_eq_mul_inv, mul_assoc,
      mul_left_comm, mul_comm]
  · intro f g h
    let EG : ℝ :=
      conclusion_leyang_arithmetic_three_channel_exact_independence_expectation g
    let EH : ℝ :=
      conclusion_leyang_arithmetic_three_channel_exact_independence_expectation h
    calc
      conclusion_leyang_arithmetic_three_channel_exact_independence_expectation
          (fun x : Equiv.Perm (Fin 10) × (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 19)) =>
            f x.1 * g x.2.1 * h x.2.2) =
          conclusion_leyang_arithmetic_three_channel_exact_independence_expectation
            (fun a : Equiv.Perm (Fin 10) =>
              conclusion_leyang_arithmetic_three_channel_exact_independence_expectation
                (fun yz : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 19) =>
                  f a * g yz.1 * h yz.2)) := by
            simpa [conclusion_leyang_arithmetic_three_channel_exact_independence_expectation] using
              (Finset.expect_product' (s := (Finset.univ : Finset (Equiv.Perm (Fin 10))))
                (t := (Finset.univ : Finset (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 19))))
                (f := fun a yz => f a * g yz.1 * h yz.2))
      _ =
          conclusion_leyang_arithmetic_three_channel_exact_independence_expectation
            (fun a : Equiv.Perm (Fin 10) => (f a * EG) * EH) := by
            refine Finset.expect_congr rfl ?_
            intro a _ha
            calc
              conclusion_leyang_arithmetic_three_channel_exact_independence_expectation
                  (fun yz : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 19) =>
                    f a * g yz.1 * h yz.2) =
                conclusion_leyang_arithmetic_three_channel_exact_independence_expectation
                  (fun b : Equiv.Perm (Fin 3) =>
                    conclusion_leyang_arithmetic_three_channel_exact_independence_expectation
                      (fun c : Equiv.Perm (Fin 19) => (f a * g b) * h c)) := by
                  simpa [conclusion_leyang_arithmetic_three_channel_exact_independence_expectation,
                    mul_assoc] using
                    (Finset.expect_product' (s := (Finset.univ : Finset (Equiv.Perm (Fin 3))))
                      (t := (Finset.univ : Finset (Equiv.Perm (Fin 19))))
                      (f := fun b c => (f a * g b) * h c))
              _ =
                conclusion_leyang_arithmetic_three_channel_exact_independence_expectation
                  (fun b : Equiv.Perm (Fin 3) => (f a * g b) * EH) := by
                  refine Finset.expect_congr rfl ?_
                  intro b _hb
                  simpa [EH,
                    conclusion_leyang_arithmetic_three_channel_exact_independence_expectation,
                    mul_assoc, mul_left_comm, mul_comm] using
                    (Finset.expect_mul (s := (Finset.univ : Finset (Equiv.Perm (Fin 19))))
                      (f := fun c : Equiv.Perm (Fin 19) => h c) (a := f a * g b)).symm
              _ = (f a * EG) * EH := by
                  calc
                    conclusion_leyang_arithmetic_three_channel_exact_independence_expectation
                        (fun b : Equiv.Perm (Fin 3) => (f a * g b) * EH) =
                      f a *
                        conclusion_leyang_arithmetic_three_channel_exact_independence_expectation
                          (fun b : Equiv.Perm (Fin 3) => g b * EH) := by
                            simpa [
                              conclusion_leyang_arithmetic_three_channel_exact_independence_expectation,
                              mul_assoc, mul_left_comm, mul_comm] using
                              (Finset.mul_expect
                                (s := (Finset.univ : Finset (Equiv.Perm (Fin 3))))
                                (f := fun b : Equiv.Perm (Fin 3) => g b * EH) (a := f a)).symm
                    _ = f a * (EG * EH) := by
                          congr 1
                          symm
                          simpa [EG,
                            conclusion_leyang_arithmetic_three_channel_exact_independence_expectation,
                            mul_assoc, mul_left_comm, mul_comm] using
                            (Finset.expect_mul
                              (s := (Finset.univ : Finset (Equiv.Perm (Fin 3))))
                              (f := fun b : Equiv.Perm (Fin 3) => g b) (a := EH))
                    _ = (f a * EG) * EH := by ring
      _ =
          (conclusion_leyang_arithmetic_three_channel_exact_independence_expectation f * EG) *
            EH := by
            simpa [EG,
              conclusion_leyang_arithmetic_three_channel_exact_independence_expectation, mul_assoc,
              mul_left_comm, mul_comm] using
              (Finset.expect_mul (s := (Finset.univ : Finset (Equiv.Perm (Fin 10))))
                (f := fun a : Equiv.Perm (Fin 10) => f a) (a := EG * EH)).symm
      _ =
          conclusion_leyang_arithmetic_three_channel_exact_independence_expectation f *
            conclusion_leyang_arithmetic_three_channel_exact_independence_expectation g *
              conclusion_leyang_arithmetic_three_channel_exact_independence_expectation h := by
            simp [EG, EH, mul_assoc]

end

end Omega.Conclusion
