import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators
open scoped ComplexConjugate

/-- Summing the Fourier expansion of a primitive count over a finite coset kills every channel
outside the annihilator and multiplies the surviving channels by the subgroup cardinality.
    thm:conclusion-primitive-coset-fourier-filter -/
theorem paper_conclusion_primitive_coset_fourier_filter {G X : Type*} [Fintype G] [Mul G]
    (H : Finset G) (ann : Finset X) (c : G) (chi : X → G → Complex) (Bn : X → Complex)
    (Bcoset : G → Complex)
    (hmul : ∀ x g h, chi x (g * h) = chi x g * chi x h)
    (hann : ∀ x ∈ ann, ∀ h ∈ H, chi x h = 1)
    (hfourier : ∀ g,
      Bcoset g = (Fintype.card G : Complex)⁻¹ *
        Finset.sum ann (fun x => conj (chi x g) * Bn x)) :
    Finset.sum H (fun h => Bcoset (c * h)) =
      (H.card : Complex) * (Fintype.card G : Complex)⁻¹ *
        Finset.sum ann (fun x => conj (chi x c) * Bn x) := by
  let scale : Complex := (Fintype.card G : Complex)⁻¹
  calc
    Finset.sum H (fun h => Bcoset (c * h))
        = Finset.sum H
            (fun h => scale * Finset.sum ann (fun x => conj (chi x (c * h)) * Bn x)) :=
          by simp [scale, hfourier]
    _ = scale * Finset.sum H
          (fun h => Finset.sum ann (fun x => conj (chi x (c * h)) * Bn x)) := by
          rw [← Finset.mul_sum]
    _ = scale * Finset.sum ann
          (fun x => Finset.sum H (fun h => conj (chi x (c * h)) * Bn x)) := by
          rw [Finset.sum_comm]
    _ = scale * Finset.sum ann
          (fun x => Finset.sum H (fun h => conj (chi x c) * Bn x)) := by
          refine congrArg (fun z => scale * z) ?_
          refine Finset.sum_congr rfl ?_
          intro x hx
          refine Finset.sum_congr rfl ?_
          intro h hh
          rw [hmul, hann x hx h hh, mul_one]
    _ = scale * Finset.sum ann
          (fun x => (H.card : Complex) * (conj (chi x c) * Bn x)) := by
          refine congrArg (fun z => scale * z) ?_
          refine Finset.sum_congr rfl ?_
          intro x hx
          simp
    _ = scale * ((H.card : Complex) * Finset.sum ann (fun x => conj (chi x c) * Bn x)) :=
          by
            refine congrArg (fun z => scale * z) ?_
            rw [← Finset.mul_sum]
    _ = (H.card : Complex) * (Fintype.card G : Complex)⁻¹ *
          Finset.sum ann (fun x => conj (chi x c) * Bn x) := by
          simp [scale, mul_assoc, mul_left_comm, mul_comm]

end Omega.Conclusion
