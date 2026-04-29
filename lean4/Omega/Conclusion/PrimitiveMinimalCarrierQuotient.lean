import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic
import Omega.Conclusion.PrimitiveCosetFourierFilter

namespace Omega.Conclusion

open scoped BigOperators

/-- The common kernel of the active Fourier channels. -/
def primitiveMinimalCarrierKernel {G X : Type*} [CommGroup G] (active : Finset X)
    (χ : X → G → Complex) (hχ1 : ∀ x, χ x 1 = 1)
    (hχmul : ∀ x g h, χ x (g * h) = χ x g * χ x h) : Subgroup G where
  carrier := { g | ∀ x ∈ active, χ x g = 1 }
  one_mem' x hx := hχ1 x
  mul_mem' ha hb x hx := by rw [hχmul, ha x hx, hb x hx, one_mul]
  inv_mem' := by
    intro g ha x hx
    have hgg : χ x (g * g⁻¹) = 1 := by simpa using hχ1 x
    rw [hχmul, ha x hx, one_mul] at hgg
    exact hgg

/-- The primitive carrier is constant on right cosets of `H`. -/
def PrimitiveCarrierInvariant {G : Type*} [CommGroup G] (H : Subgroup G) (B : G → Complex) : Prop :=
  ∀ c h, h ∈ H → B (c * h) = B c

/-- Being constant on quotient classes is the concrete factorization condition through `G/H`. -/
def PrimitiveCarrierFactorsThroughQuotient {G : Type*} [CommGroup G] (H : Subgroup G)
    (B : G → Complex) : Prop :=
  ∀ ⦃a b : G⦄, a⁻¹ * b ∈ H → B a = B b

/-- Every active Fourier channel kills `H`, so it descends to the carrier quotient. -/
def PrimitiveCarrierSupportOnQuotient {G X : Type*} [CommGroup G] (H : Subgroup G)
    (active : Finset X) (χ : X → G → Complex) : Prop :=
  ∀ x ∈ active, ∀ h ∈ H, χ x h = 1

/-- If the primitive congruence profile is expanded on the active Fourier support, then the common
kernel of the active channels is exactly the maximal subgroup on which the profile is constant.
    thm:conclusion-primitive-minimal-carrier-quotient -/
theorem paper_conclusion_primitive_minimal_carrier_quotient {G X : Type*} [Fintype G]
    [CommGroup G] (active : Finset X) (χ : X → G → Complex) (Bn : X → Complex) (B : G → Complex)
    (hχ1 : ∀ x, χ x 1 = 1) (hχmul : ∀ x g h, χ x (g * h) = χ x g * χ x h)
    (hfourier : ∀ g, B g = Finset.sum active (fun x => χ x g * Bn x))
    (hcoeff_unique : ∀ k,
      (∀ c, Finset.sum active (fun x => χ x c * ((χ x k - 1) * Bn x)) = 0) →
        k ∈ primitiveMinimalCarrierKernel active χ hχ1 hχmul) :
    let H := primitiveMinimalCarrierKernel active χ hχ1 hχmul
    PrimitiveCarrierInvariant H B ∧
      PrimitiveCarrierFactorsThroughQuotient H B ∧
      (∀ K : Subgroup G, PrimitiveCarrierInvariant K B → K ≤ H) ∧
      PrimitiveCarrierSupportOnQuotient H active χ := by
  dsimp
  constructor
  · intro c h hh
    rw [hfourier, hfourier]
    refine Finset.sum_congr rfl ?_
    intro x hx
    rw [hχmul, hh x hx, mul_one]
  constructor
  · intro a b hab
    have hconst : PrimitiveCarrierInvariant (primitiveMinimalCarrierKernel active χ hχ1 hχmul) B :=
      by
        intro c h hh
        rw [hfourier, hfourier]
        refine Finset.sum_congr rfl ?_
        intro x hx
        rw [hχmul, hh x hx, mul_one]
    simpa [mul_assoc] using (hconst a (a⁻¹ * b) hab).symm
  constructor
  · intro K hK k hk
    apply hcoeff_unique k
    intro c
    have hEq : B (c * k) = B c := hK c k hk
    rw [hfourier (c * k), hfourier c] at hEq
    have hsum :
        Finset.sum active (fun x => χ x c * (χ x k * Bn x)) =
          Finset.sum active (fun x => χ x c * Bn x) := by
      calc
        Finset.sum active (fun x => χ x c * (χ x k * Bn x))
            = Finset.sum active (fun x => χ x (c * k) * Bn x) := by
                refine Finset.sum_congr rfl ?_
                intro x hx
                rw [hχmul]
                ring
        _ = Finset.sum active (fun x => χ x c * Bn x) := hEq
    calc
      Finset.sum active (fun x => χ x c * ((χ x k - 1) * Bn x))
          = Finset.sum active (fun x => χ x c * (χ x k * Bn x) - χ x c * Bn x) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              ring
      _ = Finset.sum active (fun x => χ x c * (χ x k * Bn x)) -
            Finset.sum active (fun x => χ x c * Bn x) := by
            rw [Finset.sum_sub_distrib]
      _ = 0 := by rw [hsum, sub_self]
  · intro x hx h hh
    exact hh x hx

end Omega.Conclusion
