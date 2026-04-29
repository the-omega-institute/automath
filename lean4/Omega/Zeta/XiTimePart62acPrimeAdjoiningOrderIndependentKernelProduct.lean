import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete finite-coordinate model of a localized prime set. -/
def xi_time_part62ac_prime_adjoining_order_independent_kernel_product_localizedObject
    (S : Finset ℕ) : Finset ℕ :=
  S

/-- Adjoin one prime direction to the finite localized model. -/
def xi_time_part62ac_prime_adjoining_order_independent_kernel_product_adjoin
    (S : Finset ℕ) (p : ℕ) : Finset ℕ :=
  insert p S

/-- Iterated prime adjoining along a finite list. Duplicate list entries do not change the
localized object, matching the set-theoretic union in the paper statement. -/
def xi_time_part62ac_prime_adjoining_order_independent_kernel_product_adjoinList :
    Finset ℕ → List ℕ → Finset ℕ
  | S, [] => S
  | S, p :: ps =>
      xi_time_part62ac_prime_adjoining_order_independent_kernel_product_adjoinList
        (xi_time_part62ac_prime_adjoining_order_independent_kernel_product_adjoin S p) ps

/-- The cardinal contribution of the newly added `p`-axis kernel. -/
def xi_time_part62ac_prime_adjoining_order_independent_kernel_product_axisKernelCard
    (p : ℕ) : ℕ :=
  p

/-- Product of all newly added prime-axis kernel cardinalities. -/
def xi_time_part62ac_prime_adjoining_order_independent_kernel_product_kernelProduct
    (T : Finset ℕ) : ℕ :=
  T.prod fun p =>
    xi_time_part62ac_prime_adjoining_order_independent_kernel_product_axisKernelCard p

/-- Paper label: `cor:xi-time-part62ac-prime-adjoining-order-independent-kernel-product`.
In the finite prime-axis model, iterating single-prime adjoining along any enumeration of `T`
ends at `S ∪ T`, the directions newly visible over `S` are exactly `T`, and the total kernel
cardinality factors as the product of the individual prime-axis kernel cardinalities. -/
theorem paper_xi_time_part62ac_prime_adjoining_order_independent_kernel_product
    (S T : Finset ℕ) (hTprime : ∀ p ∈ T, Nat.Prime p) (hTnew : ∀ p ∈ T, p ∉ S)
    (order : List ℕ) (horder : order.toFinset = T) :
    xi_time_part62ac_prime_adjoining_order_independent_kernel_product_adjoinList S order =
        S ∪ T ∧
      (S ∪ T) \ S = T ∧
      xi_time_part62ac_prime_adjoining_order_independent_kernel_product_kernelProduct T =
        T.prod
          (fun p =>
            xi_time_part62ac_prime_adjoining_order_independent_kernel_product_axisKernelCard p) ∧
      0 < xi_time_part62ac_prime_adjoining_order_independent_kernel_product_kernelProduct T := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hadjoin :
        ∀ (S₀ : Finset ℕ) (order₀ : List ℕ),
          xi_time_part62ac_prime_adjoining_order_independent_kernel_product_adjoinList
              S₀ order₀ =
            S₀ ∪ order₀.toFinset := by
      intro S₀ order₀
      induction order₀ generalizing S₀ with
      | nil =>
          simp [xi_time_part62ac_prime_adjoining_order_independent_kernel_product_adjoinList]
      | cons p ps ih =>
          rw [xi_time_part62ac_prime_adjoining_order_independent_kernel_product_adjoinList, ih]
          ext q
          simp [xi_time_part62ac_prime_adjoining_order_independent_kernel_product_adjoin,
            Finset.mem_union, Finset.mem_insert]
    rw [hadjoin, horder]
  · ext p
    by_cases hpT : p ∈ T
    · simp [hpT, hTnew p hpT]
    · simp [hpT]
  · rfl
  · exact Finset.prod_pos fun p hpT => (hTprime p hpT).pos

end Omega.Zeta
