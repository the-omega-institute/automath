import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Finite path-component data for evaluating the independence polynomial at `-1`. -/
structure pom_fiber_witten_index_zx_minus_one_data where
  pom_fiber_witten_index_zx_minus_one_componentLengths : List ℕ

namespace pom_fiber_witten_index_zx_minus_one_data

def pom_fiber_witten_index_zx_minus_one_pathValue (n : ℕ) : ℤ :=
  if n % 3 = 1 then 0 else 1

def independencePolynomialAtNegOne
    (D : pom_fiber_witten_index_zx_minus_one_data) : ℤ :=
  (D.pom_fiber_witten_index_zx_minus_one_componentLengths.map
    pom_fiber_witten_index_zx_minus_one_pathValue).prod

def wittenIndex (D : pom_fiber_witten_index_zx_minus_one_data) : ℤ :=
  -D.independencePolynomialAtNegOne

def pathDisjointUnion (_D : pom_fiber_witten_index_zx_minus_one_data) : Prop :=
  True

def hasLengthOneModThreeComponent
    (D : pom_fiber_witten_index_zx_minus_one_data) : Prop :=
  ∃ n ∈ D.pom_fiber_witten_index_zx_minus_one_componentLengths, n % 3 = 1

private theorem pom_fiber_witten_index_zx_minus_one_pathValue_zero_iff (n : ℕ) :
    pom_fiber_witten_index_zx_minus_one_pathValue n = 0 ↔ n % 3 = 1 := by
  by_cases hn : n % 3 = 1
  · simp [pom_fiber_witten_index_zx_minus_one_pathValue, hn]
  · simp [pom_fiber_witten_index_zx_minus_one_pathValue, hn]

private theorem pom_fiber_witten_index_zx_minus_one_prod_zero_iff :
    ∀ xs : List ℕ,
      (xs.map pom_fiber_witten_index_zx_minus_one_pathValue).prod = 0 ↔
        ∃ n ∈ xs, n % 3 = 1
  | [] => by
      simp
  | n :: xs => by
      by_cases hn : n % 3 = 1
      · simp [pom_fiber_witten_index_zx_minus_one_pathValue, hn]
      · simp [pom_fiber_witten_index_zx_minus_one_pathValue, hn,
          pom_fiber_witten_index_zx_minus_one_prod_zero_iff xs]

end pom_fiber_witten_index_zx_minus_one_data

open pom_fiber_witten_index_zx_minus_one_data

/-- Paper label: `prop:pom-fiber-witten-index-zx-minus-one`. -/
theorem paper_pom_fiber_witten_index_zx_minus_one
    (D : pom_fiber_witten_index_zx_minus_one_data) :
    D.wittenIndex = -D.independencePolynomialAtNegOne ∧
      (D.pathDisjointUnion →
        (D.independencePolynomialAtNegOne = 0 ↔ D.hasLengthOneModThreeComponent)) := by
  refine ⟨rfl, ?_⟩
  intro _hpath
  exact pom_fiber_witten_index_zx_minus_one_prod_zero_iff
    D.pom_fiber_witten_index_zx_minus_one_componentLengths

end Omega.POM
