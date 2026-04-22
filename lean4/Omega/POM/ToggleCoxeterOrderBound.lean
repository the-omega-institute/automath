import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.POM.FiberIndsetFactorization
import Omega.POM.ToggleOrder

namespace Omega.POM

/-- The modeled order of the scan element on a single path component, read from its cycle
decomposition. -/
def pom_toggle_coxeter_order_bound_component_order (cycleLengths : List ℕ) : ℕ :=
  cycleLengths.foldl Nat.lcm 1

/-- The product-action order obtained by taking the lcm of the component orders. -/
def pom_toggle_coxeter_order_bound_product_order {r : ℕ} (componentOrders : Fin r → ℕ) : ℕ :=
  (List.ofFn componentOrders).foldl Nat.lcm 1

/-- Universal lcm bound for a permutation acting on a finite set of size `m`. -/
def pom_toggle_coxeter_order_bound_universal_on_size (m : ℕ) : ℕ :=
  ((List.range m).map Nat.succ).foldl Nat.lcm 1

/-- Universal lcm bound specialized to the Fibonacci state count `F_{ℓ+2}` of a path component. -/
def pom_toggle_coxeter_order_bound_fibonacci_universal (ell : ℕ) : ℕ :=
  pom_toggle_coxeter_order_bound_universal_on_size (Nat.fib (ell + 2))

private lemma pom_toggle_coxeter_order_bound_cycle_dvd_universal_on_size
    (m d : ℕ) (hdle : d ≤ m) (hdpos : 0 < d) :
    d ∣ pom_toggle_coxeter_order_bound_universal_on_size m := by
  unfold pom_toggle_coxeter_order_bound_universal_on_size
  have hmem : d ∈ (List.range m).map Nat.succ := by
    refine List.mem_map.mpr ?_
    refine ⟨d - 1, List.mem_range.mpr ?_, ?_⟩
    · omega
    · omega
  exact Omega.POM.ToggleOrder.dvd_foldl_lcm_of_mem hmem

private lemma pom_toggle_coxeter_order_bound_foldl_lcm_dvd
    (cycles : List ℕ) (seed m : ℕ) (hseed : seed ∣ m) (hdvd : ∀ d ∈ cycles, d ∣ m) :
    cycles.foldl Nat.lcm seed ∣ m := by
  induction cycles generalizing seed with
  | nil =>
      simpa using hseed
  | cons d ds ih =>
      simp [List.foldl]
      apply ih
      · exact Nat.lcm_dvd hseed (hdvd d (by simp))
      · intro a ha
        exact hdvd a (by simp [ha])

private lemma pom_toggle_coxeter_order_bound_component_order_dvd_of_le
    (cycles : List ℕ) (m : ℕ) (hle : ∀ d ∈ cycles, d ≤ m) (hpos : ∀ d ∈ cycles, 0 < d) :
    pom_toggle_coxeter_order_bound_component_order cycles ∣
      pom_toggle_coxeter_order_bound_universal_on_size m := by
  unfold pom_toggle_coxeter_order_bound_component_order
  apply pom_toggle_coxeter_order_bound_foldl_lcm_dvd
  · simp
  · intro d hd
    exact pom_toggle_coxeter_order_bound_cycle_dvd_universal_on_size m d (hle d hd) (hpos d hd)

/-- Paper label: `thm:pom-toggle-coxeter-order-bound`.
For a product of path components, the modeled scan-element order is the lcm of the component
orders. If the `i`-th component acts on a set of size `F_{ℓ_i+2}` and its cycle lengths are
positive and sum to that size, then each component order is bounded by the universal lcm on
`{1, …, F_{ℓ_i+2}}`, hence so is the product order. -/
theorem paper_pom_toggle_coxeter_order_bound
    (lengths : List ℕ)
    (componentCycles : (i : Fin lengths.length) → List ℕ)
    (hpos : ∀ i d, d ∈ componentCycles i → 0 < d)
    (hcycleBound : ∀ i d, d ∈ componentCycles i → d ≤ Nat.fib (lengths.get i + 2)) :
    Nonempty (((i : Fin lengths.length) → Omega.X (lengths.get i)) ≃
      ((i : Fin lengths.length) → Omega.PathIndSets (lengths.get i))) ∧
    (∀ i,
      pom_toggle_coxeter_order_bound_component_order (componentCycles i) ∣
        pom_toggle_coxeter_order_bound_fibonacci_universal (lengths.get i)) ∧
    pom_toggle_coxeter_order_bound_product_order
        (fun i => pom_toggle_coxeter_order_bound_component_order (componentCycles i)) =
      (List.ofFn fun i => pom_toggle_coxeter_order_bound_component_order (componentCycles i)).foldl
        Nat.lcm 1 ∧
    pom_toggle_coxeter_order_bound_product_order
        (fun i => pom_toggle_coxeter_order_bound_component_order (componentCycles i)) ∣
      pom_toggle_coxeter_order_bound_product_order
        (fun i => pom_toggle_coxeter_order_bound_fibonacci_universal (lengths.get i)) := by
  refine ⟨(paper_pom_fiber_indset_factorization lengths).1, ?_, rfl, ?_⟩
  · intro i
    rw [show pom_toggle_coxeter_order_bound_fibonacci_universal (lengths.get i) =
        pom_toggle_coxeter_order_bound_universal_on_size (Nat.fib (lengths.get i + 2)) by rfl]
    apply pom_toggle_coxeter_order_bound_component_order_dvd_of_le
    · intro d hd
      exact hcycleBound i d hd
    · intro d hd
      exact hpos i d hd
  · have hmem_dvd :
        ∀ d ∈ List.ofFn (fun i => pom_toggle_coxeter_order_bound_component_order (componentCycles i)),
          d ∣ pom_toggle_coxeter_order_bound_product_order
            (fun i => pom_toggle_coxeter_order_bound_fibonacci_universal (lengths.get i)) := by
      intro d hd
      rcases List.mem_ofFn.mp hd with ⟨i, rfl⟩
      exact ((show
          pom_toggle_coxeter_order_bound_component_order (componentCycles i) ∣
            pom_toggle_coxeter_order_bound_fibonacci_universal (lengths.get i) from by
            rw [show pom_toggle_coxeter_order_bound_fibonacci_universal (lengths.get i) =
                pom_toggle_coxeter_order_bound_universal_on_size (Nat.fib (lengths.get i + 2)) by rfl]
            apply pom_toggle_coxeter_order_bound_component_order_dvd_of_le
            · intro a ha
              exact hcycleBound i a ha
            · intro a ha
              exact hpos i a ha)).trans
        (Omega.POM.ToggleOrder.dvd_foldl_lcm_of_mem (List.mem_ofFn.mpr ⟨i, rfl⟩))
    exact pom_toggle_coxeter_order_bound_foldl_lcm_dvd
      (List.ofFn fun i => pom_toggle_coxeter_order_bound_component_order (componentCycles i))
      1
      (pom_toggle_coxeter_order_bound_product_order
        (fun i => pom_toggle_coxeter_order_bound_fibonacci_universal (lengths.get i)))
      (by simp)
      hmem_dvd

end Omega.POM
