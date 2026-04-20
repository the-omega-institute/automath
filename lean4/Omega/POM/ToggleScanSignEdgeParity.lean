import Mathlib.Tactic
import Omega.Core.Fib
import Omega.POM.FiberParityMod3
import Omega.POM.ToggleScanSignGeneralFiber

namespace Omega.POM

open Omega.POM.FibCubeEdgeParity

/-- The product of the Fibonacci-cube vertex counts. -/
def toggleScanFiberVertexCount (lengths : List ℕ) : ℕ :=
  (lengths.map fun ℓ => Nat.fib (ℓ + 2)).prod

/-- The Cartesian-product edge count
`Σ_j |E(Γ_{ℓ_j})| * Π_{i ≠ j} |V(Γ_{ℓ_i})|` for the product fiber. -/
def toggleScanFiberEdgeCount : List ℕ → ℕ
  | [] => 0
  | ℓ :: lengths =>
      fibConvSum ℓ * toggleScanFiberVertexCount lengths +
        Nat.fib (ℓ + 2) * toggleScanFiberEdgeCount lengths

private theorem toggleScanExceptionalLengths_eq_nil_iff (lengths : List ℕ) :
    toggleScanExceptionalLengths lengths = [] ↔ ∀ ℓ ∈ lengths, ℓ % 3 ≠ 1 := by
  induction lengths with
  | nil =>
      simp [toggleScanExceptionalLengths]
  | cons a lengths ih =>
      by_cases ha : a % 3 = 1
      · simp [toggleScanExceptionalLengths, ha]
      · simp [toggleScanExceptionalLengths, ha]

private theorem toggleScanFiberVertexCount_mod_two_eq_one_iff (lengths : List ℕ) :
    toggleScanFiberVertexCount lengths % 2 = 1 ↔ toggleScanExceptionalLengths lengths = [] := by
  rw [toggleScanFiberVertexCount, paper_pom_fiber_parity_mod3, toggleScanExceptionalLengths_eq_nil_iff]

private theorem toggleScanFiberVertexCount_mod_two_eq_zero_of_ne_nil (lengths : List ℕ)
    (h : toggleScanExceptionalLengths lengths ≠ []) : toggleScanFiberVertexCount lengths % 2 = 0 := by
  rcases Nat.mod_two_eq_zero_or_one (toggleScanFiberVertexCount lengths) with h0 | h1
  · exact h0
  · exfalso
    exact h ((toggleScanFiberVertexCount_mod_two_eq_one_iff lengths).mp h1)

private theorem fib_shift_mod_two_eq_zero_of_exceptional {ℓ : ℕ} (h : ℓ % 3 = 1) :
    Nat.fib (ℓ + 2) % 2 = 0 := by
  rw [Omega.fib_mod_two_period (ℓ + 2)]
  have hmod : (ℓ + 2) % 3 = 0 := by omega
  simp [hmod]

private theorem fib_shift_mod_two_eq_one_of_nonexceptional {ℓ : ℕ} (h : ℓ % 3 ≠ 1) :
    Nat.fib (ℓ + 2) % 2 = 1 := by
  rw [Omega.fib_mod_two_period (ℓ + 2)]
  have hcases : ℓ % 3 = 0 ∨ ℓ % 3 = 2 := by omega
  rcases hcases with h0 | h2
  · have hmod : (ℓ + 2) % 3 = 2 := by omega
    simp [hmod]
  · have hmod : (ℓ + 2) % 3 = 1 := by omega
    simp [hmod]

private theorem toggleScanFiberEdgeCount_mod_two_cons (ℓ : ℕ) (lengths : List ℕ) :
    toggleScanFiberEdgeCount (ℓ :: lengths) % 2 =
      ((fibConvSum ℓ % 2) * (toggleScanFiberVertexCount lengths % 2) +
          (Nat.fib (ℓ + 2) % 2) * (toggleScanFiberEdgeCount lengths % 2)) %
        2 := by
  simp [toggleScanFiberEdgeCount, toggleScanFiberVertexCount, Nat.add_mod, Nat.mul_mod]

private theorem toggleScanFiberEdgeCount_parity_split (lengths : List ℕ) :
    (2 ≤ (toggleScanExceptionalLengths lengths).length →
      toggleScanFiberEdgeCount lengths % 2 = 0) ∧
    (∀ ℓ, toggleScanExceptionalLengths lengths = [ℓ] →
      toggleScanFiberEdgeCount lengths % 2 = fibConvSum ℓ % 2) ∧
    (toggleScanExceptionalLengths lengths = [] →
      toggleScanFiberEdgeCount lengths % 2 =
        (lengths.map fun ℓ => fibConvSum ℓ % 2).sum % 2) := by
  induction lengths with
  | nil =>
      refine ⟨?_, ?_, ?_⟩
      · intro h
        simp [toggleScanExceptionalLengths] at h
      · intro ℓ h
        simp [toggleScanExceptionalLengths] at h
      · intro h
        simp [toggleScanExceptionalLengths, toggleScanFiberEdgeCount]
  | cons a lengths ih =>
      rcases ih with ⟨ihMany, ihSingle, ihNone⟩
      by_cases ha : a % 3 = 1
      · have hFib : Nat.fib (a + 2) % 2 = 0 := fib_shift_mod_two_eq_zero_of_exceptional ha
        refine ⟨?_, ?_, ?_⟩
        · intro hMany
          have htail_ne : toggleScanExceptionalLengths lengths ≠ [] := by
            intro hnil
            have hMany' : 1 ≤ (toggleScanExceptionalLengths lengths).length := by
              simpa [toggleScanExceptionalLengths, ha] using hMany
            simpa [hnil] using hMany'
          have hVertex : toggleScanFiberVertexCount lengths % 2 = 0 :=
            toggleScanFiberVertexCount_mod_two_eq_zero_of_ne_nil lengths htail_ne
          rw [toggleScanFiberEdgeCount_mod_two_cons, hFib, hVertex]
          omega
        · intro ℓ hSingle
          have hsingle : a = ℓ ∧ toggleScanExceptionalLengths lengths = [] := by
            simpa [toggleScanExceptionalLengths, ha] using hSingle
          have hEq : a = ℓ := hsingle.1
          have htail_nil : toggleScanExceptionalLengths lengths = [] := hsingle.2
          have hVertex : toggleScanFiberVertexCount lengths % 2 = 1 :=
            (toggleScanFiberVertexCount_mod_two_eq_one_iff lengths).2 htail_nil
          rw [toggleScanFiberEdgeCount_mod_two_cons, hFib, hVertex]
          simpa [hEq]
        · intro hNone
          simp [toggleScanExceptionalLengths, ha] at hNone
      · have hFib : Nat.fib (a + 2) % 2 = 1 := fib_shift_mod_two_eq_one_of_nonexceptional ha
        refine ⟨?_, ?_, ?_⟩
        · intro hMany
          have htailMany : 2 ≤ (toggleScanExceptionalLengths lengths).length := by
            simpa [toggleScanExceptionalLengths, ha] using hMany
          have htail_ne : toggleScanExceptionalLengths lengths ≠ [] := by
            intro hnil
            simp [hnil] at htailMany
          have hVertex : toggleScanFiberVertexCount lengths % 2 = 0 :=
            toggleScanFiberVertexCount_mod_two_eq_zero_of_ne_nil lengths htail_ne
          have hEdge : toggleScanFiberEdgeCount lengths % 2 = 0 := ihMany htailMany
          rw [toggleScanFiberEdgeCount_mod_two_cons, hFib, hVertex, hEdge]
          omega
        · intro ℓ hSingle
          have htailSingle : toggleScanExceptionalLengths lengths = [ℓ] := by
            simpa [toggleScanExceptionalLengths, ha] using hSingle
          have hVertex : toggleScanFiberVertexCount lengths % 2 = 0 := by
            apply toggleScanFiberVertexCount_mod_two_eq_zero_of_ne_nil lengths
            simp [htailSingle]
          have hEdge : toggleScanFiberEdgeCount lengths % 2 = fibConvSum ℓ % 2 :=
            ihSingle ℓ htailSingle
          rw [toggleScanFiberEdgeCount_mod_two_cons, hFib, hVertex, hEdge]
          simp
        · intro hNone
          have htailNone : toggleScanExceptionalLengths lengths = [] := by
            simpa [toggleScanExceptionalLengths, ha] using hNone
          have hVertex : toggleScanFiberVertexCount lengths % 2 = 1 :=
            (toggleScanFiberVertexCount_mod_two_eq_one_iff lengths).2 htailNone
          have hEdge :
              toggleScanFiberEdgeCount lengths % 2 =
                (lengths.map fun ℓ => fibConvSum ℓ % 2).sum % 2 :=
            ihNone htailNone
          rw [toggleScanFiberEdgeCount_mod_two_cons, hFib, hVertex, hEdge]
          simp [List.map_cons]

/-- The general-fiber scan sign is `(-1)` to the parity of the product-fiber edge count.
    thm:pom-toggle-scan-sign-edge-parity -/
theorem paper_pom_toggle_scan_sign_edge_parity (lengths : List ℕ) :
    toggleScanGeneralFiberSign lengths =
      if toggleScanFiberEdgeCount lengths % 2 = 0 then 1 else -1 := by
  rcases toggleScanFiberEdgeCount_parity_split lengths with ⟨hMany, hSingle, hNone⟩
  rcases paper_pom_toggle_scan_sign_general_fiber lengths with ⟨hsMany, hsSingle, hsNone⟩
  by_cases hA2 : 2 ≤ (toggleScanExceptionalLengths lengths).length
  · rw [hsMany hA2]
    have hEdge : toggleScanFiberEdgeCount lengths % 2 = 0 := hMany hA2
    simp [hEdge]
  · cases hA : toggleScanExceptionalLengths lengths with
    | nil =>
        rw [hsNone hA]
        have hEdge :
            toggleScanFiberEdgeCount lengths % 2 =
              (lengths.map fun ℓ => fibConvSum ℓ % 2).sum % 2 :=
          hNone hA
        rw [hEdge]
    | cons ℓ rest =>
        cases rest with
        | nil =>
            have hEdge : toggleScanFiberEdgeCount lengths % 2 = fibConvSum ℓ % 2 := by
              exact hSingle ℓ hA
            rw [hsSingle ℓ hA, toggleScanSinglePathSign, hEdge]
        | cons b rest' =>
            exfalso
            exact hA2 (by simpa [hA])

end Omega.POM
