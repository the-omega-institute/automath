import Mathlib.Tactic
import Omega.POM.FiberSignedIndexMod3
import Omega.POM.FiberSignedIndexPeriodicity

namespace Omega.POM

private theorem pom_fiber_zx_minus_one_psi3_sign_mod6 (ℓ : ℕ) :
    pathIndSetPolyNegOne ℓ = pathIndSetPolyNegOne (ℓ % 6) := by
  conv_lhs => rw [← Nat.mod_add_div ℓ 6]
  induction (ℓ / 6) with
  | zero =>
      simp
  | succ k ih =>
      rw [show ℓ % 6 + 6 * (k + 1) = (ℓ % 6 + 6 * k) + 6 by ring]
      rw [(paper_pom_fiber_signed_index_periodicity (ℓ % 6 + 6 * k)).1]
      exact ih

private theorem pom_fiber_zx_minus_one_psi3_sign_single (ℓ : ℕ)
    (hℓ : pathIndSetPolyNegOne ℓ ≠ 0) :
    pathIndSetPolyNegOne ℓ = (-1 : Int) ^ ((ℓ + 1) / 3) := by
  let q := ℓ / 6
  have hdecomp : ℓ % 6 + 6 * q = ℓ := by
    dsimp [q]
    exact Nat.mod_add_div ℓ 6
  rw [pom_fiber_zx_minus_one_psi3_sign_mod6 ℓ]
  have hlt : ℓ % 6 < 6 := Nat.mod_lt ℓ (by omega)
  have hcases :
      ℓ % 6 = 0 ∨ ℓ % 6 = 1 ∨ ℓ % 6 = 2 ∨ ℓ % 6 = 3 ∨ ℓ % 6 = 4 ∨ ℓ % 6 = 5 := by
    omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5
  · have hexp : ((ℓ + 1) / 3) = 2 * q := by
      omega
    rw [h0, hexp]
    simp [pow_mul]
  · exfalso
    apply hℓ
    rw [pom_fiber_zx_minus_one_psi3_sign_mod6 ℓ, h1]
    norm_num [pathIndSetPolyNegOne]
  · have hexp : ((ℓ + 1) / 3) = 2 * q + 1 := by
      omega
    rw [h2, hexp]
    simp [pow_add, pow_mul, pathIndSetPolyNegOne]
  · have hexp : ((ℓ + 1) / 3) = 2 * q + 1 := by
      omega
    rw [h3, hexp]
    simp [pow_add, pow_mul, pathIndSetPolyNegOne]
  · exfalso
    apply hℓ
    rw [pom_fiber_zx_minus_one_psi3_sign_mod6 ℓ, h4]
    norm_num [pathIndSetPolyNegOne]
  · have hexp : ((ℓ + 1) / 3) = 2 * q + 2 := by
      omega
    rw [h5, hexp]
    simp [pow_add, pow_mul, pathIndSetPolyNegOne]

private theorem pom_fiber_zx_minus_one_psi3_sign_prod :
    ∀ L : List ℕ,
      ((L.map pathIndSetPolyNegOne).prod ≠ 0) →
        (L.map pathIndSetPolyNegOne).prod = (-1 : Int) ^ (L.map (fun ℓ => (ℓ + 1) / 3)).sum
  | [], _ => by
      simp
  | ℓ :: L, hprod => by
      have hℓ : pathIndSetPolyNegOne ℓ ≠ 0 := by
        intro hz
        apply hprod
        simp [hz]
      have htail : (L.map pathIndSetPolyNegOne).prod ≠ 0 := by
        intro hz
        apply hprod
        simp [hz]
      calc
        (((ℓ :: L).map pathIndSetPolyNegOne).prod)
            = pathIndSetPolyNegOne ℓ * (L.map pathIndSetPolyNegOne).prod := by
              simp
        _ = (-1 : Int) ^ ((ℓ + 1) / 3) * (-1 : Int) ^ (L.map (fun ℓ => (ℓ + 1) / 3)).sum := by
              rw [pom_fiber_zx_minus_one_psi3_sign_single ℓ hℓ,
                pom_fiber_zx_minus_one_psi3_sign_prod L htail]
        _ = (-1 : Int) ^ (((ℓ + 1) / 3) + (L.map (fun ℓ => (ℓ + 1) / 3)).sum) := by
              rw [← pow_add]
        _ = (-1 : Int) ^ (((ℓ :: L).map (fun ℓ => (ℓ + 1) / 3)).sum) := by
              simp

/-- Paper label: `cor:pom-fiber-zx-minus-one-psi3-sign`. -/
theorem paper_pom_fiber_zx_minus_one_psi3_sign (L : List Nat) :
    (((L.map pathIndSetPolyNegOne).prod = 0) ↔ ∃ l ∈ L, l % 3 = 1) ∧
      (((L.map pathIndSetPolyNegOne).prod ≠ 0) →
        (L.map pathIndSetPolyNegOne).prod = (-1 : Int) ^ (L.map (fun l => (l + 1) / 3)).sum) :=
  ⟨paper_pom_fiber_signed_index_mod3 L, pom_fiber_zx_minus_one_psi3_sign_prod L⟩

end Omega.POM
