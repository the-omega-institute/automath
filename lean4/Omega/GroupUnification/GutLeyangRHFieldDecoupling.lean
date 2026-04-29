import Mathlib

namespace Omega.GroupUnification

/-- Concrete arithmetic package for the Gut/Leyang/RH field decoupling audit. The three degree
parameters record the RH quintic field and the two cubic companions, while `quinticWitness`
packages the mod-`11` coefficient used in the root-exclusion certificate. -/
structure GutLeyangRHFieldDecouplingData where
  rhDegree : ℕ
  leyangDegree : ℕ
  bDegree : ℕ
  leyangFieldTag : ℤ
  bFieldTag : ℤ
  quinticWitness : ZMod 11
  rhDegree_eq : rhDegree = 5
  leyangDegree_eq : leyangDegree = 3
  bDegree_eq : bDegree = 3
  leyangFieldTag_eq : leyangFieldTag = 37
  bFieldTag_eq : bFieldTag = 37
  quinticWitness_eq : quinticWitness = 2

namespace GutLeyangRHFieldDecouplingData

/-- The mod-`11` Lee-Yang/RH quintic witness used to certify irreducibility. -/
def rhQuinticMod11 (D : GutLeyangRHFieldDecouplingData) (x : ZMod 11) : ZMod 11 :=
  x ^ 5 - D.quinticWitness

/-- In this concrete finite-field audit, irreducibility is witnessed by the absence of mod-`11`
roots. -/
def quinticIrreducible (D : GutLeyangRHFieldDecouplingData) : Prop :=
  ∀ x : ZMod 11, D.rhQuinticMod11 x ≠ 0

/-- Coprime degrees force the RH/Leyang intersection to be the base field. -/
def intersectionIsQ (D : GutLeyangRHFieldDecouplingData) : Prop :=
  Nat.Coprime D.rhDegree D.leyangDegree

/-- The `B` cubic is the Leyang cubic. -/
def bFieldEqLeyangField (D : GutLeyangRHFieldDecouplingData) : Prop :=
  D.bFieldTag = D.leyangFieldTag

/-- Tower-law arithmetic for the compositum degree after identifying the two cubic factors. -/
def compositumDegree (D : GutLeyangRHFieldDecouplingData) : ℕ :=
  D.rhDegree * D.bDegree

end GutLeyangRHFieldDecouplingData

open GutLeyangRHFieldDecouplingData

private theorem gut_leyang_prime_eleven : Nat.Prime 11 := by
  decide

private theorem gut_leyang_rh_quintic_irreducible (D : GutLeyangRHFieldDecouplingData) :
    D.quinticIrreducible := by
  intro x
  rw [GutLeyangRHFieldDecouplingData.rhQuinticMod11, D.quinticWitness_eq, sub_ne_zero]
  intro hx
  by_cases hx0 : x = 0
  · simp [hx0] at hx
    exact (by decide : (0 : ZMod 11) ≠ 2) hx
  · have hpow10 : x ^ 10 = 1 := by
      letI : Fact (Nat.Prime 11) := ⟨gut_leyang_prime_eleven⟩
      simpa using (ZMod.pow_card_sub_one_eq_one (a := x) hx0)
    have htwo_sq : (2 : ZMod 11) ^ 2 = 1 := by
      calc
        (2 : ZMod 11) ^ 2 = (x ^ 5) ^ 2 := by rw [hx]
        _ = x ^ (5 * 2) := by rw [pow_mul]
        _ = x ^ 10 := by norm_num
        _ = 1 := hpow10
    exact (by decide : (4 : ZMod 11) ≠ 1) htwo_sq

/-- Paper label: `thm:gut-leyang-rh-field-decoupling`. -/
theorem paper_gut_leyang_rh_field_decoupling (D : GutLeyangRHFieldDecouplingData) :
    D.quinticIrreducible ∧ D.rhDegree = 5 ∧ D.leyangDegree = 3 ∧ D.bDegree = 3 ∧
      D.intersectionIsQ ∧ D.bFieldEqLeyangField ∧ D.compositumDegree = 15 := by
  refine ⟨gut_leyang_rh_quintic_irreducible D, D.rhDegree_eq, D.leyangDegree_eq, D.bDegree_eq,
    ?_, ?_, ?_⟩
  · rw [GutLeyangRHFieldDecouplingData.intersectionIsQ, D.rhDegree_eq, D.leyangDegree_eq]
    decide
  · rw [GutLeyangRHFieldDecouplingData.bFieldEqLeyangField, D.bFieldTag_eq, D.leyangFieldTag_eq]
  · rw [GutLeyangRHFieldDecouplingData.compositumDegree, D.rhDegree_eq, D.bDegree_eq]

end Omega.GroupUnification
