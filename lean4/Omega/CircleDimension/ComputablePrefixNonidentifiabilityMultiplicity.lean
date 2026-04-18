import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Paper-facing multiplicity witness: if every fresh-bit flip immediately after a shared prefix
has complexity within a uniform additive overhead, then these competitors agree on the prefix,
remain pairwise distinct, and all satisfy the same complexity bound.
    thm:cdim-computable-prefix-nonidentifiability-multiplicity -/
theorem paper_cdim_computable_prefix_nonidentifiability_multiplicity
    (Kgen : (ℕ → Bool) → ℕ) (x : ℕ → Bool) (n t C : ℕ) (_ht : 1 ≤ t)
    (hC : ∀ j : Fin t,
      Kgen
          (fun m =>
            if m < n + j.1 then
              x m
            else if m = n + j.1 then
              !(x (n + j.1))
            else
              false) ≤
        Kgen x + C) :
    ∃ y : Fin t → (ℕ → Bool),
      (∀ j m, m < n → y j m = x m) ∧
        Function.Injective y ∧ ∀ j, Kgen (y j) ≤ Kgen x + C := by
  let y : Fin t → (ℕ → Bool) :=
    fun j m =>
      if m < n + j.1 then
        x m
      else if m = n + j.1 then
        !(x (n + j.1))
      else
        false
  refine ⟨y, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro j m hm
    have hmnj : m < n + j.1 := by omega
    simp [y, hmnj]
  · intro j₁ j₂ hEq
    apply Fin.ext
    rcases lt_trichotomy j₁.1 j₂.1 with hlt | hsame | hgt
    · have hAt := congrFun hEq (n + j₁.1)
      have hlt' : n + j₁.1 < n + j₂.1 := Nat.add_lt_add_left hlt n
      have hflip := hAt
      simp [y, hlt'] at hflip
    · exact hsame
    · have hAt := congrFun hEq (n + j₂.1)
      have hlt' : n + j₂.1 < n + j₁.1 := Nat.add_lt_add_left hgt n
      have hflip := hAt
      simp [y, hlt'] at hflip
  · intro j
    simpa [y] using hC j

end Omega.CircleDimension
