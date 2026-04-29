import Mathlib.Tactic

namespace Omega.Conclusion

/-- Window-6 cyclic addresses after quotienting by the four Hamming shells. -/
abbrev conclusion_window6_radial_observable_algebra_address := Fin 4

/-- Hamming weight on the finite window. -/
def conclusion_window6_radial_observable_algebra_weight
    (x : conclusion_window6_radial_observable_algebra_address) : ℕ :=
  x.val

/-- The four radial shells. -/
def conclusion_window6_radial_observable_algebra_shell
    (x : conclusion_window6_radial_observable_algebra_address) : Fin 4 :=
  x

/-- Coordinate complement on the finite window. -/
def conclusion_window6_radial_observable_algebra_complement
    (x : conclusion_window6_radial_observable_algebra_address) :
    conclusion_window6_radial_observable_algebra_address :=
  ⟨3 - x.val, by omega⟩

/-- A function is Weyl-radial when it is constant on the four window-6 shells. -/
def conclusion_window6_radial_observable_algebra_weylInvariant
    (f : conclusion_window6_radial_observable_algebra_address → ℚ) : Prop :=
  ∀ x y,
    conclusion_window6_radial_observable_algebra_shell x =
      conclusion_window6_radial_observable_algebra_shell y →
      f x = f y

/-- A function factors through the shell coordinate. -/
def conclusion_window6_radial_observable_algebra_shellConstant
    (f : conclusion_window6_radial_observable_algebra_address → ℚ) : Prop :=
  ∃ c : Fin 4 → ℚ, ∀ x, f x = c (conclusion_window6_radial_observable_algebra_shell x)

/-- The four cubic Lagrange idempotents on shell values `0,1,2,3`. -/
def conclusion_window6_radial_observable_algebra_delta (r : Fin 4) (s : ℚ) : ℚ :=
  if r.val = 0 then -((s - 1) * (s - 2) * (s - 3)) / 6
  else if r.val = 1 then (s * (s - 2) * (s - 3)) / 2
  else if r.val = 2 then -((s * (s - 1) * (s - 3)) / 2)
  else (s * (s - 1) * (s - 2)) / 6

/-- Paper-facing finite certificate for the window-6 radial observable algebra. -/
def conclusion_window6_radial_observable_algebra_statement : Prop :=
  (∀ f : conclusion_window6_radial_observable_algebra_address → ℚ,
      conclusion_window6_radial_observable_algebra_weylInvariant f →
        conclusion_window6_radial_observable_algebra_shellConstant f) ∧
    (∀ f : conclusion_window6_radial_observable_algebra_address → ℚ,
      conclusion_window6_radial_observable_algebra_shellConstant f →
        conclusion_window6_radial_observable_algebra_weylInvariant f) ∧
    (∀ s : ℚ,
      conclusion_window6_radial_observable_algebra_delta 0 s +
            conclusion_window6_radial_observable_algebra_delta 1 s +
          conclusion_window6_radial_observable_algebra_delta 2 s +
        conclusion_window6_radial_observable_algebra_delta 3 s = 1) ∧
    (∀ r t : Fin 4,
      conclusion_window6_radial_observable_algebra_delta r (t : ℚ) =
        if r = t then 1 else 0) ∧
    (∀ r t : Fin 4,
      conclusion_window6_radial_observable_algebra_delta r (t : ℚ) *
          conclusion_window6_radial_observable_algebra_delta r (t : ℚ) =
        conclusion_window6_radial_observable_algebra_delta r (t : ℚ))

/-- Paper label: `thm:conclusion-window6-radial-observable-algebra`. -/
theorem paper_conclusion_window6_radial_observable_algebra :
    conclusion_window6_radial_observable_algebra_statement := by
  classical
  refine ⟨?factor, ?invariant, ?partition, ?lagrange, ?idempotent⟩
  · intro f hf
    let c : Fin 4 → ℚ := fun r =>
      if h : ∃ x, conclusion_window6_radial_observable_algebra_shell x = r then
        f (Classical.choose h)
      else 0
    refine ⟨c, ?_⟩
    intro x
    have hx :
        ∃ y, conclusion_window6_radial_observable_algebra_shell y =
          conclusion_window6_radial_observable_algebra_shell x := ⟨x, rfl⟩
    dsimp [c]
    rw [dif_pos hx]
    exact hf x (Classical.choose hx) (Classical.choose_spec hx).symm
  · rintro f ⟨c, hc⟩ x y hxy
    rw [hc x, hc y, hxy]
  · intro s
    norm_num [conclusion_window6_radial_observable_algebra_delta]
    ring_nf
  · intro r t
    fin_cases r <;> fin_cases t <;>
      norm_num [conclusion_window6_radial_observable_algebra_delta]
  · intro r t
    fin_cases r <;> fin_cases t <;>
      norm_num [conclusion_window6_radial_observable_algebra_delta]

end Omega.Conclusion
