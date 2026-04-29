import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9xe-block-uniformized-lastbit-exact-fdiv`. -/
theorem paper_xi_time_part9xe_block_uniformized_lastbit_exact_fdiv {X : Type*}
    [Fintype X] (ell : X → Bool) (muBit uBit u : Bool → ℝ) (f : ℝ → ℝ)
    (hBlock :
      ∀ i : Bool,
        uBit i = (∑ x ∈ Finset.univ.filter (fun x : X => ell x = i), u (ell x))) :
    (∑ x : X, u (ell x) * f (muBit (ell x) / uBit (ell x))) =
      ∑ i : Bool, uBit i * f (muBit i / uBit i) := by
  classical
  let term : X → ℝ := fun x => u (ell x) * f (muBit (ell x) / uBit (ell x))
  calc
    (∑ x : X, u (ell x) * f (muBit (ell x) / uBit (ell x))) =
        ∑ i : Bool, (∑ x ∈ Finset.univ.filter (fun x : X => ell x = i), term x) := by
      simpa [term] using (Finset.sum_fiberwise (s := Finset.univ) (g := ell) (f := term)).symm
    _ = ∑ i : Bool, uBit i * f (muBit i / uBit i) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      calc
        (∑ x ∈ Finset.univ.filter (fun x : X => ell x = i), term x) =
            ∑ x ∈ Finset.univ.filter (fun x : X => ell x = i),
              u (ell x) * f (muBit i / uBit i) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          have hxell : ell x = i := (Finset.mem_filter.mp hx).2
          simp [term, hxell]
        _ = (∑ x ∈ Finset.univ.filter (fun x : X => ell x = i), u (ell x)) *
            f (muBit i / uBit i) := by
          rw [Finset.sum_mul]
        _ = uBit i * f (muBit i / uBit i) := by
          rw [← hBlock i]

end Omega.Zeta
