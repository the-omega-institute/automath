import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-window6-cartan-lattice-mod2-boundary-parity`. -/
theorem paper_conclusion_window6_cartan_lattice_mod2_boundary_parity :
    Function.Surjective (fun v : Fin 3 → ℤ => fun i : Fin 3 => (v i : ZMod 2)) ∧
      (∀ v : Fin 3 → ℤ,
        (fun i : Fin 3 => (v i : ZMod 2)) = 0 ↔ ∃ w : Fin 3 → ℤ, v = fun i => 2 * w i) := by
  classical
  constructor
  · intro y
    refine ⟨fun i => (y i).val, ?_⟩
    funext i
    exact_mod_cast ZMod.natCast_zmod_val (y i)
  · intro v
    constructor
    · intro hv
      let w : Fin 3 → ℤ := fun i =>
        Classical.choose (show ∃ c : ℤ, v i = (2 : ℤ) * c from
          (ZMod.intCast_zmod_eq_zero_iff_dvd (v i) 2).mp (by simpa using congrFun hv i))
      refine ⟨w, ?_⟩
      · funext i
        dsimp [w]
        exact (Classical.choose_spec
          (show ∃ c : ℤ, v i = (2 : ℤ) * c from
            (ZMod.intCast_zmod_eq_zero_iff_dvd (v i) 2).mp
              (by simpa using congrFun hv i)))
    · rintro ⟨w, rfl⟩
      funext i
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * w i) 2).mpr ⟨w i, rfl⟩

end Omega.Conclusion
