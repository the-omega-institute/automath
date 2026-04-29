import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-prime-interleaving-composition-law`. -/
theorem paper_conclusion_prime_interleaving_composition_law {Ω X Y P : Type*}
    [AddCommMonoid P] (f : Ω → X) (g : X → Y) (rf : Ω → P) (rg : X → P)
    (Iodd Ieven oddProj evenProj : P → P)
    (hf : Function.Injective fun ω => (f ω, rf ω))
    (hg : Function.Injective fun x => (g x, rg x))
    (hodd : ∀ a b, oddProj (Ieven a + Iodd b) = b)
    (heven : ∀ a b, evenProj (Ieven a + Iodd b) = a) :
    Function.Injective (fun ω => (g (f ω), Ieven (rf ω) + Iodd (rg (f ω)))) := by
  intro omega1 omega2 homega
  have hg_eq : g (f omega1) = g (f omega2) := congrArg Prod.fst homega
  have hreg_eq :
      Ieven (rf omega1) + Iodd (rg (f omega1)) =
        Ieven (rf omega2) + Iodd (rg (f omega2)) :=
    congrArg Prod.snd homega
  have hrg_eq : rg (f omega1) = rg (f omega2) := by
    simpa [hodd] using congrArg oddProj hreg_eq
  have hf_eq : f omega1 = f omega2 := hg (Prod.ext hg_eq hrg_eq)
  have hrf_eq : rf omega1 = rf omega2 := by
    simpa [heven] using congrArg evenProj hreg_eq
  exact hf (Prod.ext hf_eq hrf_eq)

end Omega.Conclusion
