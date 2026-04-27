import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-foldbin-exact-inversion-minimal-advice-bits`. -/
theorem paper_xi_foldbin_exact_inversion_minimal_advice_bits {Alpha Beta : Type}
    [Fintype Alpha] [DecidableEq Beta] (fold : Alpha -> Beta) (B : Nat) :
    ((Exists fun enc : Alpha -> Fin (2 ^ B) =>
      Exists fun dec : Beta -> Fin (2 ^ B) -> Option Alpha =>
        (forall n : Alpha, dec (fold n) (enc n) = some n) /\
          (forall w b n, dec w b = some n -> fold n = w))) <->
      (forall w : Beta, Fintype.card {n : Alpha // fold n = w} <= 2 ^ B) := by
  classical
  constructor
  · rintro ⟨enc, dec, hsuccess, _hfiber⟩ w
    let label : {n : Alpha // fold n = w} -> Fin (2 ^ B) := fun n => enc n.1
    have hlabel : Function.Injective label := by
      intro x y hxy
      apply Subtype.ext
      have hx : dec w (enc x.1) = some x.1 := by
        simpa [x.2] using hsuccess x.1
      have hy : dec w (enc y.1) = some y.1 := by
        simpa [y.2] using hsuccess y.1
      have hencxy : enc x.1 = enc y.1 := by
        simpa [label] using hxy
      have hsome : some x.1 = some y.1 := by
        rw [hencxy] at hx
        exact hx.symm.trans hy
      simpa using Option.some.inj hsome
    simpa [label, Fintype.card_fin] using Fintype.card_le_of_injective label hlabel
  · intro hcard
    have hchoose :
        forall w : Beta,
          Exists fun code : {n : Alpha // fold n = w} -> Fin (2 ^ B) =>
            Function.Injective code := by
      intro w
      let e : {n : Alpha // fold n = w} ≃ Fin (Fintype.card {n : Alpha // fold n = w}) :=
        Fintype.equivFin {n : Alpha // fold n = w}
      let code : {n : Alpha // fold n = w} -> Fin (2 ^ B) := fun n =>
        ⟨(e n).1, lt_of_lt_of_le (e n).2 (hcard w)⟩
      refine ⟨code, ?_⟩
      intro x y hxy
      apply e.injective
      apply Fin.ext
      simpa [code] using congrArg Fin.val hxy
    let code : forall w : Beta, {n : Alpha // fold n = w} -> Fin (2 ^ B) :=
      fun w => Classical.choose (hchoose w)
    have hcode : forall w : Beta, Function.Injective (code w) :=
      fun w => Classical.choose_spec (hchoose w)
    let enc : Alpha -> Fin (2 ^ B) := fun n => code (fold n) ⟨n, rfl⟩
    let dec : Beta -> Fin (2 ^ B) -> Option Alpha := fun w b =>
      if h : Exists fun n : {n : Alpha // fold n = w} => code w n = b then
        some (Classical.choose h).1
      else
        none
    refine ⟨enc, dec, ?_, ?_⟩
    · intro n
      dsimp [dec]
      split
      · rename_i hit
        have hchosen : Classical.choose hit = (⟨n, rfl⟩ :
            {m : Alpha // fold m = fold n}) := by
          apply hcode (fold n)
          simpa [enc] using Classical.choose_spec hit
        simp [hchosen]
      · rename_i hit
        exact False.elim (hit ⟨⟨n, rfl⟩, by simp [enc]⟩)
    · intro w b n hdec
      dsimp [dec] at hdec
      split at hdec
      · rename_i hit
        injection hdec with hn
        rw [← hn]
        exact (Classical.choose hit).2
      · contradiction

end Omega.Zeta
