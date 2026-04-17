import Omega.Core.Fib
import Omega.Folding.FiberWeightCountComplement
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Tactic

namespace Nat

abbrev Odd (n : Nat) : Prop := _root_.Odd n
abbrev Even (n : Nat) : Prop := _root_.Even n

end Nat

namespace Omega

private theorem fib_prev_ge_two (m : Nat) (hm : 2 ≤ m) : 2 ≤ Nat.fib (m + 1) := by
  calc
    Nat.fib (m + 1) ≥ Nat.fib 3 := Nat.fib_mono (by omega)
    _ = 2 := by native_decide

private theorem fib_prev_minus_two_lt_current (m : Nat) (hm : 2 ≤ m) :
    Nat.fib (m + 1) - 2 < Nat.fib (m + 2) := by
  have hprev_ge_two : 2 ≤ Nat.fib (m + 1) := fib_prev_ge_two m hm
  have hmono : Nat.fib (m + 1) ≤ Nat.fib (m + 2) := Nat.fib_mono (by omega)
  omega

private theorem eq_or_eq_add_of_mod_eq {a b n : Nat} (hn : 0 < n) (_hb : b < n)
    (ha : a < 2 * n) (h : a % n = b) :
    a = b ∨ a = b + n := by
  have hdiv : a / n < 2 := (Nat.div_lt_iff_lt_mul hn).2 ha
  have hrepr : a = (a / n) * n + a % n := by
    simpa [Nat.mul_comm] using (Nat.div_add_mod a n).symm
  cases hq : a / n with
  | zero =>
      left
      simpa [hq, h] using hrepr
  | succ q =>
      have hq0 : q = 0 := by omega
      subst hq0
      right
      simpa [hq, h, Nat.add_comm] using hrepr

private theorem complementAction_fixed_iff_double_stableValue
    (m : Nat) (hm : 2 ≤ m) (x : X m) :
    complementAction x = x ↔
      (2 * stableValue x) % Nat.fib (m + 2) = Nat.fib (m + 1) - 2 := by
  set c : Nat := Nat.fib (m + 1) - 2
  have hc_lt : c < Nat.fib (m + 2) := by
    simpa [c] using fib_prev_minus_two_lt_current m hm
  constructor
  · intro hx
    have hleft : X.stableAdd (complementAction x) x = X.ofNat m c := by
      simpa [complementAction, c] using X.stableSub_add_cancel (X.ofNat m c) x
    have hxx : X.stableAdd x x = X.ofNat m c := by
      calc
        X.stableAdd x x = X.stableAdd (complementAction x) x := by simpa [hx]
        _ = X.ofNat m c := hleft
    have hval := congrArg stableValue hxx
    simpa [c, two_mul, X.stableValue_stableAdd, X.stableValue_ofNat_lt _ hc_lt] using hval
  · intro hdouble
    have hleft : X.stableAdd (complementAction x) x = X.ofNat m c := by
      simpa [complementAction, c] using X.stableSub_add_cancel (X.ofNat m c) x
    have hright : X.stableAdd x x = X.ofNat m c := by
      rw [X.stableAdd_self, hdouble]
    exact X.stableAdd_right_cancel (x := x) (hleft.trans hright.symm)

private theorem complementAction_fixed_double_cases
    (m : Nat) (hm : 2 ≤ m) (x : X m) (hfix : complementAction x = x) :
    2 * stableValue x = Nat.fib (m + 1) - 2 ∨
      2 * stableValue x = Nat.fib (m + 1) - 2 + Nat.fib (m + 2) := by
  set c : Nat := Nat.fib (m + 1) - 2
  set F : Nat := Nat.fib (m + 2)
  have hF_pos : 0 < F := by
    simpa [F] using fib_succ_pos (m + 1)
  have hc_lt : c < F := by
    simpa [c, F] using fib_prev_minus_two_lt_current m hm
  have hsv_lt : stableValue x < F := by
    simpa [F] using stableValue_lt_fib x
  have hdouble_lt : 2 * stableValue x < 2 * F := by omega
  have hmod : (2 * stableValue x) % F = c := by
    simpa [c, F] using (complementAction_fixed_iff_double_stableValue m hm x).1 hfix
  rcases eq_or_eq_add_of_mod_eq hF_pos hc_lt hdouble_lt hmod with h | h
  · exact Or.inl <| by simpa [c, F] using h
  · exact Or.inr <| by simpa [c, F, Nat.add_comm] using h

private theorem complementAction_histogram_parity
    (m d : Nat) (hm : 2 ≤ m) :
    (Finset.card (Finset.filter (fun x : X m => X.fiberMultiplicity x = d) Finset.univ)) % 2 =
      (Finset.card
          (Finset.filter
            (fun x : X m => complementAction x = x ∧ X.fiberMultiplicity x = d) Finset.univ)) % 2 := by
  classical
  let S : Type := {x : X m // X.fiberMultiplicity x = d}
  let g : S → S := fun x =>
    ⟨complementAction x.1, by simpa [x.2] using fiberMultiplicity_complementAction x.1 hm⟩
  have hg : Function.Involutive g := by
    intro x
    ext1
    change complementAction (complementAction x.1) = x.1
    simpa using complementAction_involutive m hm x.1
  let σ : Equiv.Perm S := Function.Involutive.toPerm g hg
  have hsq : σ ^ 2 = 1 := by
    ext x
    simp [σ, pow_two, g, hg x]
  have hsupp :
      σ.support = (Finset.univ : Finset S).filter (fun x : S => σ x ≠ x) := by
    ext x
    simp [Equiv.Perm.mem_support]
  have hsum :=
    Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset S))
      (p := fun x : S => σ x = x)
  have hsum' :
      Fintype.card {x : S // σ x = x} + σ.support.card = Fintype.card S := by
    simpa [Fintype.card_subtype, hsupp, Finset.card_univ] using hsum
  have hcard :
      Fintype.card S = Fintype.card {x : S // σ x = x} + σ.support.card := by
    omega
  have hparity_sub :
      Fintype.card S % 2 = Fintype.card {x : S // σ x = x} % 2 := by
    have h2dvd : 2 ∣ σ.support.card := Equiv.Perm.two_dvd_card_support hsq
    omega
  have hparity_left :
      (Finset.card (Finset.filter (fun x : X m => X.fiberMultiplicity x = d) Finset.univ)) % 2 =
        Fintype.card {x : S // σ x = x} % 2 := by
    simpa [S, Fintype.card_subtype] using hparity_sub
  let e : {x : S // σ x = x} ≃ {x : X m // complementAction x = x ∧ X.fiberMultiplicity x = d} :=
    { toFun := fun x =>
        ⟨x.1.1, by
          have hfix : σ x.1 = x.1 := x.2
          have hcomp : complementAction x.1.1 = x.1.1 := by
            simpa [σ, g] using congrArg Subtype.val hfix
          exact ⟨hcomp, x.1.2⟩⟩
      invFun := fun x =>
        ⟨⟨x.1, x.2.2⟩, by
          ext1
          simpa [σ, g] using x.2.1⟩
      left_inv := by
        intro x
        cases x
        rfl
      right_inv := by
        intro x
        cases x
        rfl }
  have hfixed_card :
      Fintype.card {x : S // σ x = x} =
        Fintype.card {x : X m // complementAction x = x ∧ X.fiberMultiplicity x = d} :=
    Fintype.card_congr e
  have hparity_right :
      Fintype.card {x : S // σ x = x} % 2 =
        (Finset.card
            (Finset.filter
              (fun x : X m => complementAction x = x ∧ X.fiberMultiplicity x = d)
              Finset.univ)) % 2 := by
    rw [hfixed_card, Fintype.card_subtype]
  exact hparity_left.trans hparity_right

/-- Fixed points of the complement action are controlled by the parity of `F_{m+2}`; on each
fiber-multiplicity level, the involution pairs off all nonfixed points.
    prop:fold-complement-duality-fixedpoints-parity -/
theorem paper_fold_complement_duality_fixedpoints_parity (m d : Nat) (hm : 2 ≤ m) :
    (Nat.Odd (Nat.fib (m + 2)) → ∃! x : X m, complementAction x = x) ∧
      (Nat.Even (Nat.fib (m + 2)) → ∀ x : X m, complementAction x ≠ x) ∧
      ((Finset.card (Finset.filter (fun x : X m => X.fiberMultiplicity x = d) Finset.univ)) % 2 =
        (Finset.card
            (Finset.filter
              (fun x : X m => complementAction x = x ∧ X.fiberMultiplicity x = d)
              Finset.univ)) % 2) := by
  refine ⟨?_, ?_, complementAction_histogram_parity m d hm⟩
  · intro hOddF
    set c : Nat := Nat.fib (m + 1) - 2
    set F : Nat := Nat.fib (m + 2)
    have hc_lt : c < F := by
      simpa [c, F] using fib_prev_minus_two_lt_current m hm
    rcases Nat.even_or_odd c with hcEven | hcOdd
    · rcases hcEven with ⟨k, hk⟩
      have hk_lt : k < F := by omega
      refine ⟨X.ofNat m k, ?_, ?_⟩
      · apply (complementAction_fixed_iff_double_stableValue m hm (X.ofNat m k)).2
        rw [X.stableValue_ofNat_lt _ hk_lt]
        have hkk_lt : k + k < Nat.fib (m + 2) := by omega
        rw [show Nat.fib (m + 1) - 2 = k + k by simpa [c] using hk]
        simpa [two_mul] using (Nat.mod_eq_of_lt hkk_lt)
      · intro y hy
        apply X.eq_of_stableValue_eq
        rw [X.stableValue_ofNat_lt _ hk_lt]
        rcases hOddF with ⟨t, ht⟩
        rcases complementAction_fixed_double_cases m hm y hy with hyc | hyc <;> omega
    · rcases hcOdd with ⟨k, hk⟩
      rcases hOddF with ⟨t, ht⟩
      have hk_lt_t : k < t := by omega
      have hr_lt : k + t + 1 < F := by omega
      refine ⟨X.ofNat m (k + t + 1), ?_, ?_⟩
      · apply (complementAction_fixed_iff_double_stableValue m hm (X.ofNat m (k + t + 1))).2
        rw [X.stableValue_ofNat_lt _ hr_lt]
        have hsum : 2 * (k + t + 1) = c + F := by omega
        rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt hc_lt]
      · intro y hy
        apply X.eq_of_stableValue_eq
        rw [X.stableValue_ofNat_lt _ hr_lt]
        rcases complementAction_fixed_double_cases m hm y hy with hyc | hyc <;> omega
  · intro hEvenF x hfix
    set c : Nat := Nat.fib (m + 1) - 2
    have hprev_not_even_dvd : ¬ 2 ∣ Nat.fib (m + 1) := by
      intro hprev
      have hm1 : 3 ∣ m + 1 := (fib_even_iff_three_dvd (m + 1)).1 hprev
      have hm2 : 3 ∣ m + 2 := (fib_even_iff_three_dvd (m + 2)).1 (even_iff_two_dvd.mp hEvenF)
      omega
    have hprev_not_even : ¬ Nat.Even (Nat.fib (m + 1)) := by
      intro h
      exact hprev_not_even_dvd (even_iff_two_dvd.mp h)
    have hprev_odd : Nat.Odd (Nat.fib (m + 1)) := Nat.not_even_iff_odd.mp hprev_not_even
    have hc_odd : Nat.Odd c := by
      rcases hprev_odd with ⟨k, hk⟩
      have hk_pos : 1 ≤ k := by
        have hge : 2 ≤ Nat.fib (m + 1) := fib_prev_ge_two m hm
        omega
      refine ⟨k - 1, ?_⟩
      omega
    rcases hc_odd with ⟨k, hk⟩
    rcases hEvenF with ⟨t, ht⟩
    rcases complementAction_fixed_double_cases m hm x hfix with hx | hx <;> omega

end Omega
