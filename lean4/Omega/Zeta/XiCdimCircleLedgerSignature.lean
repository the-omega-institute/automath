import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.List.Range
import Mathlib.Tactic
import Omega.Zeta.XiCdimSpectrumCompleteness

namespace Omega.Zeta

/-- Paper label: `prop:xi-cdim-circle-ledger-signature`. The free rank and the finite circle
spectrum together recover the full invariant-factor presentation. -/
theorem paper_xi_cdim_circle_ledger_signature (rank rank' : ℕ) (factors factors' : List ℕ)
    (hfac : ∀ n ∈ factors, 1 < n) (hfac' : ∀ n ∈ factors', 1 < n) :
    let spec := (List.range (factors.length + 1)).map (Omega.Zeta.xiCdimLambda factors)
    let spec' := (List.range (factors'.length + 1)).map (Omega.Zeta.xiCdimLambda factors')
    (rank = rank' ∧ spec = spec') ↔ rank = rank' ∧ factors = factors' := by
  dsimp
  set spec : List ℕ := (List.range (factors.length + 1)).map (Omega.Zeta.xiCdimLambda factors)
  set spec' : List ℕ := (List.range (factors'.length + 1)).map (Omega.Zeta.xiCdimLambda factors')
  have hrecover :
      ∀ {xs : List ℕ} (hxs : ∀ m ∈ xs, 1 < m) {n : ℕ} (hn : n < xs.length),
        xs[n] =
          (((List.range (xs.length + 1)).map (Omega.Zeta.xiCdimLambda xs))[xs.length - (n + 1)]!) /
            (((List.range (xs.length + 1)).map (Omega.Zeta.xiCdimLambda xs))[xs.length - n]!) := by
    intro xs hxs n hn
    have hprefix_pos : 0 < (xs.take n).prod := by
      apply Nat.pos_iff_ne_zero.mpr
      intro hz
      rw [List.prod_eq_zero_iff] at hz
      have hz_xs : 0 ∈ xs := (List.take_sublist n xs).subset hz
      exact Nat.not_lt_zero 1 (hxs 0 hz_xs)
    have hidx1 : xs.length - (n + 1) < xs.length + 1 := by omega
    have hidx2 : xs.length - n < xs.length + 1 := by omega
    have hget1 :
        (((List.range (xs.length + 1)).map (Omega.Zeta.xiCdimLambda xs))[xs.length - (n + 1)]!) =
          Omega.Zeta.xiCdimLambda xs (xs.length - (n + 1)) := by
      simp [hidx1]
    have hget2 :
        (((List.range (xs.length + 1)).map (Omega.Zeta.xiCdimLambda xs))[xs.length - n]!) =
          Omega.Zeta.xiCdimLambda xs (xs.length - n) := by
      simp [hidx2]
    calc
      xs[n] = ((xs.take n).prod * xs[n]) / (xs.take n).prod := by
        symm
        rw [Nat.mul_div_right _ hprefix_pos]
      _ = (xs.take (n + 1)).prod / (xs.take n).prod := by
        rw [List.prod_take_succ _ _ hn]
      _ = Omega.Zeta.xiCdimLambda xs (xs.length - (n + 1)) /
            Omega.Zeta.xiCdimLambda xs (xs.length - n) := by
        rw [Omega.Zeta.xiCdimLambda, Omega.Zeta.xiCdimLambda]
        have hsub1 : xs.length - (xs.length - (n + 1)) = n + 1 := by omega
        have hsub2 : xs.length - (xs.length - n) = n := by omega
        rw [hsub1, hsub2]
      _ = (((List.range (xs.length + 1)).map (Omega.Zeta.xiCdimLambda xs))[xs.length - (n + 1)]!) /
            (((List.range (xs.length + 1)).map (Omega.Zeta.xiCdimLambda xs))[xs.length - n]!) := by
        rw [hget1, hget2]
  constructor
  · rintro ⟨hrank, hspec⟩
    refine ⟨hrank, ?_⟩
    have hlen : factors.length = factors'.length := by
      simpa [spec, spec', List.length_map, List.length_range] using congrArg List.length hspec
    apply List.ext_getElem hlen
    intro n hn hn'
    have hspec1 :
        spec[factors.length - (n + 1)]! = spec'[factors.length - (n + 1)]! := by
      exact congrArg (fun l => l[factors.length - (n + 1)]!) hspec
    have hspec2 : spec[factors.length - n]! = spec'[factors.length - n]! := by
      exact congrArg (fun l => l[factors.length - n]!) hspec
    calc
      factors[n] = spec[factors.length - (n + 1)]! / spec[factors.length - n]! := by
        simpa [spec] using hrecover hfac hn
      _ = spec'[factors.length - (n + 1)]! / spec'[factors.length - n]! := by
        rw [hspec1, hspec2]
      _ = factors'[n] := by
        simpa [spec', hlen] using (hrecover hfac' hn').symm
  · rintro ⟨hrank, rfl⟩
    exact ⟨hrank, rfl⟩

end Omega.Zeta
