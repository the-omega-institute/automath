import Omega.Folding.FiberWeightCount
import Omega.Folding.MomentRecurrence
import Omega.Folding.FiberArithmetic

namespace Omega

/-- Complement symmetry of weight congruence count:
    wcc(m, F_{m+1}-2-r) = wcc(m, r) for m ≥ 2.
    The bitwise complement maps weight w to F_{m+3}-2-weight(w),
    which shifts weight mod F_{m+2} by the complement constant F_{m+1}-2.
    prop:fold-fiber-count-reciprocity -/
theorem weightCongruenceCount_complement (m : Nat) (hm : 2 ≤ m) (r : Nat)
    (hr : r < Nat.fib (m + 2)) (hr2 : r ≤ Nat.fib (m + 1) - 2) :
    weightCongruenceCount m (Nat.fib (m + 1) - 2 - r) = weightCongruenceCount m r := by
  have hFpos : 0 < Nat.fib (m + 2) := fib_succ_pos (m + 1)
  have hF1le : Nat.fib (m + 1) ≤ Nat.fib (m + 2) := Nat.fib_mono (by omega)
  have hF3 : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
  have hF1_ge2 : 2 ≤ Nat.fib (m + 1) := by
    calc Nat.fib (m + 1) ≥ Nat.fib 3 := Nat.fib_mono (by omega)
      _ = 2 := by native_decide
  have hF1_2_lt : Nat.fib (m + 1) - 2 - r < Nat.fib (m + 2) := by omega
  rw [weightCongruenceCount_eq_sum_ewc m (Nat.fib (m + 1) - 2 - r) hF1_2_lt,
    weightCongruenceCount_eq_sum_ewc m r hr]
  -- Goal: ewc(m, F_{m+1}-2-r) + ewc(m, F_{m+1}-2-r+F_{m+2}) = ewc(m, r) + ewc(m, r+F_{m+2})
  -- Step 1: ewc(m, F_{m+1}-2-r) = ewc(m, r+F_{m+2}) via ewc symmetry
  -- F_{m+3}-2-(F_{m+1}-2-r) = F_{m+1}+F_{m+2}-2-F_{m+1}+2+r = F_{m+2}+r
  have hle1 : Nat.fib (m + 1) - 2 - r ≤ Nat.fib (m + 3) - 2 := by omega
  have h1 : exactWeightCount m (Nat.fib (m + 1) - 2 - r) =
      exactWeightCount m (r + Nat.fib (m + 2)) := by
    rw [exactWeightCount_symmetric m (Nat.fib (m + 1) - 2 - r) hle1]
    congr 1; omega
  -- Step 2: ewc(m, F_{m+1}-2-r+F_{m+2}) = ewc(m, r) via ewc symmetry
  -- F_{m+3}-2-(F_{m+1}-2-r+F_{m+2}) = F_{m+1}+F_{m+2}-2-F_{m+1}+2+r-F_{m+2} = r
  have hle2 : Nat.fib (m + 1) - 2 - r + Nat.fib (m + 2) ≤ Nat.fib (m + 3) - 2 := by omega
  have h2 : exactWeightCount m (Nat.fib (m + 1) - 2 - r + Nat.fib (m + 2)) =
      exactWeightCount m r := by
    rw [exactWeightCount_symmetric m _ hle2]
    congr 1; omega
  rw [h1, h2]; ring

/-- Complement preserves fiber multiplicity: d(Fold(complement w)) = d(Fold w).
    prop:fold-fiber-count-reciprocity -/
theorem fiberMultiplicity_complement (w : Word m) :
    X.fiberMultiplicity (Fold (complement w)) = X.fiberMultiplicity (Fold w) := by
  classical
  simp only [X.fiberMultiplicity]
  -- Bijection: complement maps fiber(Fold w) to fiber(Fold(complement w))
  -- Bijection: complement maps fiber(Fold w) ↔ fiber(Fold(complement w))
  -- Key: Fold v = Fold w ↔ weight v ≡ weight w (mod F)
  --   ↔ T-weight v ≡ T-weight w (mod F)
  --   ↔ weight(compl v) ≡ weight(compl w) (mod F)
  --   ↔ Fold(compl v) = Fold(compl w)
  -- Key helper: Fold_complement_mod gives stableValue(Fold(complement v)) = (T-weight v) % F
  -- So Fold(complement v) = Fold(complement w) iff (T-weight v) % F = (T-weight w) % F
  -- which follows from weight v % F = weight w % F
  have hkey : ∀ (a b : Word m), Fold a = Fold b →
      Fold (complement a) = Fold (complement b) := by
    intro a b hv
    -- Fold(complement v) = X.ofNat m (weight(complement v) % F)
    -- weight(complement v) = T - weight v, weight(complement w) = T - weight w
    -- Fold v = Fold w means weight v % F = weight w % F
    -- From weight_complement: weight(comp v) + weight v = T
    -- So weight(comp v) = T - weight v, weight(comp w) = T - weight w
    -- weight(comp v) - weight(comp w) = weight w - weight v (or vice versa)
    -- Hence weight(comp v) % F = weight(comp w) % F
    rw [Fold_eq_iff_weight_mod] at hv ⊢
    have hcv := weight_complement a
    have hcw := weight_complement b
    -- hcv: weight(comp v) + weight v = T
    -- hcw: weight(comp w) + weight w = T
    -- So weight(comp v) - weight(comp w) = weight w - weight v (in Z)
    -- which means they're congruent mod anything
    -- In Nat: we need to show a % n = b % n when a + x = T and b + y = T and x % n = y % n
    have hsum : weight (complement a) + weight a = weight (complement b) + weight b := by omega
    -- weight(comp v) + weight v ≡ weight(comp w) + weight w (mod F)  [equal]
    -- weight v ≡ weight w (mod F)  [hypothesis hv]
    -- ⇒ weight(comp v) ≡ weight(comp w) (mod F)
    -- Proof: (a + b) % n = (c + d) % n and b % n = d % n ⇒ a % n = c % n
    have h1 : Nat.ModEq (Nat.fib (m + 2)) (weight (complement a) + weight a)
        (weight (complement b) + weight b) := by
      show _ % _ = _ % _; rw [hsum]
    exact (Nat.ModEq.add_right_cancel (show Nat.ModEq _ (weight a) (weight b) from hv) h1)
  -- Map fiber(Fold w) → fiber(Fold(complement w)) via complement
  symm
  apply Finset.card_bij (fun v _ => complement v)
  · intro v hv; rw [X.mem_fiber] at hv ⊢; exact hkey v w hv
  · intro v₁ _ v₂ _ h
    have := congr_arg complement h
    rwa [complement_involution, complement_involution] at this
  · intro u hu
    rw [X.mem_fiber] at hu
    refine ⟨complement u, ?_, complement_involution u⟩
    rw [X.mem_fiber]
    -- hu: Fold u = Fold(complement w). Apply hkey u (complement w) to get
    -- Fold(complement u) = Fold(complement(complement w)) = Fold w
    have := hkey u (complement w) hu
    rwa [complement_involution] at this

-- ══════════════════════════════════════════════════════════════
-- Phase R17: Fold + complement algebra
-- ══════════════════════════════════════════════════════════════

/-- sv(Fold(complement w)) + sv(Fold w) ≡ F_{m+1}-2 (mod F_{m+2}).
    prop:fold-fiber-count-reciprocity -/
theorem stableValue_Fold_add_complement (w : Word m) (hm : 2 ≤ m) :
    (stableValue (Fold (complement w)) + stableValue (Fold w)) % Nat.fib (m + 2) =
    (Nat.fib (m + 1) - 2) % Nat.fib (m + 2) := by
  rw [stableValue_Fold_mod, stableValue_Fold_mod]
  have hcomp := weight_complement w
  have hF3 : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
  have hF1_ge2 : 2 ≤ Nat.fib (m + 1) := by
    calc Nat.fib (m + 1) ≥ Nat.fib 3 := Nat.fib_mono (by omega)
      _ = 2 := by native_decide
  -- weight(comp w) + weight w = F_{m+3} - 2 = (F_{m+1} - 2) + F_{m+2}
  have heq : weight (complement w) + weight w = Nat.fib (m + 1) - 2 + Nat.fib (m + 2) := by omega
  -- (a % F + b % F) % F = (a + b) % F
  rw [← Nat.add_mod, heq]
  -- (F_{m+1} - 2 + F_{m+2}) % F_{m+2} = (F_{m+1} - 2) % F_{m+2}
  rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]

/-- The complement action on X m: x ↦ (F_{m+1}-2) - x in Z/F_{m+2}Z.
    prop:fold-fiber-count-reciprocity -/
noncomputable def complementAction (x : X m) : X m :=
  X.stableSub (X.ofNat m (Nat.fib (m + 1) - 2)) x

/-- The complement action is involutive: comp(comp(x)) = x.
    prop:fold-fiber-count-reciprocity -/
theorem complementAction_involutive (m : Nat) (_hm : 2 ≤ m) :
    Function.Involutive (complementAction (m := m)) := by
  intro x
  unfold complementAction
  set c := X.ofNat m (Nat.fib (m + 1) - 2)
  show X.stableSub c (X.stableSub c x) = x
  -- c - (c - x) = x, proved via: (c - x) + x = c, so c - (c-x) has the same add-with-(c-x) as x
  have h1 : X.stableAdd x (X.stableSub c x) = c := by
    rw [X.stableAdd_comm]; exact X.stableSub_add_cancel c x
  have h2 : X.stableAdd (X.stableSub c (X.stableSub c x)) (X.stableSub c x) = c :=
    X.stableSub_add_cancel c (X.stableSub c x)
  exact X.stableAdd_right_cancel (x := X.stableSub c x) (h2.trans h1.symm)

/-- complementAction (Fold w) = Fold (complement w).
    prop:fold-fiber-count-reciprocity -/
theorem complementAction_eq_Fold_complement (w : Word m) (hm : 2 ≤ m) :
    complementAction (Fold w) = Fold (complement w) := by
  apply X.eq_of_stableValue_eq
  -- Both have the same stableValue: use stableValue_Fold_add_complement
  -- sv(complementAction(Fold w)) = sv(stableSub c (Fold w))
  -- sv(Fold(comp w)) satisfies: sv(Fold(comp w)) + sv(Fold w) ≡ c (mod F)
  -- sv(stableSub c (Fold w)) satisfies the same by definition of stableSub
  -- Since both are in [0, F), they must be equal.
  have hadd := stableValue_Fold_add_complement w hm
  -- hadd: (sv(Fold(comp w)) + sv(Fold w)) % F = (F1-2) % F
  unfold complementAction
  have hF : 0 < Nat.fib (m + 2) := fib_succ_pos (m + 1)
  have hF1_lt : Nat.fib (m + 1) - 2 < Nat.fib (m + 2) := by
    have := Nat.fib_mono (show m + 1 ≤ m + 2 by omega); omega
  -- sv(stableSub c x) where c = ofNat(F1-2), x = Fold w
  -- = (sv(c) + (F - sv(x))) % F = (F1-2 + (F - sv(Fold w))) % F
  rw [X.stableValue_stableSub, X.stableValue_ofNat_lt _ hF1_lt]
  -- sv(Fold(comp w)) also satisfies:
  -- sv(Fold(comp w)) = (F1-2 + F - sv(Fold w)) % F  (from hadd, since sv < F)
  -- They're equal because (a + (F - b)) % F = (a + F - b) % F when b < F
  have hsvlt := stableValue_lt_fib (Fold w)
  have hsvlt2 := stableValue_lt_fib (Fold (complement w))
  -- From hadd: sv(Fold(comp w)) ≡ F1-2 - sv(Fold w) (mod F)
  -- Our goal: (F1-2 + (F - sv(Fold w))) % F = sv(Fold(comp w))
  -- Since sv(Fold(comp w)) < F, we have sv(Fold(comp w)) = (F1-2 - sv(Fold w) + F) % F
  -- = (F1-2 + (F - sv(Fold w))) % F. Done!
  -- From hadd: (sv(Fold(comp w)) + sv(Fold w)) % F = (F1-2) % F
  -- Since both sides < 2F, and F1-2 < F:
  rw [Nat.mod_eq_of_lt hF1_lt] at hadd
  -- hadd : (sv(comp) + sv(w)) % F = F1-2
  -- sum < 2F, so sum = F1-2 or sum = F1-2+F
  set s := stableValue (Fold (complement w))
  set v := stableValue (Fold w)
  have hsum_lt : s + v < 2 * Nat.fib (m + 2) := by omega
  -- From a % n = b with a < 2n and b < n: a = b or a = b + n
  have : s + v = Nat.fib (m + 1) - 2 ∨ s + v = Nat.fib (m + 1) - 2 + Nat.fib (m + 2) := by
    -- a % n = b with a < 2n and b < n implies a = b or a = b + n
    have h1 := Nat.div_add_mod (s + v) (Nat.fib (m + 2))
    have h2 : (s + v) / Nat.fib (m + 2) < 2 := (Nat.div_lt_iff_lt_mul hF).mpr hsum_lt
    have h3 : (s + v) % Nat.fib (m + 2) = Nat.fib (m + 1) - 2 := hadd
    interval_cases ((s + v) / Nat.fib (m + 2)) <;> omega
  -- Goal: (F1-2 + (F - v)) % F = s
  -- Case 1: s + v = F1-2, so s = F1-2-v, and F1-2+F-v = s+F, so (s+F) % F = s. ✓
  -- Case 2: s + v = F1-2+F, so s = F1-2+F-v, and F1-2+F-v = s, so s % F = s (since s < F). ✓
  have hF1F2 : Nat.fib (m + 1) ≤ Nat.fib (m + 2) := Nat.fib_mono (by omega)
  rcases this with h | h
  · -- s + v = F1-2, so F1-2+(F-v) = s+F
    have : Nat.fib (m + 1) - 2 + (Nat.fib (m + 2) - v) = s + Nat.fib (m + 2) := by omega
    rw [this, show s + Nat.fib (m + 2) = s + 1 * Nat.fib (m + 2) from by ring,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega : s < Nat.fib (m + 2))]
  · -- s + v = F1-2+F, so F1-2+(F-v) = s
    have : Nat.fib (m + 1) - 2 + (Nat.fib (m + 2) - v) = s := by omega
    rw [this, Nat.mod_eq_of_lt (by omega : s < Nat.fib (m + 2))]

/-- d(complementAction x) = d(x).
    prop:fold-fiber-count-reciprocity -/
theorem fiberMultiplicity_complementAction (x : X m) (hm : 2 ≤ m) :
    X.fiberMultiplicity (complementAction x) = X.fiberMultiplicity x := by
  -- x = Fold w for some w (via Fold surjectivity)
  obtain ⟨w, rfl⟩ := Fold_surjective m x
  rw [complementAction_eq_Fold_complement w hm]
  exact fiberMultiplicity_complement w

-- ══════════════════════════════════════════════════════════════
-- Phase R57: Fiber multiplicity complement parity
-- ══════════════════════════════════════════════════════════════

/-- Fiber multiplicity parity is preserved under the complement action.
    cor:fold-fiber-parity-complement -/
theorem fiberMultiplicity_complement_parity (x : X m) (hm : 2 ≤ m) :
    X.fiberMultiplicity x % 2 = X.fiberMultiplicity (complementAction x) % 2 :=
  congrArg (· % 2) (fiberMultiplicity_complementAction x hm).symm

-- ══════════════════════════════════════════════════════════════
-- Phase R136: Weight count spectrum at m=5
-- ══════════════════════════════════════════════════════════════

/-- EWC spectrum at m=5: complete weight distribution [1,1,1,2,1,2,2,1,3,2,2,3,1].
    bridge:ewc-complement-symmetry -/
theorem ewc_spectrum_five :
    exactWeightCount 5 0 = 1 ∧ exactWeightCount 5 1 = 1 ∧
    exactWeightCount 5 2 = 1 ∧ exactWeightCount 5 3 = 2 ∧
    exactWeightCount 5 4 = 1 ∧ exactWeightCount 5 5 = 2 ∧
    exactWeightCount 5 6 = 2 ∧ exactWeightCount 5 7 = 1 ∧
    exactWeightCount 5 8 = 3 ∧ exactWeightCount 5 9 = 2 ∧
    exactWeightCount 5 10 = 2 ∧ exactWeightCount 5 11 = 3 ∧
    exactWeightCount 5 12 = 1 := by native_decide

/-- EWC total for m=5 over weight range 0..20: Σ ewc(5,n) = 2^5 = 32.
    bridge:ewc-complement-symmetry -/
theorem ewc_sum_five :
    (Finset.range 21).sum (exactWeightCount 5) = 32 := by native_decide

/-- Paper: bridge:ewc-complement-symmetry -/
theorem paper_ewc_spectrum_five :
    exactWeightCount 5 0 = 1 ∧ exactWeightCount 5 1 = 1 ∧
    exactWeightCount 5 2 = 1 ∧ exactWeightCount 5 3 = 2 ∧
    exactWeightCount 5 4 = 1 ∧ exactWeightCount 5 5 = 2 ∧
    exactWeightCount 5 6 = 2 ∧ exactWeightCount 5 7 = 1 ∧
    exactWeightCount 5 8 = 3 ∧ exactWeightCount 5 9 = 2 ∧
    exactWeightCount 5 10 = 2 ∧ exactWeightCount 5 11 = 3 ∧
    exactWeightCount 5 12 = 1 :=
  ewc_spectrum_five

-- ══════════════════════════════════════════════════════════════
-- Phase R302: EWC spectrum at m=6
-- ══════════════════════════════════════════════════════════════

/-- EWC spectrum at m=6: complete weight distribution over range 0..32.
    prop:pom-ewc-spectrum -/
theorem ewc_spectrum_six :
    exactWeightCount 6 0 = 1 ∧ exactWeightCount 6 1 = 1 ∧
    exactWeightCount 6 2 = 1 ∧ exactWeightCount 6 3 = 2 ∧
    exactWeightCount 6 4 = 1 ∧ exactWeightCount 6 5 = 2 ∧
    exactWeightCount 6 6 = 2 ∧ exactWeightCount 6 7 = 1 ∧
    exactWeightCount 6 8 = 3 ∧ exactWeightCount 6 9 = 2 ∧
    exactWeightCount 6 10 = 2 ∧ exactWeightCount 6 11 = 3 ∧
    exactWeightCount 6 12 = 1 ∧ exactWeightCount 6 13 = 3 ∧
    exactWeightCount 6 14 = 3 ∧ exactWeightCount 6 15 = 2 ∧
    exactWeightCount 6 16 = 4 ∧ exactWeightCount 6 17 = 2 ∧
    exactWeightCount 6 18 = 3 ∧ exactWeightCount 6 19 = 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    native_decide

/-- EWC total for m=6: Σ_{n<33} ewc(6,n) = 2^6 = 64.
    prop:pom-ewc-spectrum -/
theorem ewc_sum_six :
    (Finset.range 33).sum (fun n => exactWeightCount 6 n) = 64 := by native_decide

/-- Paper package.
    prop:pom-ewc-spectrum -/
theorem paper_ewc_spectrum_six :
    exactWeightCount 6 0 = 1 ∧ exactWeightCount 6 1 = 1 ∧
    exactWeightCount 6 8 = 3 ∧ exactWeightCount 6 16 = 4 ∧
    exactWeightCount 6 32 = 1 ∧
    (Finset.range 33).sum (fun n => exactWeightCount 6 n) = 64 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- Fiber count reciprocity/reflection symmetry package.
    prop:fold-fiber-count-reciprocity -/
theorem paper_pom_fiber_reciprocity_package :
    (∀ (m : Nat) (_hm : 2 ≤ m), Function.Involutive (complementAction (m := m))) ∧
    (∀ (m : Nat) (_hm : 2 ≤ m) (x : X m),
      X.fiberMultiplicity (complementAction x) = X.fiberMultiplicity x) :=
  ⟨complementAction_involutive, fun _ _hm x => fiberMultiplicity_complementAction x _hm⟩

end Omega
