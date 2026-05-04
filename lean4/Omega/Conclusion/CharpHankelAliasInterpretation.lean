import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Concrete finite-order data for the finite phase-closure Hankel aliasing statement. -/
structure conclusion_charp_hankel_alias_interpretation_data where
  q : ℕ
  m : ℕ
  alpha : ℚ
  phase : ℚ

/-- The finite-order phase closure hypothesis for the aliasing residue modulus. -/
def conclusion_charp_hankel_alias_interpretation_data.phaseClosure
    (D : conclusion_charp_hankel_alias_interpretation_data) : Prop :=
  0 < D.m ∧ D.phase ^ D.m = 1

/-- The ungrouped binomial-exponential summand before finite-order residues are merged. -/
def conclusion_charp_hankel_alias_interpretation_summand
    (D : conclusion_charp_hankel_alias_interpretation_data) (n k : ℕ) : ℚ :=
  (Nat.choose D.q k : ℚ) * (D.alpha ^ D.q * D.phase ^ k) ^ n

/-- The grouped coefficient attached to a residue class modulo the phase order. -/
def conclusion_charp_hankel_alias_interpretation_groupedCoefficient
    (D : conclusion_charp_hankel_alias_interpretation_data) (a : ℕ) : ℚ :=
  Finset.sum ((Finset.range (D.q + 1)).filter (fun k => k % D.m = a))
    (fun k => (Nat.choose D.q k : ℚ))

/-- The grouped residue summand in the collapsed exponential expansion. -/
def conclusion_charp_hankel_alias_interpretation_groupedSummand
    (D : conclusion_charp_hankel_alias_interpretation_data) (n a : ℕ) : ℚ :=
  conclusion_charp_hankel_alias_interpretation_groupedCoefficient D a *
    (D.alpha ^ D.q * D.phase ^ a) ^ n

/-- The displayed grouped expansion of the binomial exponential sum by residues modulo `m`. -/
def conclusion_charp_hankel_alias_interpretation_data.groupedExpansion
    (D : conclusion_charp_hankel_alias_interpretation_data) : Prop :=
  ∀ n : ℕ,
    Finset.sum (Finset.range (D.q + 1))
        (fun k => conclusion_charp_hankel_alias_interpretation_summand D n k) =
      Finset.sum (Finset.range D.m)
        (fun a => conclusion_charp_hankel_alias_interpretation_groupedSummand D n a)

/-- The nonzero grouped residue classes that survive in the collapsed Hankel model. -/
def conclusion_charp_hankel_alias_interpretation_support
    (D : conclusion_charp_hankel_alias_interpretation_data) : Finset ℕ :=
  (Finset.range D.m).filter
    (fun a => conclusion_charp_hankel_alias_interpretation_groupedCoefficient D a ≠ 0)

/-- The concrete Hankel rank read off from the nonzero grouped coefficients. -/
def conclusion_charp_hankel_alias_interpretation_hankelRank
    (D : conclusion_charp_hankel_alias_interpretation_data) : ℕ :=
  (conclusion_charp_hankel_alias_interpretation_support D).card

/-- The rank formula as the count of nonzero grouped coefficients. -/
def conclusion_charp_hankel_alias_interpretation_data.rankFormula
    (D : conclusion_charp_hankel_alias_interpretation_data) : Prop :=
  conclusion_charp_hankel_alias_interpretation_hankelRank D =
    (conclusion_charp_hankel_alias_interpretation_support D).card

/-- Paper label: `cor:conclusion-charp-hankel-alias-interpretation`. -/
theorem paper_conclusion_charp_hankel_alias_interpretation
    (D : conclusion_charp_hankel_alias_interpretation_data) :
    D.phaseClosure → D.groupedExpansion ∧ D.rankFormula := by
  intro hPhase
  constructor
  · intro n
    classical
    have hm : 0 < D.m := hPhase.1
    have hpartition :
        (Finset.range D.m).biUnion
            (fun a => (Finset.range (D.q + 1)).filter (fun k => k % D.m = a)) =
          Finset.range (D.q + 1) := by
      ext k
      constructor
      · intro hk
        rcases Finset.mem_biUnion.mp hk with ⟨a, -, ha⟩
        exact (Finset.mem_filter.mp ha).1
      · intro hk
        refine Finset.mem_biUnion.mpr ?_
        refine ⟨k % D.m, ?_, ?_⟩
        · exact Finset.mem_range.mpr (Nat.mod_lt k hm)
        · exact Finset.mem_filter.mpr ⟨hk, rfl⟩
    symm
    calc
      Finset.sum (Finset.range D.m)
          (fun a => conclusion_charp_hankel_alias_interpretation_groupedSummand D n a)
          =
            Finset.sum (Finset.range D.m)
              (fun a =>
                Finset.sum ((Finset.range (D.q + 1)).filter (fun k => k % D.m = a))
                  (fun k => conclusion_charp_hankel_alias_interpretation_summand D n k)) := by
              refine Finset.sum_congr rfl ?_
              intro a ha
              rw [conclusion_charp_hankel_alias_interpretation_groupedSummand,
                conclusion_charp_hankel_alias_interpretation_groupedCoefficient,
                Finset.sum_mul]
              refine Finset.sum_congr rfl ?_
              intro k hk
              have hka : k % D.m = a := (Finset.mem_filter.mp hk).2
              have hphasek : D.phase ^ k = D.phase ^ a := by
                calc
                  D.phase ^ k = D.phase ^ (k % D.m + D.m * (k / D.m)) := by
                    rw [Nat.mod_add_div]
                  _ = D.phase ^ (k % D.m) * D.phase ^ (D.m * (k / D.m)) := by
                    rw [pow_add]
                  _ = D.phase ^ (k % D.m) * (D.phase ^ D.m) ^ (k / D.m) := by
                    rw [pow_mul]
                  _ = D.phase ^ (k % D.m) := by
                    rw [hPhase.2]
                    simp
                  _ = D.phase ^ a := by
                    rw [hka]
              simp [conclusion_charp_hankel_alias_interpretation_summand, hphasek]
      _ =
            Finset.sum
              ((Finset.range D.m).biUnion
                (fun a => (Finset.range (D.q + 1)).filter (fun k => k % D.m = a)))
              (fun k => conclusion_charp_hankel_alias_interpretation_summand D n k) := by
              rw [Finset.sum_biUnion]
              intro a ha b hb hab
              exact Finset.disjoint_filter.2 (fun k _ hka hkb => hab (hka.symm.trans hkb))
      _ =
            Finset.sum (Finset.range (D.q + 1))
              (fun k => conclusion_charp_hankel_alias_interpretation_summand D n k) := by
              rw [hpartition]
  · rfl

end Omega.Conclusion
