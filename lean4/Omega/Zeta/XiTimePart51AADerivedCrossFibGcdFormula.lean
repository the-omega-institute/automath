import Mathlib.Tactic
import Omega.Core.Fib

namespace Omega.Zeta

/-- Chapter-local data for the multi-window derived-cross Fibonacci gcd seed model. The list
`windows` records the window parameters `m_i`. -/
structure XiDerivedCrossFibGcdFormulaData where
  windows : List ℕ

/-- The modulus attached to the window `m` in the seed model. -/
def fibWindowModulus (m : ℕ) : ℕ :=
  Nat.fib (m + 2)

def XiDerivedCrossFibGcdFormulaData.shiftedWindows (D : XiDerivedCrossFibGcdFormulaData) :
    List ℕ :=
  D.windows.map (· + 2)

def XiDerivedCrossFibGcdFormulaData.moduli (D : XiDerivedCrossFibGcdFormulaData) : List ℕ :=
  D.windows.map fibWindowModulus

def XiDerivedCrossFibGcdFormulaData.modulusGcd (D : XiDerivedCrossFibGcdFormulaData) : ℕ :=
  D.moduli.foldr Nat.gcd 0

def XiDerivedCrossFibGcdFormulaData.indexGcd (D : XiDerivedCrossFibGcdFormulaData) : ℕ :=
  D.shiftedWindows.foldr Nat.gcd 0

def XiDerivedCrossFibGcdFormulaData.homologyMultiplicity (D : XiDerivedCrossFibGcdFormulaData)
    (q : ℕ) : ℕ :=
  Nat.choose (D.windows.length - 1) q

/-- The Smith-reduced leading invariant divides every Fibonacci modulus in the row vector. -/
def XiDerivedCrossFibGcdFormulaData.koszulSmithReduction
    (D : XiDerivedCrossFibGcdFormulaData) : Prop :=
  ∀ N ∈ D.moduli, D.modulusGcd ∣ N

/-- The gcd of the Fibonacci moduli collapses to the Fibonacci number indexed by the gcd of the
shifted window parameters. -/
def XiDerivedCrossFibGcdFormulaData.fibGcdCollapse
    (D : XiDerivedCrossFibGcdFormulaData) : Prop :=
  D.modulusGcd = Nat.fib D.indexGcd

/-- The seed homology multiplicity is the binomial coefficient predicted by the exterior-power
factor `K(0)^(r-1)`. -/
def XiDerivedCrossFibGcdFormulaData.derivedHomologyClosedForm
    (D : XiDerivedCrossFibGcdFormulaData) : Prop :=
  ∀ q, D.homologyMultiplicity q = Nat.choose (D.windows.length - 1) q

private lemma foldr_gcd_dvd_of_mem : ∀ {L : List ℕ} {a : ℕ}, a ∈ L → L.foldr Nat.gcd 0 ∣ a
  | [], _, h => by cases h
  | b :: bs, a, h => by
      rcases List.mem_cons.mp h with rfl | htail
      · exact Nat.gcd_dvd_left _ _
      · exact dvd_trans (Nat.gcd_dvd_right _ _) (foldr_gcd_dvd_of_mem htail)

private lemma fib_foldr_gcd (L : List ℕ) :
    (L.map Nat.fib).foldr Nat.gcd 0 = Nat.fib (L.foldr Nat.gcd 0) := by
  induction L with
  | nil =>
      simp
  | cons a as ih =>
      simp [ih, Omega.fib_gcd]

/-- In the seed list-based model of the multi-window derived tensor product, the gcd of the
Fibonacci moduli is the Smith invariant of the Koszul row, it collapses to the Fibonacci number
at the gcd of the shifted window indices, and the homology multiplicities are the expected
binomial coefficients.
    thm:xi-time-part51aa-derived-cross-fib-gcd-formula -/
theorem paper_xi_time_part51aa_derived_cross_fib_gcd_formula
    (D : XiDerivedCrossFibGcdFormulaData) :
    D.koszulSmithReduction ∧ D.fibGcdCollapse ∧ D.derivedHomologyClosedForm := by
  refine ⟨?_, ?_, ?_⟩
  · intro N hN
    exact foldr_gcd_dvd_of_mem hN
  · simpa [XiDerivedCrossFibGcdFormulaData.fibGcdCollapse,
      XiDerivedCrossFibGcdFormulaData.modulusGcd,
      XiDerivedCrossFibGcdFormulaData.indexGcd,
      XiDerivedCrossFibGcdFormulaData.moduli,
      XiDerivedCrossFibGcdFormulaData.shiftedWindows,
      fibWindowModulus] using fib_foldr_gcd D.shiftedWindows
  · intro q
    rfl

end Omega.Zeta
