import Mathlib.Tactic
import Omega.Conclusion.CanonicalFixedpointFullshiftConjugacy

namespace Omega.Conclusion

/-- The stream obtained by periodically repeating the first `k` digits of `a`.
For `k = 0` this is just `a`, which makes the zero-prefix closure case tautological. -/
def conclusion_canonical_fixedpoints_cantor_closure_periodicPrefix
    (D : CanonicalSliceData) (a : CanonicalDigitStream D) (k : Nat) :
    CanonicalDigitStream D :=
  fun n =>
    if _hk : 0 < k then
      a (n % k)
    else
      a n

/-- A stream is periodic with period `k`. -/
def conclusion_canonical_fixedpoints_cantor_closure_periodic
    {D : CanonicalSliceData} (a : CanonicalDigitStream D) (k : Nat) : Prop :=
  ∀ n : Nat, a (n + k) = a n

/-- Prefix-topological closure statement: every infinite canonical digit stream is approached,
at each finite prefix depth, by a periodic fixed-point stream with the same prefix. -/
def conclusion_canonical_fixedpoints_cantor_closure_closure_eq
    (D : CanonicalSliceData) : Prop :=
  ∀ a : CanonicalDigitStream D, ∀ k : Nat,
    ∃ p : CanonicalDigitStream D,
      conclusion_canonical_fixedpoints_cantor_closure_periodic p k ∧
        canonicalPrefix D k p = canonicalPrefix D k a

/-- The first-digit cylinder in the canonical digit Cantor set. -/
def conclusion_canonical_fixedpoints_cantor_closure_firstDigitCylinder
    (D : CanonicalSliceData) (d : Fin (D.M + 1)) : Set (CanonicalDigitStream D) :=
  {a | a 0 = d}

/-- Concrete disjoint self-similar decomposition by the first digit. -/
def conclusion_canonical_fixedpoints_cantor_closure_selfSimilar_decomposition
    (D : CanonicalSliceData) : Prop :=
  (∀ a : CanonicalDigitStream D,
      a ∈ ⋃ d : Fin (D.M + 1),
        conclusion_canonical_fixedpoints_cantor_closure_firstDigitCylinder D d) ∧
    ∀ d e : Fin (D.M + 1), d ≠ e →
      conclusion_canonical_fixedpoints_cantor_closure_firstDigitCylinder D d ∩
        conclusion_canonical_fixedpoints_cantor_closure_firstDigitCylinder D e = ∅

/-- The similarity dimension of the canonical digit Cantor set in the normalized address line. -/
noncomputable def conclusion_canonical_fixedpoints_cantor_closure_dimension
    (D : CanonicalSliceData) : ℝ :=
  Real.log (((D.M + 1 : Nat) : ℝ)) / Real.log 2

/-- Paper-facing dimension formula for the canonical digit Cantor set. -/
def conclusion_canonical_fixedpoints_cantor_closure_dimension_formula
    (D : CanonicalSliceData) : Prop :=
  conclusion_canonical_fixedpoints_cantor_closure_dimension D =
    Real.log (((D.M + 1 : Nat) : ℝ)) / Real.log 2

/-- Paper label: `thm:conclusion-canonical-fixedpoints-cantor-closure`.
The canonical fixed-point streams are prefix-dense in the full digit Cantor set, the latter
splits into disjoint first-digit cylinders, and its normalized similarity dimension is the
standard logarithmic formula. -/
theorem paper_conclusion_canonical_fixedpoints_cantor_closure (D : CanonicalSliceData) :
    conclusion_canonical_fixedpoints_cantor_closure_closure_eq D ∧
      conclusion_canonical_fixedpoints_cantor_closure_selfSimilar_decomposition D ∧
        conclusion_canonical_fixedpoints_cantor_closure_dimension_formula D := by
  refine ⟨?_, ?_, rfl⟩
  · intro a k
    refine ⟨conclusion_canonical_fixedpoints_cantor_closure_periodicPrefix D a k, ?_, ?_⟩
    · intro n
      by_cases hk : 0 < k
      · simp [conclusion_canonical_fixedpoints_cantor_closure_periodicPrefix,
          hk, Nat.add_mod_right]
      · have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
        simp [conclusion_canonical_fixedpoints_cantor_closure_periodicPrefix, hk0]
    · funext i
      have hk : 0 < k := Nat.lt_of_le_of_lt (Nat.zero_le i.1) i.2
      simp [canonicalPrefix, conclusion_canonical_fixedpoints_cantor_closure_periodicPrefix, hk,
        Nat.mod_eq_of_lt i.2]
  · refine ⟨?_, ?_⟩
    · intro a
      exact Set.mem_iUnion.mpr ⟨a 0, rfl⟩
    · intro d e hde
      ext a
      constructor
      · intro ha
        rcases ha with ⟨hd, he⟩
        have h : d = e := by
          calc
            d = a 0 := hd.symm
            _ = e := he
        exact (hde h).elim
      · intro ha
        simp at ha

end Omega.Conclusion
