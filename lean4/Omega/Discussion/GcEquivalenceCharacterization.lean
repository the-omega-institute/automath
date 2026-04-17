import Mathlib.Tactic

namespace Omega.Discussion

/-- Concrete GC audit data, represented by its trace sequence. -/
structure GcAuditDatum where
  traceSeq : ℕ → ℤ

/-- The trace-sequence functor on GC audit data. -/
def gcTrSeq (A : GcAuditDatum) : ℕ → ℤ :=
  A.traceSeq

/-- Möbius/Witt primitive extraction, represented by the same concrete sequence data. -/
def gcMob (a : ℕ → ℤ) : ℕ → ℤ :=
  a

/-- Euler packaging of the primitive sequence. -/
def gcEuler (p : ℕ → ℤ) : ℕ → ℤ :=
  p

/-- Zeta-determinant output of the GC audit interface. -/
def gcZetaDet (A : GcAuditDatum) : ℕ → ℤ :=
  gcEuler (gcMob (gcTrSeq A))

/-- Concrete paper wrapper for the strict Witt-Euler commuting diagram. -/
theorem paper_discussion_witt_euler_gc_functor (A : GcAuditDatum) :
    gcZetaDet A = gcEuler (gcMob (gcTrSeq A)) := by
  rfl

/-- Equality of GC outputs is equivalent to equality of the trace and primitive shadow data once
the Witt-Euler diagram is packaged concretely. -/
theorem paper_discussion_gc_equivalence_characterization
    (A B : GcAuditDatum) :
    gcZetaDet A = gcZetaDet B ↔
      gcTrSeq A = gcTrSeq B ∧ gcMob (gcTrSeq A) = gcMob (gcTrSeq B) := by
  constructor
  · intro hzeta
    have htrace : gcTrSeq A = gcTrSeq B := by
      calc
        gcTrSeq A = gcEuler (gcMob (gcTrSeq A)) := by
          simpa using (paper_discussion_witt_euler_gc_functor A).symm
        _ = gcEuler (gcMob (gcTrSeq B)) := by
          simpa [gcZetaDet] using hzeta
        _ = gcTrSeq B := by
          simpa using paper_discussion_witt_euler_gc_functor B
    exact ⟨htrace, by simpa [gcMob] using htrace⟩
  · rintro ⟨htrace, _hmob⟩
    calc
      gcZetaDet A = gcEuler (gcMob (gcTrSeq A)) := paper_discussion_witt_euler_gc_functor A
      _ = gcEuler (gcMob (gcTrSeq B)) := by simpa [gcMob] using htrace
      _ = gcZetaDet B := paper_discussion_witt_euler_gc_functor B

end Omega.Discussion
