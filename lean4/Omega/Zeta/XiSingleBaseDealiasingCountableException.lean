import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Set.Countable
import Mathlib.Tactic

namespace Omega.Zeta

/-- The single-base phase code attached to the exponent `s`. -/
noncomputable def xiSingleBasePhase (b : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (-(s - (1 / 2 : ℂ)) * Complex.log b)

/-- Collision bases for a fixed distinct pair are parameterized by the integer winding number when
the real parts coincide, and are empty otherwise. -/
def xiSingleBaseCollisionBases (s s' : ℂ) : Set ℝ :=
  if _h : (s - s').re = 0 then
    Set.range fun k : ℤ => Real.exp (-((k : ℝ) * (2 * Real.pi)) / (s - s').im)
  else
    ∅

/-- Distinct pairs from the countable set `S`. -/
def xiSingleBaseDistinctPairs (S : Set ℂ) : Set (ℂ × ℂ) :=
  {p | p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 ≠ p.2}

/-- The countable exceptional set of bases where two distinct phases can collide. -/
def xiSingleBaseExceptionalBases (S : Set ℂ) : Set ℝ :=
  ⋃ p ∈ xiSingleBaseDistinctPairs S, xiSingleBaseCollisionBases p.1 p.2

theorem xiSingleBaseCollisionBases_countable (s s' : ℂ) :
    (xiSingleBaseCollisionBases s s').Countable := by
  by_cases h : (s - s').re = 0
  · have h' : s.re - s'.re = 0 := by simpa [Complex.sub_re] using h
    simpa [xiSingleBaseCollisionBases, h'] using Set.countable_range
      (fun k : ℤ => Real.exp (-((k : ℝ) * (2 * Real.pi)) / (s - s').im))
  · have h' : s.re - s'.re ≠ 0 := by simpa [Complex.sub_re] using h
    simp [xiSingleBaseCollisionBases, h']

theorem mem_xiSingleBaseCollisionBases_of_collision
    {s s' : ℂ} (hss : s ≠ s')
    {b : ℝ} (hb : 1 < b)
    (hcollision : xiSingleBasePhase b s = xiSingleBasePhase b s') :
    b ∈ xiSingleBaseCollisionBases s s' := by
  have hb0 : 0 < b := lt_trans zero_lt_one hb
  have hlogc : Complex.log (b : ℂ) = (Real.log b : ℂ) := by
    simpa using (Complex.ofReal_log (le_of_lt hb0)).symm
  have hperiod :
      ∃ n : ℤ,
        -(s - (1 / 2 : ℂ)) * Complex.log b =
          -(s' - (1 / 2 : ℂ)) * Complex.log b + n * (2 * Real.pi * Complex.I) := by
    simpa [xiSingleBasePhase] using (Complex.exp_eq_exp_iff_exists_int).mp hcollision
  rcases hperiod with ⟨n, hn⟩
  have hsub :
      -(s - (1 / 2 : ℂ)) * Complex.log b - (-(s' - (1 / 2 : ℂ)) * Complex.log b) =
        n * (2 * Real.pi * Complex.I) := by
    rw [hn]
    ring
  have hEq : -(s - s') * (Real.log b : ℂ) = n * (2 * Real.pi * Complex.I) := by
    calc
      -(s - s') * (Real.log b : ℂ) =
          (-(s - (1 / 2 : ℂ)) * Complex.log b) - (-(s' - (1 / 2 : ℂ)) * Complex.log b) := by
        rw [hlogc]
        ring
      _ = n * (2 * Real.pi * Complex.I) := hsub
  have hre : (-(s - s') * (Real.log b : ℂ)).re = 0 := by
    simpa using congrArg Complex.re hEq
  have hmulre : -(s - s').re * Real.log b = 0 := by
    simpa [Complex.mul_re] using hre
  have hlogpos : 0 < Real.log b := Real.log_pos hb
  have hre_zero : (s - s').re = 0 := by
    nlinarith
  have him : (-(s - s') * (Real.log b : ℂ)).im = (n : ℝ) * (2 * Real.pi) := by
    simpa using congrArg Complex.im hEq
  have hmulim : -(s - s').im * Real.log b = (n : ℝ) * (2 * Real.pi) := by
    simpa [Complex.mul_im, hre_zero] using him
  have him_ne : (s - s').im ≠ 0 := by
    intro him_zero
    have hzero : s - s' = 0 := by
      apply Complex.ext <;> simp [hre_zero, him_zero]
    exact hss (sub_eq_zero.mp hzero)
  have hlog_formula : Real.log b = -((n : ℝ) * (2 * Real.pi)) / (s - s').im := by
    field_simp [him_ne]
    nlinarith [hmulim]
  have hmem :
      b ∈ Set.range (fun k : ℤ => Real.exp (-((k : ℝ) * (2 * Real.pi)) / (s - s').im)) := by
    refine ⟨n, ?_⟩
    rw [← Real.exp_log hb0, hlog_formula]
  simpa [xiSingleBaseCollisionBases, hre_zero] using hmem

theorem xiSingleBaseDistinctPairs_countable {S : Set ℂ} (hS : S.Countable) :
    (xiSingleBaseDistinctPairs S).Countable := by
  refine (hS.prod hS).mono ?_
  intro p hp
  simpa [Set.mem_prod, xiSingleBaseDistinctPairs] using And.intro hp.1 hp.2.1

theorem xiSingleBaseExceptionalBases_countable {S : Set ℂ} (hS : S.Countable) :
    (xiSingleBaseExceptionalBases S).Countable := by
  have hPairs : (xiSingleBaseDistinctPairs S).Countable :=
    xiSingleBaseDistinctPairs_countable hS
  simpa [xiSingleBaseExceptionalBases] using
    hPairs.biUnion fun p _ => xiSingleBaseCollisionBases_countable p.1 p.2

theorem mem_xiSingleBaseExceptionalBases_of_collision
    {S : Set ℂ} {s s' : ℂ}
    (hs : s ∈ S) (hs' : s' ∈ S) (hss : s ≠ s')
    {b : ℝ} (hb : 1 < b)
    (hcollision : xiSingleBasePhase b s = xiSingleBasePhase b s') :
    b ∈ xiSingleBaseExceptionalBases S := by
  refine Set.mem_iUnion.2 ⟨(s, s'), Set.mem_iUnion.2 ⟨⟨hs, hs', hss⟩, ?_⟩⟩
  exact mem_xiSingleBaseCollisionBases_of_collision hss hb hcollision

/-- Paper label: `thm:xi-single-base-dealiasing-countable-exception`. Every distinct pair in the
countable set contributes at most countably many collision bases, so the union of all collision
bases is countable and the phase code is injective off that exceptional set. -/
theorem paper_xi_single_base_dealiasing_countable_exception
    (S : Set ℂ) (hS : S.Countable) :
    (xiSingleBaseExceptionalBases S).Countable ∧
      ∀ ⦃b : ℝ⦄, 1 < b → b ∉ xiSingleBaseExceptionalBases S →
        Set.InjOn (xiSingleBasePhase b) S := by
  refine ⟨xiSingleBaseExceptionalBases_countable hS, ?_⟩
  intro b hb hbnot s hs s' hs' hphase
  by_cases hss : s = s'
  · exact hss
  · exfalso
    exact hbnot (mem_xiSingleBaseExceptionalBases_of_collision hs hs' hss hb hphase)

end Omega.Zeta
