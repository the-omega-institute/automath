import Mathlib.Tactic

namespace Omega.Conclusion

/-- Coordinatewise idempotence in a finite diagonal algebra supported on `active`. -/
def conclusion_fibadic_finite_layer_gcd_primitive_central_idempotents_idempotent
    {ι : Type*} [DecidableEq ι] (active : Finset ι) (coeff : ι → ℤ) : Prop :=
  ∀ d ∈ active, coeff d * coeff d = coeff d

/-- The active support of a diagonal coefficient vector. -/
def conclusion_fibadic_finite_layer_gcd_primitive_central_idempotents_support
    {ι : Type*} [DecidableEq ι] (active : Finset ι) (coeff : ι → ℤ) : Finset ι :=
  active.filter fun d => coeff d ≠ 0

/-- A primitive central idempotent in the finite diagonal model has singleton active support. -/
def conclusion_fibadic_finite_layer_gcd_primitive_central_idempotents_primitiveCentral
    {ι : Type*} [DecidableEq ι] (active : Finset ι) (coeff : ι → ℤ) : Prop :=
  conclusion_fibadic_finite_layer_gcd_primitive_central_idempotents_idempotent active coeff ∧
    (conclusion_fibadic_finite_layer_gcd_primitive_central_idempotents_support active coeff).card =
      1

lemma conclusion_fibadic_finite_layer_gcd_primitive_central_idempotents_int_idempotent
    (c : ℤ) (h : c * c = c) : c = 0 ∨ c = 1 := by
  have hmul : c * (c - 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hmul with hc | hc
  · exact Or.inl hc
  · exact Or.inr (sub_eq_zero.mp hc)

lemma conclusion_fibadic_finite_layer_gcd_primitive_central_idempotents_idempotent_iff
    {ι : Type*} [DecidableEq ι] (active : Finset ι) (coeff : ι → ℤ) :
    conclusion_fibadic_finite_layer_gcd_primitive_central_idempotents_idempotent
        active coeff ↔
      ∃ S : Finset ι, S ⊆ active ∧
        ∀ d ∈ active, coeff d = if d ∈ S then 1 else 0 := by
  constructor
  · intro hidem
    refine ⟨active.filter fun d => coeff d = 1, ?_, ?_⟩
    · intro d hd
      exact (Finset.mem_filter.mp hd).1
    · intro d hd
      have h01 :=
        conclusion_fibadic_finite_layer_gcd_primitive_central_idempotents_int_idempotent
          (coeff d) (hidem d hd)
      rcases h01 with hzero | hone
      · simp [hd, hzero]
      · simp [hd, hone]
  · rintro ⟨S, _hS, hcoord⟩ d hd
    rw [hcoord d hd]
    by_cases hmem : d ∈ S <;> simp [hmem]

lemma conclusion_fibadic_finite_layer_gcd_primitive_central_idempotents_primitive_iff
    {ι : Type*} [DecidableEq ι] (active : Finset ι) (coeff : ι → ℤ) :
    conclusion_fibadic_finite_layer_gcd_primitive_central_idempotents_primitiveCentral
        active coeff ↔
      ∃ d ∈ active, ∀ e ∈ active, coeff e = if e = d then 1 else 0 := by
  constructor
  · rintro ⟨hidem, hcard⟩
    rcases Finset.card_eq_one.mp hcard with ⟨d, hsupport_eq⟩
    have hdsupport :
        d ∈
          conclusion_fibadic_finite_layer_gcd_primitive_central_idempotents_support
            active coeff := by
      simp [hsupport_eq]
    have hdactive : d ∈ active := by
      exact (Finset.mem_filter.mp hdsupport).1
    have hdnonzero : coeff d ≠ 0 := by
      exact (Finset.mem_filter.mp hdsupport).2
    refine ⟨d, hdactive, ?_⟩
    intro e heactive
    by_cases hed : e = d
    · have henonzero : coeff e ≠ 0 := by
        simpa [hed] using hdnonzero
      have h01 :=
        conclusion_fibadic_finite_layer_gcd_primitive_central_idempotents_int_idempotent
          (coeff e) (hidem e heactive)
      rcases h01 with hzero | hone
      · exact (henonzero hzero).elim
      · simpa [hed] using hone
    · have henonzero_false : ¬ coeff e ≠ 0 := by
        intro henonzero
        have hesupport :
            e ∈
              conclusion_fibadic_finite_layer_gcd_primitive_central_idempotents_support
                active coeff := by
          exact Finset.mem_filter.mpr ⟨heactive, henonzero⟩
        have : e = d := by
          simpa [hsupport_eq] using hesupport
        exact hed this
      have hzero : coeff e = 0 := by simpa using henonzero_false
      simp [hed, hzero]
  · rintro ⟨d, hdactive, hcoord⟩
    have hidem :
        conclusion_fibadic_finite_layer_gcd_primitive_central_idempotents_idempotent
          active coeff := by
      intro e heactive
      rw [hcoord e heactive]
      by_cases hed : e = d <;> simp [hed]
    refine ⟨hidem, ?_⟩
    apply Finset.card_eq_one.mpr
    refine ⟨d, ?_⟩
    ext e
    constructor
    · intro hesupport
      have heactive : e ∈ active := (Finset.mem_filter.mp hesupport).1
      have henonzero : coeff e ≠ 0 := (Finset.mem_filter.mp hesupport).2
      by_cases hed : e = d
      · simp [hed]
      · have hzero : coeff e = 0 := by simpa [hed] using hcoord e heactive
        exact (henonzero hzero).elim
    · intro hed
      have hed_eq : e = d := by simpa using hed
      have heactive : e ∈ active := by simpa [hed_eq] using hdactive
      have hcoeff : coeff e = 1 := by simpa [hed_eq] using hcoord d hdactive
      exact Finset.mem_filter.mpr ⟨heactive, by simp [hcoeff]⟩

/-- Paper-facing statement for
`thm:conclusion-fibadic-finite-layer-gcd-primitive-central-idempotents`. -/
def conclusion_fibadic_finite_layer_gcd_primitive_central_idempotents_statement : Prop :=
  ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (active : Finset ι),
    (∀ coeff : ι → ℤ,
      conclusion_fibadic_finite_layer_gcd_primitive_central_idempotents_idempotent
          active coeff ↔
        ∃ S : Finset ι, S ⊆ active ∧
          ∀ d ∈ active, coeff d = if d ∈ S then 1 else 0) ∧
      (∀ coeff : ι → ℤ,
        conclusion_fibadic_finite_layer_gcd_primitive_central_idempotents_primitiveCentral
            active coeff ↔
          ∃ d ∈ active, ∀ e ∈ active, coeff e = if e = d then 1 else 0)

/-- Paper label: `thm:conclusion-fibadic-finite-layer-gcd-primitive-central-idempotents`. -/
theorem paper_conclusion_fibadic_finite_layer_gcd_primitive_central_idempotents :
    conclusion_fibadic_finite_layer_gcd_primitive_central_idempotents_statement := by
  intro ι _fintype _decEq active
  exact
    ⟨fun coeff =>
      conclusion_fibadic_finite_layer_gcd_primitive_central_idempotents_idempotent_iff
        active coeff,
      fun coeff =>
        conclusion_fibadic_finite_layer_gcd_primitive_central_idempotents_primitive_iff
          active coeff⟩

end Omega.Conclusion
