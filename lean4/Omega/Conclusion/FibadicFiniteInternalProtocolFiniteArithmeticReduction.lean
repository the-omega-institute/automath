import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete finite data for the finite internal fibadic protocol reduction.  The observable and
endomorphism families are finite, and each generator carries a finite conductor. -/
structure conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_Data where
  Observable : Type
  observableFintype : Fintype Observable
  Endomorphism : Type
  endomorphismFintype : Fintype Endomorphism
  observableConductor : Observable → ℕ
  endomorphismConductor : Endomorphism → ℕ

/-- The lcm of the finite observable conductors. -/
noncomputable def
    conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_observable_lcm
    (D : conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_Data) : ℕ :=
  letI := D.observableFintype
  Finset.lcm Finset.univ D.observableConductor

/-- The lcm of the finite endomorphism conductors. -/
noncomputable def
    conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_endomorphism_lcm
    (D : conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_Data) : ℕ :=
  letI := D.endomorphismFintype
  Finset.lcm Finset.univ D.endomorphismConductor

/-- The common modulus supporting all finite observables and continuous endomorphism reductions. -/
noncomputable def
    conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_common_modulus
    (D : conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_Data) : ℕ :=
  Nat.lcm
    (conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_observable_lcm D)
    (conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_endomorphism_lcm D)

/-- The finite protocols generated from the observable and endomorphism generators by the closure
operations appearing in the paper statement. -/
inductive conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_Protocol
    (D : conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_Data) where
  | observable : D.Observable →
      conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_Protocol D
  | endomorphism : D.Endomorphism →
      conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_Protocol D
  | compose :
      conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_Protocol D →
      conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_Protocol D →
      conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_Protocol D
  | product :
      conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_Protocol D →
      conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_Protocol D →
      conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_Protocol D
  | equality :
      conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_Protocol D →
      conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_Protocol D →
      conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_Protocol D
  | booleanNot :
      conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_Protocol D →
      conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_Protocol D
  | booleanAnd :
      conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_Protocol D →
      conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_Protocol D →
      conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_Protocol D

/-- The conductor assigned to a generated finite protocol.  Binary closure operations use the lcm
of the input conductors; Boolean negation preserves the input conductor. -/
noncomputable def
    conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_protocol_conductor
    {D : conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_Data} :
    conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_Protocol D → ℕ
  | .observable v => D.observableConductor v
  | .endomorphism T => D.endomorphismConductor T
  | .compose P Q =>
      Nat.lcm
        (conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_protocol_conductor P)
        (conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_protocol_conductor Q)
  | .product P Q =>
      Nat.lcm
        (conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_protocol_conductor P)
        (conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_protocol_conductor Q)
  | .equality P Q =>
      Nat.lcm
        (conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_protocol_conductor P)
        (conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_protocol_conductor Q)
  | .booleanNot P =>
      conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_protocol_conductor P
  | .booleanAnd P Q =>
      Nat.lcm
        (conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_protocol_conductor P)
        (conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_protocol_conductor Q)

/-- All finite-valued observables factor through the common lcm modulus. -/
noncomputable def
    conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_Data.observables_factor_through_common_modulus
    (D : conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_Data) : Prop :=
  ∀ v : D.Observable,
    D.observableConductor v ∣
      conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_common_modulus D

/-- All continuous endomorphism generators reduce modulo the common lcm modulus. -/
noncomputable def
    conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_Data.endomorphisms_reduce_mod_common_modulus
    (D : conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_Data) : Prop :=
  ∀ T : D.Endomorphism,
    D.endomorphismConductor T ∣
      conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_common_modulus D

/-- Every finite protocol generated by composition, products, equality tests, and Boolean
operations reduces to arithmetic modulo the common lcm modulus. -/
noncomputable def
    conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_Data.generated_protocols_reduce_to_finite_arithmetic
    (D : conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_Data) : Prop :=
  ∀ P : conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_Protocol D,
    conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_protocol_conductor P ∣
      conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_common_modulus D

theorem
    conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_observable_dvd_common
    (D : conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_Data)
    (v : D.Observable) :
    D.observableConductor v ∣
      conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_common_modulus D := by
  letI := D.observableFintype
  have hv :
      D.observableConductor v ∣
        conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_observable_lcm D :=
    Finset.dvd_lcm (Finset.mem_univ v)
  exact dvd_trans hv (Nat.dvd_lcm_left _ _)

theorem
    conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_endomorphism_dvd_common
    (D : conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_Data)
    (T : D.Endomorphism) :
    D.endomorphismConductor T ∣
      conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_common_modulus D := by
  letI := D.endomorphismFintype
  have hT :
      D.endomorphismConductor T ∣
        conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_endomorphism_lcm D :=
    Finset.dvd_lcm (Finset.mem_univ T)
  exact dvd_trans hT (Nat.dvd_lcm_right _ _)

theorem
    conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_protocol_dvd_common
    (D : conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_Data)
    (P : conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_Protocol D) :
    conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_protocol_conductor P ∣
      conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_common_modulus D := by
  induction P with
  | observable v =>
      exact
        conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_observable_dvd_common
          D v
  | endomorphism T =>
      exact
        conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_endomorphism_dvd_common
          D T
  | compose P Q hP hQ =>
      exact Nat.lcm_dvd hP hQ
  | product P Q hP hQ =>
      exact Nat.lcm_dvd hP hQ
  | equality P Q hP hQ =>
      exact Nat.lcm_dvd hP hQ
  | booleanNot P hP =>
      exact hP
  | booleanAnd P Q hP hQ =>
      exact Nat.lcm_dvd hP hQ

/-- Paper label:
`thm:conclusion-fibadic-finite-internal-protocol-finite-arithmetic-reduction`. -/
theorem paper_conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction
    (D : conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_Data) :
    D.observables_factor_through_common_modulus ∧
      D.endomorphisms_reduce_mod_common_modulus ∧
        D.generated_protocols_reduce_to_finite_arithmetic := by
  refine ⟨?_, ?_, ?_⟩
  · intro v
    exact
      conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_observable_dvd_common
        D v
  · intro T
    exact
      conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_endomorphism_dvd_common
        D T
  · intro P
    exact
      conclusion_fibadic_finite_internal_protocol_finite_arithmetic_reduction_protocol_dvd_common
        D P

end Omega.Conclusion
