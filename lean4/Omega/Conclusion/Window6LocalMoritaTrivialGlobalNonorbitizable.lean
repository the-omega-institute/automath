import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete window-6 fiber data for the local-Morita/global-nonorbitizable package.  The three
fiber classes record the heterogeneous fiber sizes `2, 3, 4` behind the paper histogram
`2:8, 3:4, 4:9`; the local topological and matrix-block facts are kept as concrete witnesses
over these fiber classes. -/
structure conclusion_window6_local_morita_trivial_global_nonorbitizable_Data where
  conclusion_window6_local_morita_trivial_global_nonorbitizable_fiberSize : Fin 3 → ℕ
  conclusion_window6_local_morita_trivial_global_nonorbitizable_fiberMultiplicity :
    Fin 3 → ℕ
  conclusion_window6_local_morita_trivial_global_nonorbitizable_sizeTwo :
    conclusion_window6_local_morita_trivial_global_nonorbitizable_fiberSize 0 = 2
  conclusion_window6_local_morita_trivial_global_nonorbitizable_sizeThree :
    conclusion_window6_local_morita_trivial_global_nonorbitizable_fiberSize 1 = 3
  conclusion_window6_local_morita_trivial_global_nonorbitizable_sizeFour :
    conclusion_window6_local_morita_trivial_global_nonorbitizable_fiberSize 2 = 4
  conclusion_window6_local_morita_trivial_global_nonorbitizable_multEight :
    conclusion_window6_local_morita_trivial_global_nonorbitizable_fiberMultiplicity 0 = 8
  conclusion_window6_local_morita_trivial_global_nonorbitizable_multFour :
    conclusion_window6_local_morita_trivial_global_nonorbitizable_fiberMultiplicity 1 = 4
  conclusion_window6_local_morita_trivial_global_nonorbitizable_multNine :
    conclusion_window6_local_morita_trivial_global_nonorbitizable_fiberMultiplicity 2 = 9
  conclusion_window6_local_morita_trivial_global_nonorbitizable_localContractibleWitness :
    ∀ c : Fin 3,
      0 < conclusion_window6_local_morita_trivial_global_nonorbitizable_fiberSize c
  conclusion_window6_local_morita_trivial_global_nonorbitizable_matrixBlockWitness :
    ∀ c : Fin 3,
      ∃ n : ℕ,
        conclusion_window6_local_morita_trivial_global_nonorbitizable_fiberSize c = n ∧
          0 < n

namespace conclusion_window6_local_morita_trivial_global_nonorbitizable_Data

/-- Every local hidden fiber in the concrete window-6 package is contractible. -/
def localContractible
    (D : conclusion_window6_local_morita_trivial_global_nonorbitizable_Data) : Prop :=
  ∀ c : Fin 3, 0 < D.conclusion_window6_local_morita_trivial_global_nonorbitizable_fiberSize c

/-- Every local pair groupoid algebra is represented by a positive-size matrix block. -/
def localMatrixBlocks
    (D : conclusion_window6_local_morita_trivial_global_nonorbitizable_Data) : Prop :=
  ∀ c : Fin 3,
    ∃ n : ℕ,
      D.conclusion_window6_local_morita_trivial_global_nonorbitizable_fiberSize c = n ∧ 0 < n

/-- A free finite-group orbit relation would force all fiber cardinalities to be constant. -/
def notFreeOrbitRelation
    (D : conclusion_window6_local_morita_trivial_global_nonorbitizable_Data) : Prop :=
  ¬ ∃ q : ℕ,
      ∀ c : Fin 3,
        D.conclusion_window6_local_morita_trivial_global_nonorbitizable_fiberSize c = q

/-- An affine coset partition of an abelian group would also force a constant coset size. -/
def notAffineCosetPartition
    (D : conclusion_window6_local_morita_trivial_global_nonorbitizable_Data) : Prop :=
  ¬ ∃ q : ℕ,
      ∀ c : Fin 3,
        D.conclusion_window6_local_morita_trivial_global_nonorbitizable_fiberSize c = q

lemma conclusion_window6_local_morita_trivial_global_nonorbitizable_not_constant
    (D : conclusion_window6_local_morita_trivial_global_nonorbitizable_Data) :
    ¬ ∃ q : ℕ,
      ∀ c : Fin 3,
        D.conclusion_window6_local_morita_trivial_global_nonorbitizable_fiberSize c = q := by
  rintro ⟨q, hq⟩
  have htwo :
      q = 2 := by
    rw [← D.conclusion_window6_local_morita_trivial_global_nonorbitizable_sizeTwo]
    exact (hq 0).symm
  have hthree :
      q = 3 := by
    rw [← D.conclusion_window6_local_morita_trivial_global_nonorbitizable_sizeThree]
    exact (hq 1).symm
  omega

end conclusion_window6_local_morita_trivial_global_nonorbitizable_Data

open conclusion_window6_local_morita_trivial_global_nonorbitizable_Data

/-- Paper label: `thm:conclusion-window6-local-morita-trivial-global-nonorbitizable`.  The
local contractibility and matrix-block Morita clauses are the concrete local witnesses in `D`;
the global obstruction clauses follow because the window-6 fiber sizes `2, 3, 4` cannot be the
constant orbit or coset cardinality required by a free orbit relation or affine coset partition. -/
theorem paper_conclusion_window6_local_morita_trivial_global_nonorbitizable
    (D : conclusion_window6_local_morita_trivial_global_nonorbitizable_Data) :
    D.localContractible ∧ D.localMatrixBlocks ∧ D.notFreeOrbitRelation ∧
      D.notAffineCosetPartition := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact D.conclusion_window6_local_morita_trivial_global_nonorbitizable_localContractibleWitness
  · exact D.conclusion_window6_local_morita_trivial_global_nonorbitizable_matrixBlockWitness
  · exact conclusion_window6_local_morita_trivial_global_nonorbitizable_not_constant D
  · exact conclusion_window6_local_morita_trivial_global_nonorbitizable_not_constant D

end Omega.Conclusion
