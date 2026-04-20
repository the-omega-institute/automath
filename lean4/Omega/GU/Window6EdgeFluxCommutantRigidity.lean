import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic
import Omega.GU.Window6EdgeFluxFullMatrixSaturation


namespace Omega.GU

open Matrix

/-- The concrete commutant submodule of a fixed endomorphism. -/
private def matrixCentralizer
    (T : Matrix (Fin 21) (Fin 21) Real) :
    Submodule Real (Matrix (Fin 21) (Fin 21) Real) where
  carrier := {A | T * A = A * T}
  zero_mem' := by simp
  add_mem' := by
    intro A B hA hB
    have hA' : T * A = A * T := hA
    have hB' : T * B = B * T := hB
    calc
      T * (A + B) = T * A + T * B := by rw [mul_add]
      _ = A * T + B * T := by rw [hA', hB']
      _ = (A + B) * T := by rw [add_mul]
  smul_mem' := by
    intro c A hA
    have hA' : T * A = A * T := hA
    calc
      T * (c • A) = c • (T * A) := by rw [Matrix.mul_smul]
      _ = c • (A * T) := by rw [hA']
      _ = (c • A) * T := by rw [Matrix.smul_mul]

private lemma window6EdgeFluxClosure_le_matrixCentralizer
    (L : Fin 6 → Matrix (Fin 21) (Fin 21) Real) (T : Matrix (Fin 21) (Fin 21) Real)
    (hComm : ∀ i : Fin 6, T * L i = L i * T) :
    window6EdgeFluxClosure L ≤ matrixCentralizer T := by
  refine Submodule.span_le.2 ?_
  intro A hA
  rcases hA with hA | hA
  · have hI : A = 1 := by simpa using hA
    subst hI
    simp [matrixCentralizer]
  · rcases hA with ⟨i, rfl⟩
    exact hComm i

/-- If the six edge generators already saturate `End(V)`, then any matrix commuting with all six
is scalar. This is the matrix form of the paper's commutant-rigidity argument.
    thm:window6-edge-flux-commutant-rigidity -/
theorem paper_window6_edge_flux_commutant_rigidity
    (L : Fin 6 → Matrix (Fin 21) (Fin 21) Real) (hLie : Window6LieEnvelopeIsSl21 L) :
    ∀ T : Matrix (Fin 21) (Fin 21) Real,
      (∀ i : Fin 6, T * L i = L i * T) →
      ∃ c : Real, T = c • (1 : Matrix (Fin 21) (Fin 21) Real) := by
  intro T hComm
  have hFull := paper_window6_edge_flux_full_matrix_saturation L hLie
  have hClosure :
      window6EdgeFluxClosure L ≤ matrixCentralizer T :=
    window6EdgeFluxClosure_le_matrixCentralizer L T hComm
  have hCommAll : ∀ A : Matrix (Fin 21) (Fin 21) Real, T * A = A * T := by
    intro A
    exact hClosure (hFull A)
  have hScalar :
      T ∈ Set.range (Matrix.scalar (Fin 21) : Real → Matrix (Fin 21) (Fin 21) Real) := by
    refine Matrix.mem_range_scalar_iff_commute_single'.2 ?_
    intro i j
    change Matrix.single i j (1 : Real) * T = T * Matrix.single i j (1 : Real)
    simpa using (hCommAll (Matrix.single i j (1 : Real))).symm
  rcases hScalar with ⟨c, rfl⟩
  refine ⟨c, ?_⟩
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · simp [Matrix.scalar, hij]

end Omega.GU
