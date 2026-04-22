import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Tactic
import Omega.POM.PrimeTraceShiftFreeMonoid

namespace Omega.POM

open FreeMonoid

/-- A concrete three-letter alphabet carrying distinct prime codes. -/
abbrev pom_prime_trace_index_duality_alphabet := Fin 3

/-- Concrete prime code used for the chapter-local prime-trace duality wrapper. -/
def pom_prime_trace_index_duality_code (i : pom_prime_trace_index_duality_alphabet) : ℕ :=
  match i.1 with
  | 0 => 2
  | 1 => 3
  | _ => 5

private theorem pom_prime_trace_index_duality_code_injective :
    Function.Injective pom_prime_trace_index_duality_code := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [pom_prime_trace_index_duality_code] at hij ⊢

/-- Folded states are exactly the valid prime traces produced by the concrete code. -/
abbrev pom_prime_trace_index_duality_folded_state :=
  {w : FreeMonoid ℕ // pomValidPrimeTrace pom_prime_trace_index_duality_code w}

/-- The residual fiber over a folded state consists of the source words with that prime trace. -/
abbrev pom_prime_trace_index_duality_fiber
    (y : pom_prime_trace_index_duality_folded_state) :=
  {x : FreeMonoid pom_prime_trace_index_duality_alphabet //
    pomPrimeTraceHom pom_prime_trace_index_duality_code x = y.1}

/-- Because the prime-trace code is injective, each residual fiber is a singleton and its rank
image is `Fin 1`. -/
abbrev pom_prime_trace_index_duality_residual_image
    (_y : pom_prime_trace_index_duality_folded_state) := Fin 1

/-- Canonical decode map built from the valid prime-trace witness. -/
noncomputable def pom_prime_trace_index_duality_decode
    (y : pom_prime_trace_index_duality_folded_state) :
    FreeMonoid pom_prime_trace_index_duality_alphabet :=
  FreeMonoid.ofList (FreeMonoid.toList y.1 |>.map (Function.invFun pom_prime_trace_index_duality_code))

private theorem pom_prime_trace_index_duality_decode_sound
    (y : pom_prime_trace_index_duality_folded_state) :
    pomPrimeTraceHom pom_prime_trace_index_duality_code
        (pom_prime_trace_index_duality_decode y) = y.1 := by
  have hdecode :
      List.map pom_prime_trace_index_duality_code
          ((FreeMonoid.toList y.1).map (Function.invFun pom_prime_trace_index_duality_code)) =
        FreeMonoid.toList y.1 :=
    pomEncodeDecodeList pom_prime_trace_index_duality_code (FreeMonoid.toList y.1) y.2
  apply FreeMonoid.toList.injective
  simpa [pom_prime_trace_index_duality_decode, pomPrimeTraceHom, FreeMonoid.toList_map] using
    hdecode

/-- The rank map remembers only the unique fiber index. -/
def pom_prime_trace_index_duality_rank_map
    {y : pom_prime_trace_index_duality_folded_state}
    (_x : pom_prime_trace_index_duality_fiber y) :
    pom_prime_trace_index_duality_residual_image y :=
  0

/-- The inverse map reconstructs the unique source word from the folded state and the fiber rank.
-/
noncomputable def pom_prime_trace_index_duality_unrank_map
    (y : pom_prime_trace_index_duality_folded_state) :
    pom_prime_trace_index_duality_residual_image y →
      pom_prime_trace_index_duality_fiber y
  | _ => ⟨pom_prime_trace_index_duality_decode y,
      pom_prime_trace_index_duality_decode_sound y⟩

private theorem pom_prime_trace_index_duality_fiber_subsingleton
    (y : pom_prime_trace_index_duality_folded_state) :
    Subsingleton (pom_prime_trace_index_duality_fiber y) := by
  let hShiftFree :=
    paper_pom_prime_trace_shift_free_monoid
      pom_prime_trace_index_duality_code pom_prime_trace_index_duality_code_injective
  have hInjective : Function.Injective (pomPrimeTraceHom pom_prime_trace_index_duality_code) :=
    hShiftFree.2.2.1
  refine ⟨?_⟩
  intro a b
  apply Subtype.ext
  exact hInjective (a.2.trans b.2.symm)

private theorem pom_prime_trace_index_duality_rank_map_bijective
    (y : pom_prime_trace_index_duality_folded_state) :
    Function.Bijective (pom_prime_trace_index_duality_rank_map (y := y)) := by
  constructor
  · intro a b _
    exact (pom_prime_trace_index_duality_fiber_subsingleton y).elim a b
  · intro i
    fin_cases i
    exact ⟨pom_prime_trace_index_duality_unrank_map y 0, rfl⟩

/-- Global inverse obtained from the folded state together with the fiber rank. -/
noncomputable def pom_prime_trace_index_duality_inverse :
    (Σ y : pom_prime_trace_index_duality_folded_state,
      pom_prime_trace_index_duality_residual_image y) →
      FreeMonoid pom_prime_trace_index_duality_alphabet
  | ⟨y, i⟩ => (pom_prime_trace_index_duality_unrank_map y i).1

/-- Proposition-level statement for the prime-trace/fiber-index duality package. -/
def pom_prime_trace_index_duality_statement : Prop :=
  (∀ y : pom_prime_trace_index_duality_folded_state,
    Function.Bijective (pom_prime_trace_index_duality_rank_map (y := y))) ∧
    (∀ y : pom_prime_trace_index_duality_folded_state,
      ∀ i : pom_prime_trace_index_duality_residual_image y,
        pomPrimeTraceHom pom_prime_trace_index_duality_code
            (pom_prime_trace_index_duality_inverse ⟨y, i⟩) = y.1) ∧
    (∀ y : pom_prime_trace_index_duality_folded_state,
      ∀ x : pom_prime_trace_index_duality_fiber y,
        pom_prime_trace_index_duality_inverse
            ⟨y, pom_prime_trace_index_duality_rank_map x⟩ = x.1)

/-- `prop:pom-prime-trace-index-duality` -/
theorem paper_pom_prime_trace_index_duality :
    pom_prime_trace_index_duality_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro y
    exact pom_prime_trace_index_duality_rank_map_bijective y
  · intro y i
    simp [pom_prime_trace_index_duality_inverse, pom_prime_trace_index_duality_unrank_map,
      pom_prime_trace_index_duality_decode_sound]
  · intro y x
    have hx :
        pom_prime_trace_index_duality_unrank_map y
            (pom_prime_trace_index_duality_rank_map x) = x := by
      exact (pom_prime_trace_index_duality_fiber_subsingleton y).elim _ _
    exact congrArg Subtype.val hx

end Omega.POM
