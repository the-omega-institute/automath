import Mathlib.Tactic
import Omega.Zeta.XiTimePart9n1bFourGeneraRecoverHodgeVector

namespace Omega.Zeta

open Finset

/-- Dimensions of the four irreducible `S₄` summands used by the reciprocity package:
sign, two-dimensional, standard, and twisted-standard. -/
def xi_time_part9n1b_prym_chevalley_weil_reciprocity_irrepDimension : Fin 4 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 3
  | ⟨3, _⟩ => 3

/-- Multiplicities recovered from the four genus equalities. -/
def xi_time_part9n1b_prym_chevalley_weil_reciprocity_multiplicity : Fin 4 → ℕ
  | ⟨0, _⟩ => 5
  | ⟨1, _⟩ => 4
  | ⟨2, _⟩ => 3
  | ⟨3, _⟩ => 9

/-- Geometric Jacobian/Prym carrier dimensions for the four summands. -/
def xi_time_part9n1b_prym_chevalley_weil_reciprocity_carrierDimension :
    Fin 4 → ℕ :=
  fun i =>
    xi_time_part9n1b_prym_chevalley_weil_reciprocity_irrepDimension i *
      xi_time_part9n1b_prym_chevalley_weil_reciprocity_multiplicity i

/-- Concrete genus and carrier data for the Prym--Chevalley--Weil reciprocity computation. -/
structure xi_time_part9n1b_prym_chevalley_weil_reciprocity_data where
  xi_time_part9n1b_prym_chevalley_weil_reciprocity_gX : ℤ
  xi_time_part9n1b_prym_chevalley_weil_reciprocity_gH : ℤ
  xi_time_part9n1b_prym_chevalley_weil_reciprocity_gC6 : ℤ
  xi_time_part9n1b_prym_chevalley_weil_reciprocity_gCF : ℤ
  xi_time_part9n1b_prym_chevalley_weil_reciprocity_mSgn : ℤ
  xi_time_part9n1b_prym_chevalley_weil_reciprocity_mV2 : ℤ
  xi_time_part9n1b_prym_chevalley_weil_reciprocity_mV3 : ℤ
  xi_time_part9n1b_prym_chevalley_weil_reciprocity_mV3p : ℤ
  xi_time_part9n1b_prym_chevalley_weil_reciprocity_hSgn :
    xi_time_part9n1b_prym_chevalley_weil_reciprocity_mSgn =
      xi_time_part9n1b_prym_chevalley_weil_reciprocity_gH
  xi_time_part9n1b_prym_chevalley_weil_reciprocity_hV2 :
    2 * xi_time_part9n1b_prym_chevalley_weil_reciprocity_mV2 =
      xi_time_part9n1b_prym_chevalley_weil_reciprocity_gC6 -
        xi_time_part9n1b_prym_chevalley_weil_reciprocity_gH
  xi_time_part9n1b_prym_chevalley_weil_reciprocity_hV3 :
    xi_time_part9n1b_prym_chevalley_weil_reciprocity_mV3 =
      xi_time_part9n1b_prym_chevalley_weil_reciprocity_gCF
  xi_time_part9n1b_prym_chevalley_weil_reciprocity_hV3p :
    3 * xi_time_part9n1b_prym_chevalley_weil_reciprocity_mV3p =
      xi_time_part9n1b_prym_chevalley_weil_reciprocity_gX -
        xi_time_part9n1b_prym_chevalley_weil_reciprocity_gC6 -
          3 * xi_time_part9n1b_prym_chevalley_weil_reciprocity_gCF
  xi_time_part9n1b_prym_chevalley_weil_reciprocity_hNums :
    xi_time_part9n1b_prym_chevalley_weil_reciprocity_gX = 49 ∧
      xi_time_part9n1b_prym_chevalley_weil_reciprocity_gH = 5 ∧
        xi_time_part9n1b_prym_chevalley_weil_reciprocity_gC6 = 13 ∧
          xi_time_part9n1b_prym_chevalley_weil_reciprocity_gCF = 3

/-- The four recovered multiplicities and the resulting carrier dimensions exhaust dimension 49. -/
def xi_time_part9n1b_prym_chevalley_weil_reciprocity_statement
    (D : xi_time_part9n1b_prym_chevalley_weil_reciprocity_data) : Prop :=
  (D.xi_time_part9n1b_prym_chevalley_weil_reciprocity_mSgn,
      D.xi_time_part9n1b_prym_chevalley_weil_reciprocity_mV2,
      D.xi_time_part9n1b_prym_chevalley_weil_reciprocity_mV3,
      D.xi_time_part9n1b_prym_chevalley_weil_reciprocity_mV3p) =
    (5, 4, 3, 9) ∧
    (∀ i : Fin 4,
      xi_time_part9n1b_prym_chevalley_weil_reciprocity_carrierDimension i =
        xi_time_part9n1b_prym_chevalley_weil_reciprocity_irrepDimension i *
          xi_time_part9n1b_prym_chevalley_weil_reciprocity_multiplicity i) ∧
      (∑ i : Fin 4,
        xi_time_part9n1b_prym_chevalley_weil_reciprocity_carrierDimension i) = 49

/-- Paper label: `thm:xi-time-part9n1b-prym-chevalley-weil-reciprocity`. -/
theorem paper_xi_time_part9n1b_prym_chevalley_weil_reciprocity
    (D : xi_time_part9n1b_prym_chevalley_weil_reciprocity_data) :
    xi_time_part9n1b_prym_chevalley_weil_reciprocity_statement D := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      paper_xi_time_part9n1b_four_genera_recover_hodge_vector
        D.xi_time_part9n1b_prym_chevalley_weil_reciprocity_gX
        D.xi_time_part9n1b_prym_chevalley_weil_reciprocity_gH
        D.xi_time_part9n1b_prym_chevalley_weil_reciprocity_gC6
        D.xi_time_part9n1b_prym_chevalley_weil_reciprocity_gCF
        D.xi_time_part9n1b_prym_chevalley_weil_reciprocity_mSgn
        D.xi_time_part9n1b_prym_chevalley_weil_reciprocity_mV2
        D.xi_time_part9n1b_prym_chevalley_weil_reciprocity_mV3
        D.xi_time_part9n1b_prym_chevalley_weil_reciprocity_mV3p
        D.xi_time_part9n1b_prym_chevalley_weil_reciprocity_hSgn
        D.xi_time_part9n1b_prym_chevalley_weil_reciprocity_hV2
        D.xi_time_part9n1b_prym_chevalley_weil_reciprocity_hV3
        D.xi_time_part9n1b_prym_chevalley_weil_reciprocity_hV3p
        D.xi_time_part9n1b_prym_chevalley_weil_reciprocity_hNums
  · intro i
    rfl
  · native_decide

end Omega.Zeta
