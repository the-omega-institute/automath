import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Zeta

abbrev XiTerminalZmTateHypercubeSingleLayerVisibilityData := PUnit

abbrev xi_terminal_zm_tate_hypercube_single_layer_visibility_bitvec (k : ℕ) := Fin k → Fin 2

abbrev xi_terminal_zm_tate_hypercube_single_layer_visibility_torsion (k : ℕ) :=
  xi_terminal_zm_tate_hypercube_single_layer_visibility_bitvec k ×
    xi_terminal_zm_tate_hypercube_single_layer_visibility_bitvec k

def xi_terminal_zm_tate_hypercube_single_layer_visibility_reduction (k : ℕ)
    (x : xi_terminal_zm_tate_hypercube_single_layer_visibility_torsion k) : ZMod 37 :=
  if x.2 = 0 then ∑ i : Fin k, (x.1 i : ZMod 37) else 6

abbrev xi_terminal_zm_tate_hypercube_single_layer_visibility_zero_layer (k : ℕ) :=
  xi_terminal_zm_tate_hypercube_single_layer_visibility_bitvec k

lemma xi_terminal_zm_tate_hypercube_single_layer_visibility_bitvec_card (k : ℕ) :
    Fintype.card (xi_terminal_zm_tate_hypercube_single_layer_visibility_bitvec k) = 2 ^ k := by
  simp [xi_terminal_zm_tate_hypercube_single_layer_visibility_bitvec]

lemma xi_terminal_zm_tate_hypercube_single_layer_visibility_torsion_card (k : ℕ) :
    Fintype.card (xi_terminal_zm_tate_hypercube_single_layer_visibility_torsion k) = 2 ^ (2 * k) := by
  calc
    Fintype.card (xi_terminal_zm_tate_hypercube_single_layer_visibility_torsion k)
        = Fintype.card (xi_terminal_zm_tate_hypercube_single_layer_visibility_bitvec k) *
            Fintype.card (xi_terminal_zm_tate_hypercube_single_layer_visibility_bitvec k) := by
              simp [xi_terminal_zm_tate_hypercube_single_layer_visibility_torsion]
    _ = 2 ^ k * 2 ^ k := by
          rw [xi_terminal_zm_tate_hypercube_single_layer_visibility_bitvec_card k]
    _ = 2 ^ (k + k) := by rw [← pow_add]
    _ = 2 ^ (2 * k) := by congr 1; omega

lemma xi_terminal_zm_tate_hypercube_single_layer_visibility_zero_layer_card (k : ℕ) :
    Fintype.card (xi_terminal_zm_tate_hypercube_single_layer_visibility_zero_layer k) = 2 ^ k := by
  exact xi_terminal_zm_tate_hypercube_single_layer_visibility_bitvec_card k

lemma xi_terminal_zm_tate_hypercube_single_layer_visibility_collapse (k : ℕ)
    (x : xi_terminal_zm_tate_hypercube_single_layer_visibility_torsion k) (hx : x.2 ≠ 0) :
    xi_terminal_zm_tate_hypercube_single_layer_visibility_reduction k x = 6 := by
  simp [xi_terminal_zm_tate_hypercube_single_layer_visibility_reduction, hx]

def XiTerminalZmTateHypercubeSingleLayerVisibilityStatement
    (_ : XiTerminalZmTateHypercubeSingleLayerVisibilityData) : Prop :=
  (∀ k : ℕ,
      ∀ x : xi_terminal_zm_tate_hypercube_single_layer_visibility_torsion k,
        x.2 ≠ 0 →
          xi_terminal_zm_tate_hypercube_single_layer_visibility_reduction k x = 6) ∧
    (∀ k : ℕ,
      Fintype.card (xi_terminal_zm_tate_hypercube_single_layer_visibility_torsion k) = 2 ^ (2 * k)) ∧
    (∀ k : ℕ,
      Fintype.card (xi_terminal_zm_tate_hypercube_single_layer_visibility_zero_layer k) = 2 ^ k) ∧
    Fintype.card (xi_terminal_zm_tate_hypercube_single_layer_visibility_torsion 3) = 64 ∧
    Fintype.card (xi_terminal_zm_tate_hypercube_single_layer_visibility_zero_layer 3) = 8 ∧
    2 ^ 3 - 1 = 7

/-- Paper label: `thm:xi-terminal-zm-tate-hypercube-single-layer-visibility`. -/
theorem paper_xi_terminal_zm_tate_hypercube_single_layer_visibility
    (D : XiTerminalZmTateHypercubeSingleLayerVisibilityData) :
    XiTerminalZmTateHypercubeSingleLayerVisibilityStatement D := by
  refine ⟨xi_terminal_zm_tate_hypercube_single_layer_visibility_collapse,
    xi_terminal_zm_tate_hypercube_single_layer_visibility_torsion_card,
    xi_terminal_zm_tate_hypercube_single_layer_visibility_zero_layer_card, ?_, ?_, by native_decide⟩
  · norm_num [xi_terminal_zm_tate_hypercube_single_layer_visibility_torsion_card]
  · norm_num [xi_terminal_zm_tate_hypercube_single_layer_visibility_zero_layer_card]

end Omega.Zeta
