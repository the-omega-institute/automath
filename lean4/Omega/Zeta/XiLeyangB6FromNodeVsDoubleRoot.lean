import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

open Polynomial

namespace Omega.Zeta

noncomputable def xi_leyang_b6_from_node_vs_double_root_PLY : Polynomial ℤ :=
  C (256 : ℤ) * X ^ 3 + C (411 : ℤ) * X ^ 2 + C (165 : ℤ) * X + C (32 : ℤ)

noncomputable def xi_leyang_b6_from_node_vs_double_root_Q5 : Polynomial ℤ :=
  C (4096 : ℤ) * X ^ 5 + C (5376 : ℤ) * X ^ 4 + C (-464 : ℤ) * X ^ 3 +
    C (-2749 : ℤ) * X ^ 2 + C (-723 : ℤ) * X + C (80 : ℤ)

noncomputable def xi_leyang_b6_from_node_vs_double_root_A7 : Polynomial ℤ :=
  C (45056 : ℤ) * X ^ 7 + C (60160 : ℤ) * X ^ 6 + C (-11984 : ℤ) * X ^ 5 +
    C (-19765 : ℤ) * X ^ 4 + C (18906 : ℤ) * X ^ 3 +
    C (14723 : ℤ) * X ^ 2 + C (2216 : ℤ) * X + C (200 : ℤ)

noncomputable def xi_leyang_b6_from_node_vs_double_root_P4 : Polynomial ℤ :=
  C (8192 : ℤ) * X ^ 4 + C (5888 : ℤ) * X ^ 3 + C (-3680 : ℤ) * X ^ 2 +
    C (-2848 : ℤ) * X + C (152 : ℤ)

noncomputable def xi_leyang_b6_from_node_vs_double_root_N : Polynomial ℤ :=
  X * (X - C (1 : ℤ)) * (C (8 : ℤ) * X - C (3 : ℤ)) *
      (C (16 : ℤ) * X + C (11 : ℤ)) * (C (32 : ℤ) * X + C (19 : ℤ)) *
    xi_leyang_b6_from_node_vs_double_root_PLY

noncomputable def xi_leyang_b6_from_node_vs_double_root_B6 : Polynomial ℤ :=
  C (360448 : ℤ) * X ^ 6 + C (267264 : ℤ) * X ^ 5 +
    C (-221824 : ℤ) * X ^ 4 + C (18600 : ℤ) * X ^ 3 +
    C (149481 : ℤ) * X ^ 2 + C (25423 : ℤ) * X + C (1520 : ℤ)

def xi_leyang_b6_from_node_vs_double_root_identity : Prop :=
  C (93 : ℤ) * xi_leyang_b6_from_node_vs_double_root_N +
      C (4 : ℤ) * xi_leyang_b6_from_node_vs_double_root_A7 *
        xi_leyang_b6_from_node_vs_double_root_P4 =
    xi_leyang_b6_from_node_vs_double_root_Q5 *
      xi_leyang_b6_from_node_vs_double_root_B6

/-- Paper label: `thm:xi-leyang-b6-from-node-vs-double-root`. -/
theorem paper_xi_leyang_b6_from_node_vs_double_root :
    xi_leyang_b6_from_node_vs_double_root_identity := by
  unfold xi_leyang_b6_from_node_vs_double_root_identity
  apply Polynomial.funext
  intro y
  unfold xi_leyang_b6_from_node_vs_double_root_N
  unfold xi_leyang_b6_from_node_vs_double_root_PLY
  unfold xi_leyang_b6_from_node_vs_double_root_Q5
  unfold xi_leyang_b6_from_node_vs_double_root_A7
  unfold xi_leyang_b6_from_node_vs_double_root_P4
  unfold xi_leyang_b6_from_node_vs_double_root_B6
  norm_num
  ring

end Omega.Zeta
