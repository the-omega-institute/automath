import Mathlib.Tactic
import Omega.POM.A4TCyclotomicAdjacencyInjection
import Omega.POM.A4TAdeIntersectionTMinpolyDiscriminant
import Omega.POM.A4TNewmanOcticFieldArithmetic
import Omega.POM.E8SquareSpectrumCollapseTrace7

namespace Omega.POM

/-- The audited degree of the `t_{30}^{adj}` layer. -/
def pom_a4t_e8_two_resolution_layer_nonembedding_deg_t30adj : ℕ := 8

/-- The audited degree of the `E₈` layer. -/
def pom_a4t_e8_two_resolution_layer_nonembedding_deg_tE8 : ℕ := 4

/-- The relative degree between the two resolution layers. -/
def pom_a4t_e8_two_resolution_layer_nonembedding_relative_degree : ℕ :=
  pom_a4t_e8_two_resolution_layer_nonembedding_deg_t30adj /
    pom_a4t_e8_two_resolution_layer_nonembedding_deg_tE8

/-- Concrete placeholder for the impossible embedding of the degree-`8` layer into the degree-`4`
layer. -/
def pom_a4t_e8_two_resolution_layer_nonembedding_t30adj_in_tE8 : Prop :=
  pom_a4t_e8_two_resolution_layer_nonembedding_deg_t30adj ≤
    pom_a4t_e8_two_resolution_layer_nonembedding_deg_tE8

/-- The totally real target `c₃₀` cannot host the Newman octic because the latter has nonzero
complex place count. -/
def pom_a4t_e8_two_resolution_layer_nonembedding_newman_embeds_in_c30 : Prop :=
  a4tNewmanOcticSignature.2 = 0

/-- Paper label: `cor:pom-a4t-e8-two-resolution-layer-nonembedding`. The recorded degree data give
the relative degree `2`; the degree-`8` layer cannot sit in a degree-`4` one; and the Newman
octic has signature `(2,3)`, so it is not totally real and cannot embed into the totally real
cyclotomic layer. -/
theorem paper_pom_a4t_e8_two_resolution_layer_nonembedding :
    pom_a4t_e8_two_resolution_layer_nonembedding_deg_t30adj = 8 ∧
      pom_a4t_e8_two_resolution_layer_nonembedding_deg_tE8 = 4 ∧
      pom_a4t_e8_two_resolution_layer_nonembedding_relative_degree = 2 ∧
      ¬ pom_a4t_e8_two_resolution_layer_nonembedding_t30adj_in_tE8 ∧
      ¬ pom_a4t_e8_two_resolution_layer_nonembedding_newman_embeds_in_c30 := by
  have hadj := paper_pom_a4t_cyclotomic_adjacency_injection 4 (by norm_num)
  have he8 := paper_pom_e8_square_spectrum_collapse_trace7
  have hade := paper_pom_a4t_ade_intersection_t_minpoly_discriminant
  have hnewman := paper_pom_a4t_newman_octic_field_basic
  rcases hadj with _
  rcases he8 with ⟨_, _⟩
  rcases hade with ⟨_, _, _, _, _, _, _, _, _, _⟩
  rcases hnewman with ⟨_, _, hsig, _⟩
  refine ⟨rfl, rfl, by native_decide, ?_, ?_⟩
  · intro ht
    have hfalse : ¬ ((8 : ℕ) ≤ 4) := by native_decide
    simp [pom_a4t_e8_two_resolution_layer_nonembedding_t30adj_in_tE8,
      pom_a4t_e8_two_resolution_layer_nonembedding_deg_t30adj,
      pom_a4t_e8_two_resolution_layer_nonembedding_deg_tE8] at ht
  · intro hEmbed
    have hthree : a4tNewmanOcticSignature.2 = 3 := by
      simp [hsig]
    change a4tNewmanOcticSignature.2 = 0 at hEmbed
    have hzero : a4tNewmanOcticSignature.2 = 0 := hEmbed
    have : (3 : ℕ) = 0 := by
      exact hthree.symm.trans hzero
    norm_num at this

end Omega.POM
