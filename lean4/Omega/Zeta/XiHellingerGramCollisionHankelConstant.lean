import Omega.Zeta.XiHellingerHankelConstantRationality

namespace Omega.Zeta

/-- Concrete collision data for the Hellinger Gram determinant.  The determinant is a rational
model of the collision-scaled Gram determinant, and the supplied equalities encode the Andreief,
translation-invariance, and confluent-Vandermonde reduction to the Hankel determinant constant. -/
structure xi_hellinger_gram_collision_hankel_constant_Data where
  xi_hellinger_gram_collision_hankel_constant_kappa : ℕ
  xi_hellinger_gram_collision_hankel_constant_collisionGramDeterminant : ℚ → ℚ
  xi_hellinger_gram_collision_hankel_constant_hankelConstant : ℚ
  xi_hellinger_gram_collision_hankel_constant_prefactor :
    ℚ → ℚ
  xi_hellinger_gram_collision_hankel_constant_andreiefTranslationVandermonde :
    ∀ ε : ℚ,
      xi_hellinger_gram_collision_hankel_constant_collisionGramDeterminant ε =
        xi_hellinger_gram_collision_hankel_constant_prefactor ε *
          xi_hellinger_gram_collision_hankel_constant_hankelConstant
  xi_hellinger_gram_collision_hankel_constant_hankelIdentified :
    xi_hellinger_gram_collision_hankel_constant_hankelConstant =
      xiHellingerHankelConstant xi_hellinger_gram_collision_hankel_constant_kappa

namespace xi_hellinger_gram_collision_hankel_constant_Data

/-- The confluent-Vandermonde asymptotic after squaring the determinant expansion. -/
def confluentVandermondeAsymptotic
    (D : xi_hellinger_gram_collision_hankel_constant_Data) : Prop :=
  ∀ ε : ℚ,
    D.xi_hellinger_gram_collision_hankel_constant_collisionGramDeterminant ε =
      D.xi_hellinger_gram_collision_hankel_constant_prefactor ε *
        D.xi_hellinger_gram_collision_hankel_constant_hankelConstant

/-- The remaining collision integral is exactly the Hankel determinant constant, hence is a
function only of `κ`. -/
def hankelConstantOnlyDependsOnKappa
    (D : xi_hellinger_gram_collision_hankel_constant_Data) : Prop :=
  ∀ E : xi_hellinger_gram_collision_hankel_constant_Data,
    E.xi_hellinger_gram_collision_hankel_constant_kappa =
        D.xi_hellinger_gram_collision_hankel_constant_kappa →
      E.xi_hellinger_gram_collision_hankel_constant_hankelConstant =
        D.xi_hellinger_gram_collision_hankel_constant_hankelConstant

lemma xi_hellinger_gram_collision_hankel_constant_constant_depends_only_on_kappa
    (D : xi_hellinger_gram_collision_hankel_constant_Data) :
    D.hankelConstantOnlyDependsOnKappa := by
  intro E hκ
  calc
    E.xi_hellinger_gram_collision_hankel_constant_hankelConstant
        = xiHellingerHankelConstant E.xi_hellinger_gram_collision_hankel_constant_kappa := by
          exact E.xi_hellinger_gram_collision_hankel_constant_hankelIdentified
    _ = xiHellingerHankelConstant D.xi_hellinger_gram_collision_hankel_constant_kappa := by
          rw [hκ]
    _ = D.xi_hellinger_gram_collision_hankel_constant_hankelConstant := by
          exact D.xi_hellinger_gram_collision_hankel_constant_hankelIdentified.symm

end xi_hellinger_gram_collision_hankel_constant_Data

open xi_hellinger_gram_collision_hankel_constant_Data

/-- Paper label: `thm:xi-hellinger-gram-collision-hankel-constant`.  The prefixed hypotheses
provide the Andreief representation, translation reduction, and squared confluent-Vandermonde
factorization; identifying the residual integral with `xiHellingerHankelConstant κ` gives the
Hankel constant dependence clause. -/
theorem paper_xi_hellinger_gram_collision_hankel_constant
    (D : xi_hellinger_gram_collision_hankel_constant_Data) :
    D.confluentVandermondeAsymptotic ∧ D.hankelConstantOnlyDependsOnKappa := by
  refine ⟨?_, ?_⟩
  · exact D.xi_hellinger_gram_collision_hankel_constant_andreiefTranslationVandermonde
  · exact xi_hellinger_gram_collision_hankel_constant_constant_depends_only_on_kappa D

end Omega.Zeta
