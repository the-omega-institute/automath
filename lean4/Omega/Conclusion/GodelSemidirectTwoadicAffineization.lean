import Mathlib.Tactic
import Omega.Conclusion.AffineNormalFormSemidirect
import Omega.Conclusion.PrimeRegisterFixed2adicAmbientVsFiniteLedger
import Omega.Conclusion.PrimorialMixedRadixAffine

namespace Omega.Conclusion

/-- Paper-facing package assembling the affine normal form, its universal property, the concrete
`2,3,5` mixed-radix collapse, and the faithful affine action on the fixed two-adic ambient. -/
def conclusionGodelSemidirectTwoadicAffineization : Prop :=
  Fintype.card (Fin 2) = 2 ∧
    Function.Injective primeRegisterAffineAction ∧
    (∀ N M k ℓ : ℕ, 0 < N → 0 < M →
      Omega.Conclusion.AffineNormalFormSemidirect.A_N_k N k *
          Omega.Conclusion.AffineNormalFormSemidirect.A_N_k M ℓ =
        Omega.Conclusion.AffineNormalFormSemidirect.A_N_k
          (Omega.Conclusion.AffineNormalFormSemidirect.semidirectMul (N, k) (M, ℓ)).1
          (Omega.Conclusion.AffineNormalFormSemidirect.semidirectMul (N, k) (M, ℓ)).2) ∧
    (∀ {S : Type*} [Monoid S] (iota : ℕ → S) (tau : S),
      iota 1 = 1 →
      (∀ N M, iota (N * M) = iota N * iota M) →
      (∀ N, iota N * tau = tau ^ N * iota N) →
      ∃! F : ℕ × ℕ → S,
        (∀ a b,
            F (Omega.Conclusion.AffineNormalFormSemidirect.semidirectMul a b) = F a * F b) ∧
          (∀ N, F (N, 0) = iota N) ∧
          F (1, 1) = tau) ∧
    (∀ a1 a2 a3 : ℕ,
      Omega.Conclusion.AffineNormalFormSemidirect.A_N_k 2 a1 *
          Omega.Conclusion.AffineNormalFormSemidirect.A_N_k 3 a2 *
          Omega.Conclusion.AffineNormalFormSemidirect.A_N_k 5 a3 =
        Omega.Conclusion.AffineNormalFormSemidirect.A_N_k 30
          (Omega.Conclusion.PrimorialMixedRadixAffine.mixedRadixEncode3 a1 a2 a3))

/-- Paper label: `thm:conclusion-godel-semidirect-twoadic-affineization`. -/
theorem paper_conclusion_godel_semidirect_twoadic_affineization :
    conclusionGodelSemidirectTwoadicAffineization := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact paper_conclusion_prime_register_fixed_2adic_ambient_vs_finite_ledger.1
  · exact paper_conclusion_prime_register_fixed_2adic_ambient_vs_finite_ledger.2.1
  · intro N M k ℓ hN hM
    exact Omega.Conclusion.AffineNormalFormSemidirect.paper_conclusion_affine_normal_form_semidirect
      N M k ℓ hN hM
  · intro S _ iota tau hiota_one hiota_mul hcomm
    exact
      (Omega.Conclusion.AffineNormalFormSemidirect.paper_conclusion_affine_ext_initial_object).2
        iota tau hiota_one hiota_mul hcomm
  · exact
      (Omega.Conclusion.PrimorialMixedRadixAffine.paper_conclusion_primorial_mixed_radix_affine).2.2.2.1

end Omega.Conclusion
