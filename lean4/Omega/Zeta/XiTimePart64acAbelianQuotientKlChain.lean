import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

noncomputable section

/-- Concrete finite abelian-quotient package: the fine space is a product of a coarse quotient
and a uniform finite fiber. -/
structure XiTimePart64acAbelianQuotientKlChainData where
  coarseCard : ℕ
  fiberCard : ℕ
  hcoarse : 0 < coarseCard
  hfiber : 0 < fiberCard
  coarseLaw : Fin coarseCard → ℝ
  fineLaw : Fin coarseCard → Fin fiberCard → ℝ
  hcoarse_pos : ∀ c, 0 < coarseLaw c
  hfine_pos : ∀ c k, 0 < fineLaw c k
  hpush : ∀ c, ∑ k, fineLaw c k = coarseLaw c

namespace XiTimePart64acAbelianQuotientKlChainData

def thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformCoarse
    (D : XiTimePart64acAbelianQuotientKlChainData) (_c : Fin D.coarseCard) : ℝ :=
  1 / D.coarseCard

def thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformFiber
    (D : XiTimePart64acAbelianQuotientKlChainData) (_c : Fin D.coarseCard)
    (_k : Fin D.fiberCard) : ℝ :=
  1 / D.fiberCard

def thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformFine
    (D : XiTimePart64acAbelianQuotientKlChainData) (_c : Fin D.coarseCard)
    (_k : Fin D.fiberCard) : ℝ :=
  1 / (D.coarseCard * D.fiberCard)

def thm_xi_time_part64ac_abelian_quotient_kl_chain_conditionalFiber
    (D : XiTimePart64acAbelianQuotientKlChainData) (c : Fin D.coarseCard)
    (k : Fin D.fiberCard) : ℝ :=
  D.fineLaw c k / D.coarseLaw c

def thm_xi_time_part64ac_abelian_quotient_kl_chain_fineKL
    (D : XiTimePart64acAbelianQuotientKlChainData) : ℝ :=
  ∑ c, ∑ k,
    D.fineLaw c k *
      Real.log
        (D.fineLaw c k /
          thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformFine D c k)

def thm_xi_time_part64ac_abelian_quotient_kl_chain_coarseKL
    (D : XiTimePart64acAbelianQuotientKlChainData) : ℝ :=
  ∑ c,
    D.coarseLaw c *
      Real.log
        (D.coarseLaw c /
          thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformCoarse D c)

def thm_xi_time_part64ac_abelian_quotient_kl_chain_fiberKL
    (D : XiTimePart64acAbelianQuotientKlChainData) (c : Fin D.coarseCard) : ℝ :=
  ∑ k,
    thm_xi_time_part64ac_abelian_quotient_kl_chain_conditionalFiber D c k *
      Real.log
        (thm_xi_time_part64ac_abelian_quotient_kl_chain_conditionalFiber D c k /
          thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformFiber D c k)

def statement (D : XiTimePart64acAbelianQuotientKlChainData) : Prop :=
  (∀ c k,
      thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformFine D c k =
        thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformCoarse D c *
          thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformFiber D c k) ∧
    (∀ c k,
      D.fineLaw c k =
        D.coarseLaw c * thm_xi_time_part64ac_abelian_quotient_kl_chain_conditionalFiber D c k) ∧
    thm_xi_time_part64ac_abelian_quotient_kl_chain_fineKL D =
      thm_xi_time_part64ac_abelian_quotient_kl_chain_coarseKL D +
        ∑ c, D.coarseLaw c * thm_xi_time_part64ac_abelian_quotient_kl_chain_fiberKL D c

lemma thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformFine_factor
    (D : XiTimePart64acAbelianQuotientKlChainData) (c : Fin D.coarseCard)
    (k : Fin D.fiberCard) :
    thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformFine D c k =
      thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformCoarse D c *
        thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformFiber D c k := by
  have hcoarse_ne : (D.coarseCard : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt D.hcoarse)
  have hfiber_ne : (D.fiberCard : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt D.hfiber)
  unfold thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformFine
    thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformCoarse
    thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformFiber
  field_simp [hcoarse_ne, hfiber_ne]

lemma thm_xi_time_part64ac_abelian_quotient_kl_chain_fine_factor
    (D : XiTimePart64acAbelianQuotientKlChainData) (c : Fin D.coarseCard)
    (k : Fin D.fiberCard) :
    D.fineLaw c k =
      D.coarseLaw c * thm_xi_time_part64ac_abelian_quotient_kl_chain_conditionalFiber D c k := by
  unfold thm_xi_time_part64ac_abelian_quotient_kl_chain_conditionalFiber
  field_simp [(D.hcoarse_pos c).ne']

lemma thm_xi_time_part64ac_abelian_quotient_kl_chain_log_split
    (D : XiTimePart64acAbelianQuotientKlChainData) (c : Fin D.coarseCard)
    (k : Fin D.fiberCard) :
    Real.log
        (D.fineLaw c k /
          thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformFine D c k) =
      Real.log
        (D.coarseLaw c /
          thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformCoarse D c) +
        Real.log
          (thm_xi_time_part64ac_abelian_quotient_kl_chain_conditionalFiber D c k /
            thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformFiber D c k) := by
  have hcoarse_pos : 0 < D.coarseLaw c := D.hcoarse_pos c
  have hfine_pos : 0 < D.fineLaw c k := D.hfine_pos c k
  have hcond_pos :
      0 < thm_xi_time_part64ac_abelian_quotient_kl_chain_conditionalFiber D c k := by
    unfold thm_xi_time_part64ac_abelian_quotient_kl_chain_conditionalFiber
    exact div_pos hfine_pos hcoarse_pos
  have hunif_coarse_pos :
      0 < thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformCoarse D c := by
    unfold thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformCoarse
    exact one_div_pos.mpr (by exact_mod_cast D.hcoarse)
  have hunif_fiber_pos :
      0 < thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformFiber D c k := by
    unfold thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformFiber
    exact one_div_pos.mpr (by exact_mod_cast D.hfiber)
  have hratio :
      D.fineLaw c k /
          thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformFine D c k =
        (D.coarseLaw c /
            thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformCoarse D c) *
          (thm_xi_time_part64ac_abelian_quotient_kl_chain_conditionalFiber D c k /
            thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformFiber D c k) := by
    have hcoarse_ne : D.coarseLaw c ≠ 0 := hcoarse_pos.ne'
    have hcoarseCard_ne : (D.coarseCard : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt D.hcoarse)
    have hfiberCard_ne : (D.fiberCard : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt D.hfiber)
    unfold thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformFine
      thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformCoarse
      thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformFiber
      thm_xi_time_part64ac_abelian_quotient_kl_chain_conditionalFiber
    field_simp [hcoarse_ne, hcoarseCard_ne, hfiberCard_ne]
  rw [hratio,
    Real.log_mul (div_ne_zero hcoarse_pos.ne' hunif_coarse_pos.ne')
      (div_ne_zero hcond_pos.ne' hunif_fiber_pos.ne')]

lemma thm_xi_time_part64ac_abelian_quotient_kl_chain_identity
    (D : XiTimePart64acAbelianQuotientKlChainData) :
    thm_xi_time_part64ac_abelian_quotient_kl_chain_fineKL D =
      thm_xi_time_part64ac_abelian_quotient_kl_chain_coarseKL D +
        ∑ c, D.coarseLaw c * thm_xi_time_part64ac_abelian_quotient_kl_chain_fiberKL D c := by
  calc
    thm_xi_time_part64ac_abelian_quotient_kl_chain_fineKL D =
        ∑ c, ∑ k,
          D.fineLaw c k *
            (Real.log
              (D.coarseLaw c /
                thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformCoarse D c) +
              Real.log
                (thm_xi_time_part64ac_abelian_quotient_kl_chain_conditionalFiber D c k /
                  thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformFiber D c k)) := by
          unfold thm_xi_time_part64ac_abelian_quotient_kl_chain_fineKL
          refine Finset.sum_congr rfl ?_
          intro c hc
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [D.thm_xi_time_part64ac_abelian_quotient_kl_chain_log_split c k]
    _ =
        ∑ c, ((∑ k, D.fineLaw c k *
            Real.log
              (D.coarseLaw c /
                thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformCoarse D c)) +
          ∑ k, D.fineLaw c k *
            Real.log
              (thm_xi_time_part64ac_abelian_quotient_kl_chain_conditionalFiber D c k /
                thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformFiber D c k)) := by
          refine Finset.sum_congr rfl ?_
          intro c hc
          calc
            ∑ k,
                D.fineLaw c k *
                  (Real.log
                    (D.coarseLaw c /
                      thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformCoarse D c) +
                    Real.log
                      (thm_xi_time_part64ac_abelian_quotient_kl_chain_conditionalFiber D c k /
                        thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformFiber D c k))
                =
                  ∑ k,
                    (D.fineLaw c k *
                      Real.log
                        (D.coarseLaw c /
                          thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformCoarse D c) +
                      D.fineLaw c k *
                        Real.log
                          (thm_xi_time_part64ac_abelian_quotient_kl_chain_conditionalFiber D c k /
                            thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformFiber D c k)) := by
                    refine Finset.sum_congr rfl ?_
                    intro k hk
                    ring
            _ = (∑ k, D.fineLaw c k *
                    Real.log
                      (D.coarseLaw c /
                        thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformCoarse D c)) +
                  ∑ k, D.fineLaw c k *
                    Real.log
                      (thm_xi_time_part64ac_abelian_quotient_kl_chain_conditionalFiber D c k /
                        thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformFiber D c k) := by
                    rw [Finset.sum_add_distrib]
    _ =
        ∑ c,
          (D.coarseLaw c *
              Real.log
                (D.coarseLaw c /
                  thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformCoarse D c) +
            ∑ k, D.fineLaw c k *
              Real.log
                (thm_xi_time_part64ac_abelian_quotient_kl_chain_conditionalFiber D c k /
                  thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformFiber D c k)) := by
          refine Finset.sum_congr rfl ?_
          intro c hc
          rw [← D.hpush c, Finset.sum_mul]
    _ =
        thm_xi_time_part64ac_abelian_quotient_kl_chain_coarseKL D +
          ∑ c, ∑ k, D.fineLaw c k *
            Real.log
              (thm_xi_time_part64ac_abelian_quotient_kl_chain_conditionalFiber D c k /
                thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformFiber D c k) := by
          unfold thm_xi_time_part64ac_abelian_quotient_kl_chain_coarseKL
          rw [Finset.sum_add_distrib]
    _ =
        thm_xi_time_part64ac_abelian_quotient_kl_chain_coarseKL D +
          ∑ c, D.coarseLaw c *
            thm_xi_time_part64ac_abelian_quotient_kl_chain_fiberKL D c := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro c hc
          unfold thm_xi_time_part64ac_abelian_quotient_kl_chain_fiberKL
          calc
            ∑ k,
                D.fineLaw c k *
                  Real.log
                    (thm_xi_time_part64ac_abelian_quotient_kl_chain_conditionalFiber D c k /
                      thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformFiber D c k)
                =
                  ∑ k,
                    (D.coarseLaw c *
                      thm_xi_time_part64ac_abelian_quotient_kl_chain_conditionalFiber D c k) *
                      Real.log
                        (thm_xi_time_part64ac_abelian_quotient_kl_chain_conditionalFiber D c k /
                          thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformFiber D c k) := by
                    refine Finset.sum_congr rfl ?_
                    intro k hk
                    rw [D.thm_xi_time_part64ac_abelian_quotient_kl_chain_fine_factor c k]
            _ = D.coarseLaw c *
                  ∑ k,
                    thm_xi_time_part64ac_abelian_quotient_kl_chain_conditionalFiber D c k *
                      Real.log
                        (thm_xi_time_part64ac_abelian_quotient_kl_chain_conditionalFiber D c k /
                          thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformFiber D c k) := by
                    rw [Finset.mul_sum]
                    refine Finset.sum_congr rfl ?_
                    intro k hk
                    ring

end XiTimePart64acAbelianQuotientKlChainData

/-- Paper label: `thm:xi-time-part64ac-abelian-quotient-kl-chain`. In the concrete finite
product model `G₂ = G₁ × K`, the Haar law on the fine group factors as coarse Haar times the
uniform fiber law, and the KL divergence splits exactly into the coarse contribution plus the
average fiberwise conditional KL term. -/
theorem paper_xi_time_part64ac_abelian_quotient_kl_chain
    (D : Omega.Zeta.XiTimePart64acAbelianQuotientKlChainData) : D.statement := by
  refine ⟨?_, ?_, D.thm_xi_time_part64ac_abelian_quotient_kl_chain_identity⟩
  · intro c k
    exact D.thm_xi_time_part64ac_abelian_quotient_kl_chain_uniformFine_factor c k
  · intro c k
    exact D.thm_xi_time_part64ac_abelian_quotient_kl_chain_fine_factor c k

end

end Omega.Zeta
