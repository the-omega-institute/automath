import Omega.CircleDimension.ProCdimZhatEmbeddingCharacterization

namespace Omega.CircleDimension

/-- The CRT-reused product generator bound is the primewise maximum of the summed local generator
counts. -/
def proCdimCRTProduct (primes : Finset Nat) (f g : Nat → Nat) : Nat :=
  registerCirclePrimeSup primes (fun p => f p + g p)

private theorem registerCirclePrimeSup_eq_of_pointwise_eq'
    (primes : Finset Nat) (f g : Nat → Nat) (hfg : ∀ p ∈ primes, f p = g p) :
    registerCirclePrimeSup primes f = registerCirclePrimeSup primes g := by
  unfold registerCirclePrimeSup
  refine le_antisymm ?_ ?_
  · exact Finset.sup_le fun p hp => by
      simpa [hfg p hp] using (Finset.le_sup hp : g p ≤ primes.sup g)
  · exact Finset.sup_le fun p hp => by
      simpa [hfg p hp] using (Finset.le_sup hp : f p ≤ primes.sup f)

private theorem proCdimCRTProduct_eq_of_pointwise_eq
    (primes : Finset Nat) (f f' g g' : Nat → Nat)
    (hf : ∀ p ∈ primes, f p = f' p) (hg : ∀ p ∈ primes, g p = g' p) :
    proCdimCRTProduct primes f g = proCdimCRTProduct primes f' g' := by
  unfold proCdimCRTProduct
  refine registerCirclePrimeSup_eq_of_pointwise_eq' primes _ _ ?_
  intro p hp
  simp [hf p hp, hg p hp]

/-- The Sylow/CRT reuse package: the same primewise generator profile computes the `Ẑ`-embedding
dimension, and on products the local generator counts add before taking the primewise maximum.
    prop:cdim-pro-cdim-crt-reuse -/
theorem paper_cdim_pro_cdim_crt_reuse
    (primes : Finset Nat)
    (pcdimP pcdimQ pcdimProd : Nat)
    (zhatSurjectionP zhatSurjectionQ : Nat)
    (sylowP sylowQ modpP modpQ : Nat → Nat)
    (hSurjP : pcdimP = zhatSurjectionP)
    (hSurjQ : pcdimQ = zhatSurjectionQ)
    (hSylowP : pcdimP = registerCirclePrimeSup primes sylowP)
    (hSylowQ : pcdimQ = registerCirclePrimeSup primes sylowQ)
    (hModpP : ∀ p ∈ primes, modpP p = sylowP p)
    (hModpQ : ∀ p ∈ primes, modpQ p = sylowQ p)
    (hProd : pcdimProd = registerCirclePrimeSup primes (fun p => sylowP p + sylowQ p)) :
    pcdimP = proCdimZhatEmbeddingDim primes modpP ∧
      pcdimQ = proCdimZhatEmbeddingDim primes modpQ ∧
      pcdimProd = proCdimCRTProduct primes modpP modpQ := by
  have hP :=
    paper_cdim_pro_cdim_zhat_embedding_characterization primes pcdimP zhatSurjectionP
      (proCdimZhatEmbeddingDim primes modpP) sylowP modpP hSurjP hSylowP hModpP rfl
  have hQ :=
    paper_cdim_pro_cdim_zhat_embedding_characterization primes pcdimQ zhatSurjectionQ
      (proCdimZhatEmbeddingDim primes modpQ) sylowQ modpQ hSurjQ hSylowQ hModpQ rfl
  have hProdModp :
      registerCirclePrimeSup primes (fun p => sylowP p + sylowQ p) =
        proCdimCRTProduct primes modpP modpQ := by
    exact proCdimCRTProduct_eq_of_pointwise_eq primes _ _ _ _
      (by intro p hp; exact (hModpP p hp).symm)
      (by intro p hp; exact (hModpQ p hp).symm)
  exact ⟨hP, hQ, hProd.trans hProdModp⟩

end Omega.CircleDimension
