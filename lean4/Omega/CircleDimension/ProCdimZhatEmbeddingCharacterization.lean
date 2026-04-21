import Omega.CircleDimension.RegisterCircleModpFormula

namespace Omega.CircleDimension

/-- The candidate `Ẑ`-embedding dimension obtained by padding the Sylow generator counts to a
common finite support and taking their supremum. -/
def proCdimZhatEmbeddingDim (primes : Finset Nat) (modpRank : Nat → Nat) : Nat :=
  registerCirclePrimeSup primes modpRank

/-- The profinite circle dimension agrees with the minimal `Ẑ`-embedding dimension once both are
identified with the supremum of the local generator counts. The existing register-circle mod-`p`
formula supplies the comparison between the Sylow ranks and the padded `Ẑ`-coordinates.
    thm:cdim-pro-cdim-zhat-embedding-characterization -/
theorem paper_cdim_pro_cdim_zhat_embedding_characterization
    (primes : Finset Nat) (pcdim zhatSurjectionDim minEmbeddingDim : Nat)
    (sylowRank modpRank : Nat → Nat)
    (hSurjection : pcdim = zhatSurjectionDim)
    (hSylow : pcdim = registerCirclePrimeSup primes sylowRank)
    (hModp : ∀ p ∈ primes, modpRank p = sylowRank p)
    (hMin : minEmbeddingDim = proCdimZhatEmbeddingDim primes modpRank) :
    pcdim = minEmbeddingDim := by
  let K : RegisterCircleModpData :=
    { primes := primes
      pcdim := pcdim
      zhatSurjectionDim := zhatSurjectionDim
      sylowPcdim := sylowRank
      modpDim := modpRank
      sylowModpDim := sylowRank }
  have hFormula :=
    paper_cdim_register_circle_modp_formula (K := K)
      (by simpa [K] using hSurjection)
      (by simpa [K] using hSylow)
      (by
        intro p hp
        simpa [K] using hModp p hp)
      (by
        intro p hp
        simp [K])
  have hEmbedding : pcdim = proCdimZhatEmbeddingDim primes modpRank := by
    simpa [K, proCdimZhatEmbeddingDim] using hFormula.2.1
  exact hEmbedding.trans hMin.symm

end Omega.CircleDimension
