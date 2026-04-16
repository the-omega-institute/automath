import Omega.CircleDimension.AtomicDefectHankelProny

namespace Omega.TypedAddressBiaxialCompletion

/-- Chapter-local notation for the typed-address comoving Hankel package: general position
forces the Vandermonde/Hankel factorization, which in turn yields the rank certificate. -/
structure ComovingHankelData where
  kappa : ℕ
  generalPosition : Prop
  hankelFactorization : Prop
  hankelRankCertificate : Prop
  factorization_of_generalPosition : generalPosition → hankelFactorization
  rank_of_factorization : hankelFactorization → hankelRankCertificate

/-- Paper-facing typed-address restatement of the CircleDimension atomic-defect
Hankel--Prony wrapper.
    prop:typed-address-biaxial-completion-comoving-hankel -/
theorem paper_typed_address_biaxial_completion_comoving_hankel
    (D : ComovingHankelData) (hgp : D.generalPosition) :
    D.hankelFactorization ∧ D.hankelRankCertificate := by
  exact Omega.CircleDimension.paper_cdim_atomic_defect_hankel_prony
    D.generalPosition D.hankelFactorization D.hankelRankCertificate
    (D.hankelFactorization ∧ D.hankelRankCertificate) hgp
    D.factorization_of_generalPosition D.rank_of_factorization
    (fun hFactor hRank => ⟨hFactor, hRank⟩)

end Omega.TypedAddressBiaxialCompletion
