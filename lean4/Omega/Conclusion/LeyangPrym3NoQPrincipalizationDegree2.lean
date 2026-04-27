namespace Omega.Conclusion

/-- Named Galois-image hypothesis for the Prym kernel action. -/
def conclusion_leyang_prym3_no_q_principalization_degree2_galoisImageS3
    (galoisImageS3 : Prop) : Prop :=
  galoisImageS3

/-- Named transitivity assertion for the three nonzero order-two kernel points. -/
def conclusion_leyang_prym3_no_q_principalization_degree2_transitiveNonzeroKernel
    (transitiveNonzeroKernel : Prop) : Prop :=
  transitiveNonzeroKernel

/-- Named obstruction to a rational order-two subgroup of the kernel. -/
def conclusion_leyang_prym3_no_q_principalization_degree2_noQOrderTwoSubgroup
    (noQOrderTwoSubgroup : Prop) : Prop :=
  noQOrderTwoSubgroup

/-- Named degree-two principalization obstruction. -/
def conclusion_leyang_prym3_no_q_principalization_degree2_noDegreeTwoPrincipalization
    (noDegreeTwoPrincipalization : Prop) : Prop :=
  noDegreeTwoPrincipalization

/-- Compose S3 transitivity, subgroup obstruction, and degree-two obstruction. -/
theorem conclusion_leyang_prym3_no_q_principalization_degree2_from_s3
    (galoisImageS3 transitiveNonzeroKernel noQOrderTwoSubgroup
      noDegreeTwoPrincipalization : Prop)
    (htrans : galoisImageS3 → transitiveNonzeroKernel)
    (hnoSub : transitiveNonzeroKernel → noQOrderTwoSubgroup)
    (hnoDeg : noQOrderTwoSubgroup → noDegreeTwoPrincipalization)
    (hS3 : galoisImageS3) :
    noDegreeTwoPrincipalization := by
  exact hnoDeg (hnoSub (htrans hS3))

/-- Paper label: `cor:conclusion-leyang-prym3-no-q-principalization-degree2`. -/
theorem paper_conclusion_leyang_prym3_no_q_principalization_degree2
    (galoisImageS3 transitiveNonzeroKernel noQOrderTwoSubgroup
      noDegreeTwoPrincipalization : Prop)
    (htrans : galoisImageS3 → transitiveNonzeroKernel)
    (hnoSub : transitiveNonzeroKernel → noQOrderTwoSubgroup)
    (hnoDeg : noQOrderTwoSubgroup → noDegreeTwoPrincipalization)
    (hS3 : galoisImageS3) :
    noDegreeTwoPrincipalization := by
  exact conclusion_leyang_prym3_no_q_principalization_degree2_from_s3
    galoisImageS3 transitiveNonzeroKernel noQOrderTwoSubgroup noDegreeTwoPrincipalization
    htrans hnoSub hnoDeg hS3

end Omega.Conclusion
