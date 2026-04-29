namespace Omega.POM

/-- Paper label: `prop:pom-a4t-charpoly-degenerate-galois`. -/
theorem paper_pom_a4t_charpoly_degenerate_galois
    (minusFactorization plusFactorization minusCubicS3 plusCubicS3 plusQuadraticC2
      plusQuadraticDisjoint minusGaloisS3 plusGaloisS3xC2 : Prop)
    (hminus : minusFactorization → minusCubicS3 → minusGaloisS3)
    (hplus :
      plusFactorization → plusCubicS3 → plusQuadraticC2 → plusQuadraticDisjoint →
        plusGaloisS3xC2)
    (hmf : minusFactorization) (hmc : minusCubicS3) (hpf : plusFactorization)
    (hpc : plusCubicS3) (hpq : plusQuadraticC2) (hpd : plusQuadraticDisjoint) :
    minusGaloisS3 ∧ plusGaloisS3xC2 := by
  exact ⟨hminus hmf hmc, hplus hpf hpc hpq hpd⟩

end Omega.POM
