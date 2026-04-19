namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the Gödel prime-density holography and CLT package.
    thm:spg-godel-prime-density-holography-clt -/
theorem paper_spg_godel_prime_density_holography_clt
    (densityHolography gaussianFluctuation sqrtNLogNScale : Prop)
    (hDensity : densityHolography) (hCLT : gaussianFluctuation) (hScale : sqrtNLogNScale) :
    densityHolography ∧ gaussianFluctuation ∧ sqrtNLogNScale := by
  exact ⟨hDensity, hCLT, hScale⟩

end Omega.SPG
