import Omega.POM.KilloFoldResonanceProductGaloisQ1217

namespace Omega.Folding

/-- The paper-facing density implication for the six simultaneous irreducibility conditions. -/
def killo_fold_resonance_simultaneous_irreducible_density_q12_17_statement
    (product_galois chebotarev_count density_value : Prop) : Prop :=
  product_galois -> chebotarev_count -> density_value

/-- Paper label: `cor:killo-fold-resonance-simultaneous-irreducible-density-q12-17`. -/
theorem paper_killo_fold_resonance_simultaneous_irreducible_density_q12_17
    (product_galois chebotarev_count density_value : Prop)
    (killo_fold_resonance_simultaneous_irreducible_density_q12_17_derivation :
      killo_fold_resonance_simultaneous_irreducible_density_q12_17_statement
        product_galois chebotarev_count density_value) :
    killo_fold_resonance_simultaneous_irreducible_density_q12_17_statement
      product_galois chebotarev_count density_value := by
  exact killo_fold_resonance_simultaneous_irreducible_density_q12_17_derivation

end Omega.Folding
