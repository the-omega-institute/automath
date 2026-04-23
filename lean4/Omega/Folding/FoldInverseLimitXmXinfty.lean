import Omega.Folding.Fiber
import Omega.Folding.InverseLimit

namespace Omega.Folding

/-- Paper label: `prop:fold-inverse-limit-xm-xinfty`. The inverse system of stable prefixes has
limit `X_∞`, its prefix projections are coherent and surjective, and every finite window `X_m`
retains the Zeckendorf range bijection with `Fin (F_{m+2})`. -/
theorem paper_fold_inverse_limit_xm_xinfty (m : Nat) :
    Nonempty (Omega.X.CompatibleFamily ≃ Omega.X.XInfinity) ∧
      (∀ a : Omega.X.XInfinity,
        Omega.stableValue (Omega.X.prefixWord a (m + 1)) % Nat.fib (m + 2) =
          Omega.stableValue (Omega.X.prefixWord a m)) ∧
      Function.Surjective (fun a : Omega.X.XInfinity => Omega.X.prefixWord a m) ∧
      Function.Bijective (Omega.stableValueFin (m := m)) ∧
      (∀ n : Nat, n < Nat.fib (m + 2) → Omega.stableValue (Omega.X.ofNat m n) = n) := by
  refine ⟨⟨Omega.X.inverseLimitEquiv⟩, ?_, Omega.X.prefixWord_surjective m,
    (paper_zeckendorf_range_bijection m).1, (paper_zeckendorf_range_bijection m).2⟩
  intro a
  exact Omega.X.prefixWord_stableValue_coherent a m

end Omega.Folding
