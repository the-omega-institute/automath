import Mathlib.Tactic
import Omega.Folding.KilloNaturalExtensionBranchRegister

namespace Omega.Zeta

/-- Paper label:
`cor:xi-time-part62ba-primeslice-natural-extension-prefix-godelization`. -/
theorem paper_xi_time_part62ba_primeslice_natural_extension_prefix_godelization {X : Type*}
    (T : X -> X) (beta : X -> Nat) (decode : X -> Nat -> X)
    (hdecode : forall x, decode (T x) (beta x) = x) :
    forall (k : Nat) (s t : Omega.Folding.NaturalExtension T), s.1 0 = t.1 0 ->
      (forall n, n < k -> beta (s.1 (n + 1)) = beta (t.1 (n + 1))) ->
        forall n, n <= k -> s.1 n = t.1 n := by
  intro k
  induction k with
  | zero =>
      intro s t h0 _ n hn
      have hn0 : n = 0 := by omega
      simpa [hn0] using h0
  | succ k ih =>
      intro s t h0 hbranch n hn
      cases n with
      | zero =>
          exact h0
      | succ n =>
          have hn_le : n <= k := by omega
          have hprev : s.1 n = t.1 n :=
            ih s t h0 (fun m hm => hbranch m (by omega)) n hn_le
          have hlabel : beta (s.1 (n + 1)) = beta (t.1 (n + 1)) :=
            hbranch n (by omega)
          calc
            s.1 (n + 1) = decode (T (s.1 (n + 1))) (beta (s.1 (n + 1))) := by
              exact (hdecode (s.1 (n + 1))).symm
            _ = decode (s.1 n) (beta (s.1 (n + 1))) := by
              rw [s.2 n]
            _ = decode (t.1 n) (beta (t.1 (n + 1))) := by
              rw [hprev, hlabel]
            _ = decode (T (t.1 (n + 1))) (beta (t.1 (n + 1))) := by
              rw [t.2 n]
            _ = t.1 (n + 1) := by
              exact hdecode (t.1 (n + 1))

end Omega.Zeta
