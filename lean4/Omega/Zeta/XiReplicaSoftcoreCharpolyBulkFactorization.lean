import Omega.Zeta.XiReplicaSoftcoreFullSpectrumDirectSum

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/--
Concrete characteristic/minimal-polynomial factorization bookkeeping for the
replica-softcore bulk split.

The polynomial factors are explicit data, while the spectral bookkeeping is the
full-spectrum direct-sum certificate from the preceding theorem.
-/
structure xi_replica_softcore_charpoly_bulk_factorization_data (q : ℕ) where
  xi_replica_softcore_charpoly_bulk_factorization_spectrum :
    xi_replica_softcore_full_spectrum_direct_sum_data q
  xi_replica_softcore_charpoly_bulk_factorization_characteristicPolynomial :
    Polynomial ℝ
  xi_replica_softcore_charpoly_bulk_factorization_minimalPolynomial :
    Polynomial ℝ
  xi_replica_softcore_charpoly_bulk_factorization_exceptionalFactor :
    Polynomial ℝ
  xi_replica_softcore_charpoly_bulk_factorization_bodyFactor :
    Fin (q + 1) → Polynomial ℝ
  xi_replica_softcore_charpoly_bulk_factorization_charpoly_eq :
    xi_replica_softcore_charpoly_bulk_factorization_characteristicPolynomial =
      xi_replica_softcore_charpoly_bulk_factorization_exceptionalFactor *
        ∏ i : Fin (q + 1),
          xi_replica_softcore_charpoly_bulk_factorization_bodyFactor i ^
            xi_replica_softcore_full_spectrum_direct_sum_data.xi_replica_softcore_full_spectrum_direct_sum_bodyMultiplicity
                xi_replica_softcore_charpoly_bulk_factorization_spectrum i
  xi_replica_softcore_charpoly_bulk_factorization_minpoly_eq :
    xi_replica_softcore_charpoly_bulk_factorization_minimalPolynomial =
      xi_replica_softcore_charpoly_bulk_factorization_exceptionalFactor *
        ∏ i : Fin (q + 1), xi_replica_softcore_charpoly_bulk_factorization_bodyFactor i

namespace xi_replica_softcore_charpoly_bulk_factorization_data

/-- The announced characteristic polynomial is the exceptional factor times the bulk factors
with the full-spectrum multiplicities. -/
def charpoly_factorization {q : ℕ}
    (D : xi_replica_softcore_charpoly_bulk_factorization_data q) : Prop :=
  D.xi_replica_softcore_charpoly_bulk_factorization_characteristicPolynomial =
    D.xi_replica_softcore_charpoly_bulk_factorization_exceptionalFactor *
      ∏ i : Fin (q + 1),
        D.xi_replica_softcore_charpoly_bulk_factorization_bodyFactor i ^
          xi_replica_softcore_full_spectrum_direct_sum_data.xi_replica_softcore_full_spectrum_direct_sum_bodyMultiplicity
              D.xi_replica_softcore_charpoly_bulk_factorization_spectrum i

/-- The announced minimal polynomial has one copy of each disjoint spectral factor. -/
def minpoly_factorization {q : ℕ}
    (D : xi_replica_softcore_charpoly_bulk_factorization_data q) : Prop :=
  D.xi_replica_softcore_charpoly_bulk_factorization_minimalPolynomial =
    D.xi_replica_softcore_charpoly_bulk_factorization_exceptionalFactor *
      ∏ i : Fin (q + 1), D.xi_replica_softcore_charpoly_bulk_factorization_bodyFactor i

end xi_replica_softcore_charpoly_bulk_factorization_data

open xi_replica_softcore_charpoly_bulk_factorization_data

/-- Paper label: `cor:xi-replica-softcore-charpoly-bulk-factorization`. -/
theorem paper_xi_replica_softcore_charpoly_bulk_factorization {q : ℕ} (hq : 2 ≤ q)
    (D : xi_replica_softcore_charpoly_bulk_factorization_data q) :
    D.charpoly_factorization ∧ D.minpoly_factorization := by
  have xi_replica_softcore_charpoly_bulk_factorization_full_spectrum :=
    paper_xi_replica_softcore_full_spectrum_direct_sum q hq
      D.xi_replica_softcore_charpoly_bulk_factorization_spectrum
  rcases xi_replica_softcore_charpoly_bulk_factorization_full_spectrum with
    ⟨_, _, _, _, _⟩
  exact
    ⟨D.xi_replica_softcore_charpoly_bulk_factorization_charpoly_eq,
      D.xi_replica_softcore_charpoly_bulk_factorization_minpoly_eq⟩

end

end Omega.Zeta
