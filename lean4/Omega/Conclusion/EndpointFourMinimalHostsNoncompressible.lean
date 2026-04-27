import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete paper-facing data for the endpoint four-host noncompression wrapper. -/
abbrev conclusion_endpoint_four_minimal_hosts_noncompressible_Data := PUnit

namespace conclusion_endpoint_four_minimal_hosts_noncompressible_Data

/-- The half-entropy pseudodeterminant-tower host. -/
def halfentropy_pdet_host : Fin 4 := ⟨0, by norm_num⟩

/-- The single-eigenpair threshold-atlas host. -/
def eigenpair_threshold_host : Fin 4 := ⟨1, by norm_num⟩

/-- The one-target Laguerre denominator host. -/
def laguerre_denominator_host : Fin 4 := ⟨2, by norm_num⟩

/-- The one-bit stopping-evidence host. -/
def stopping_onebit_host : Fin 4 := ⟨3, by norm_num⟩

/-- Host certificate coordinates for the four endpoint layers. -/
def host_certificate (h : Fin 4) : ℕ := h.1

/-- No fixed three-coordinate finite host can injectively carry all four endpoint layers. -/
def no_unified_finite_coordinate_obstruction : Prop :=
  ¬ ∃ encode : Fin 4 → Fin 3, Function.Injective encode

/-- The four endpoint hosts are distinct and cannot be compressed to one smaller finite host. -/
def hosts_pairwise_noncompressible
    (_D : conclusion_endpoint_four_minimal_hosts_noncompressible_Data) : Prop :=
  Function.Injective host_certificate ∧
    Fintype.card (Fin 4) = 4 ∧
    ({halfentropy_pdet_host, eigenpair_threshold_host, laguerre_denominator_host,
      stopping_onebit_host} : Finset (Fin 4)) = Finset.univ ∧
    no_unified_finite_coordinate_obstruction

end conclusion_endpoint_four_minimal_hosts_noncompressible_Data

open conclusion_endpoint_four_minimal_hosts_noncompressible_Data

/-- Paper label: `thm:conclusion-endpoint-four-minimal-hosts-noncompressible`.

The four endpoint certificates are represented by four distinct finite host coordinates, and the
finite obstruction states that they cannot be carried injectively by only three coordinates. -/
theorem paper_conclusion_endpoint_four_minimal_hosts_noncompressible
    (D : conclusion_endpoint_four_minimal_hosts_noncompressible_Data) :
    D.hosts_pairwise_noncompressible := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b h
    exact Fin.ext h
  · rfl
  · ext h
    fin_cases h <;> simp [halfentropy_pdet_host, eigenpair_threshold_host,
      laguerre_denominator_host, stopping_onebit_host]
  · intro h
    rcases h with ⟨encode, hencode⟩
    have hle : Fintype.card (Fin 4) ≤ Fintype.card (Fin 3) :=
      Fintype.card_le_of_injective encode hencode
    norm_num at hle

end Omega.Conclusion
