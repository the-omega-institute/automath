import Omega.Conclusion.PrimeRegister

namespace Omega.Conclusion

/-- Hexadecimal BBP-address specialization of the side-information lower bound.
    prop:conclusion-foldgauge-pi-bbp-hex-address-rate -/
theorem paper_conclusion_foldgauge_pi_bbp_hex_address_rate (m L : ℕ)
    (encode :
      Fin (2 ^ m) ↪
        Fin (Nat.fib (m + 2)) ×
          Fin (Finset.sum (Finset.range (L + 1)) (fun i => 16 ^ i))) :
    Nat.clog 16 (2 ^ m / Nat.fib (m + 2)) ≤ L + 1 := by
  exact paper_conclusion_side_info_length_lower_bound m 16 L (by norm_num) encode

end Omega.Conclusion
