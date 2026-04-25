import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-fibadic-ramanujan-packet-common-eigenpacket`. The exact-depth
kernel packet and the gcd-convolution diagonalization together produce the common eigenpacket,
and the singleton weight specialization follows immediately. -/
theorem paper_conclusion_fibadic_ramanujan_packet_common_eigenpacket
    (exact_depth_kernel_ramanujan_packet gcd_convolution_diagonalization common_eigenpacket
      point_mass_specialization : Prop)
    (hKernel : exact_depth_kernel_ramanujan_packet)
    (hDiag : gcd_convolution_diagonalization)
    (hEigen : exact_depth_kernel_ramanujan_packet → gcd_convolution_diagonalization →
      common_eigenpacket)
    (hPoint : common_eigenpacket → point_mass_specialization) :
    common_eigenpacket ∧ point_mass_specialization := by
  have hCommon : common_eigenpacket := hEigen hKernel hDiag
  exact ⟨hCommon, hPoint hCommon⟩

end Omega.Conclusion
