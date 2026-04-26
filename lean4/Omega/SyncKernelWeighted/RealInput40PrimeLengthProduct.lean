import Omega.POM.PrimitivePrimeLucas

namespace Omega.SyncKernelWeighted

/-- Paper label: `cor:real-input-40-prime-length-product`. The primitive prime-length orbit count
already has the Lucas closed form, so the synchronization-kernel wrapper is immediate. -/
theorem paper_real_input_40_prime_length_product (p : Nat) (hp : Nat.Prime p) (hodd : p ≠ 2) :
    Omega.POM.PrimitivePrimeLucas.primitiveOrbitCount p =
      Omega.Zeta.LucasBarrier.lucas p * (Omega.Zeta.LucasBarrier.lucas p - 1) / p := by
  let _ := hp
  let _ := hodd
  simp [Omega.POM.PrimitivePrimeLucas.primitiveOrbitCount]

end Omega.SyncKernelWeighted
