import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- The trace contribution of the tensor block `F ⊗ F` in the real-input-40 splitting model. -/
def realInput40TensorTrace (u v : ℤ) (n : ℕ) : ℤ :=
  u ^ (2 * n) + 2 * (u * v) ^ n + v ^ (2 * n)

/-- The signed trace contributed by the `-F` block. -/
def realInput40SignedTrace (u v : ℤ) (n : ℕ) : ℤ :=
  u ^ n + v ^ n

/-- The block trace of `M = (F ⊗ F) ⊞ (-F)`, written with the parity sign made explicit. -/
def realInput40ArtinTrace (u v : ℤ) (n : ℕ) : ℤ :=
  realInput40TensorTrace u v n +
    if n % 2 = 0 then realInput40SignedTrace u v n else -realInput40SignedTrace u v n

/-- The extra half-orbit term that survives only on the `2 mod 4` branch. -/
def realInput40HalfOrbitCorrection (u v : ℤ) (n : ℕ) : ℤ :=
  if n % 4 = 2 then u ^ (n / 2) + v ^ (n / 2) else 0

/-- Primitive-orbit count read off from the parity split. The `2 mod 4` branch carries the
additional `π_(n/2)` correction. -/
def realInput40PrimeArtinOrbitCount (u v : ℤ) (n : ℕ) : ℤ :=
  if n % 2 = 1 then
    realInput40TensorTrace u v n - realInput40SignedTrace u v n
  else if n % 4 = 0 then
    realInput40TensorTrace u v n + realInput40SignedTrace u v n
  else
    realInput40TensorTrace u v n + realInput40SignedTrace u v n +
      realInput40HalfOrbitCorrection u v n

/-- Paper label: `thm:real-input-40-prime-artin-splitting`.
For the concrete real-input-40 block decomposition, the trace splits by parity, and after the
parity/`4`-divisibility case split the primitive-orbit count carries an extra half-orbit term
exactly on the `n ≡ 2 [ZMOD 4]` branch. -/
theorem paper_real_input_40_prime_artin_splitting (u v : ℤ) (n : ℕ) :
    realInput40PrimeArtinOrbitCount u v n =
      if n % 2 = 1 then
        realInput40TensorTrace u v n - realInput40SignedTrace u v n
      else if n % 4 = 0 then
        realInput40TensorTrace u v n + realInput40SignedTrace u v n
      else
        realInput40ArtinTrace u v n + (u ^ (n / 2) + v ^ (n / 2)) := by
  by_cases hodd : n % 2 = 1
  · have hmod : n % 2 ≠ 0 := by omega
    simp [realInput40PrimeArtinOrbitCount, realInput40SignedTrace, hodd]
  · by_cases hfour : n % 4 = 0
    · simp [realInput40PrimeArtinOrbitCount, hodd, hfour]
    · have hmod : n % 2 = 0 := by omega
      have htwo : n % 4 = 2 := by omega
      simp [realInput40PrimeArtinOrbitCount, realInput40ArtinTrace, realInput40SignedTrace, hmod,
        htwo, realInput40HalfOrbitCorrection]

end Omega.SyncKernelWeighted
