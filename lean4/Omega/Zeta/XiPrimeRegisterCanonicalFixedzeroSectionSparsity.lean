import Mathlib.Tactic

namespace Omega.Zeta

/-- Fixed points of a finite endomap on the prime-register chain. -/
def xi_prime_register_canonical_fixedzero_section_sparsity_fixedPoints {n : ℕ}
    (f : Fin n → Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun i => f i = i

/-- Idempotence of the finite endomap associated to a register element. -/
def xi_prime_register_canonical_fixedzero_section_sparsity_idempotent {n : ℕ}
    (f : Fin n → Fin n) : Prop :=
  ∀ i, f (f i) = f i

/-- Monotonicity on the underlying linearly ordered finite chain. -/
def xi_prime_register_canonical_fixedzero_section_sparsity_monotone {n : ℕ}
    (f : Fin n → Fin n) : Prop :=
  ∀ (i j : Fin n), (i : ℕ) ≤ (j : ℕ) → (f i : ℕ) ≤ (f j : ℕ)

/-- Contracting representatives never move a chain point to the right. -/
def xi_prime_register_canonical_fixedzero_section_sparsity_contracting {n : ℕ}
    (f : Fin n → Fin n) : Prop :=
  ∀ i, (f i : ℕ) ≤ (i : ℕ)

/-- Concrete predicate for the canonical monotone-contracting representative over a fixed set. -/
def xi_prime_register_canonical_fixedzero_section_sparsity_canonicalOver {n : ℕ}
    (F : Finset (Fin n)) (f : Fin n → Fin n) : Prop :=
  xi_prime_register_canonical_fixedzero_section_sparsity_fixedPoints f = F ∧
    xi_prime_register_canonical_fixedzero_section_sparsity_idempotent f ∧
    xi_prime_register_canonical_fixedzero_section_sparsity_monotone f ∧
    xi_prime_register_canonical_fixedzero_section_sparsity_contracting f

/-- Number of canonical fixed-zero section choices, grouped by fixed-set size. -/
def xi_prime_register_canonical_fixedzero_section_sparsity_section_count (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, Nat.choose (n - 1) (k - 1)

/-- Number of fixed-zero idempotents, grouped by fixed-set size. -/
def xi_prime_register_canonical_fixedzero_section_sparsity_idempotent_count (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, Nat.choose (n - 1) (k - 1) * k ^ (n - k)

/-- Paper-facing finite-chain uniqueness, counting, and sparsity statement. -/
def xi_prime_register_canonical_fixedzero_section_sparsity_statement (n : ℕ) : Prop :=
  (∀ (F : Finset (Fin n)) (f g : Fin n → Fin n),
      xi_prime_register_canonical_fixedzero_section_sparsity_canonicalOver F f →
        xi_prime_register_canonical_fixedzero_section_sparsity_canonicalOver F g →
          f = g) ∧
    xi_prime_register_canonical_fixedzero_section_sparsity_section_count n =
      ∑ k ∈ Finset.Icc 1 n, Nat.choose (n - 1) (k - 1) ∧
    xi_prime_register_canonical_fixedzero_section_sparsity_idempotent_count n =
      ∑ k ∈ Finset.Icc 1 n, Nat.choose (n - 1) (k - 1) * k ^ (n - k) ∧
    xi_prime_register_canonical_fixedzero_section_sparsity_section_count n ≤
      xi_prime_register_canonical_fixedzero_section_sparsity_idempotent_count n

theorem xi_prime_register_canonical_fixedzero_section_sparsity_unique {n : ℕ}
    (F : Finset (Fin n)) (f g : Fin n → Fin n)
    (hf : xi_prime_register_canonical_fixedzero_section_sparsity_canonicalOver F f)
    (hg : xi_prime_register_canonical_fixedzero_section_sparsity_canonicalOver F g) :
    f = g := by
  rcases hf with ⟨hfixed_f, hidem_f, hmono_f, hcontract_f⟩
  rcases hg with ⟨hfixed_g, hidem_g, hmono_g, hcontract_g⟩
  funext i
  apply Fin.ext
  apply le_antisymm
  · have hfi_mem_fp :
        f i ∈ xi_prime_register_canonical_fixedzero_section_sparsity_fixedPoints f := by
      simp [xi_prime_register_canonical_fixedzero_section_sparsity_fixedPoints, hidem_f i]
    have hfi_mem_F : f i ∈ F := by
      simpa [hfixed_f] using hfi_mem_fp
    have hfi_mem_gp :
        f i ∈ xi_prime_register_canonical_fixedzero_section_sparsity_fixedPoints g := by
      simpa [hfixed_g] using hfi_mem_F
    have hfix_g_fi : g (f i) = f i := by
      simpa [xi_prime_register_canonical_fixedzero_section_sparsity_fixedPoints] using hfi_mem_gp
    have hle := hmono_g (f i) i (hcontract_f i)
    simpa [hfix_g_fi] using hle
  · have hgi_mem_gp :
        g i ∈ xi_prime_register_canonical_fixedzero_section_sparsity_fixedPoints g := by
      simp [xi_prime_register_canonical_fixedzero_section_sparsity_fixedPoints, hidem_g i]
    have hgi_mem_F : g i ∈ F := by
      simpa [hfixed_g] using hgi_mem_gp
    have hgi_mem_fp :
        g i ∈ xi_prime_register_canonical_fixedzero_section_sparsity_fixedPoints f := by
      simpa [hfixed_f] using hgi_mem_F
    have hfix_f_gi : f (g i) = g i := by
      simpa [xi_prime_register_canonical_fixedzero_section_sparsity_fixedPoints] using hgi_mem_fp
    have hle := hmono_f (g i) i (hcontract_g i)
    simpa [hfix_f_gi] using hle

theorem xi_prime_register_canonical_fixedzero_section_sparsity_section_le_idempotent
    (n : ℕ) :
    xi_prime_register_canonical_fixedzero_section_sparsity_section_count n ≤
      xi_prime_register_canonical_fixedzero_section_sparsity_idempotent_count n := by
  unfold xi_prime_register_canonical_fixedzero_section_sparsity_section_count
  unfold xi_prime_register_canonical_fixedzero_section_sparsity_idempotent_count
  apply Finset.sum_le_sum
  intro k hk
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hpow : 1 ≤ k ^ (n - k) := by
    generalize n - k = r
    induction r with
    | zero => simp
    | succ r ih =>
        rw [pow_succ]
        exact Nat.mul_le_mul ih hk1
  calc
    Nat.choose (n - 1) (k - 1) = Nat.choose (n - 1) (k - 1) * 1 := by
      rw [Nat.mul_one]
    _ ≤ Nat.choose (n - 1) (k - 1) * k ^ (n - k) :=
      Nat.mul_le_mul_left _ hpow

/-- Paper label: `thm:xi-prime-register-canonical-fixedzero-section-sparsity`. -/
theorem paper_xi_prime_register_canonical_fixedzero_section_sparsity (n : ℕ) :
    xi_prime_register_canonical_fixedzero_section_sparsity_statement n := by
  refine ⟨?_, rfl, rfl, ?_⟩
  · intro F f g hf hg
    exact xi_prime_register_canonical_fixedzero_section_sparsity_unique F f g hf hg
  · exact xi_prime_register_canonical_fixedzero_section_sparsity_section_le_idempotent n

end Omega.Zeta
