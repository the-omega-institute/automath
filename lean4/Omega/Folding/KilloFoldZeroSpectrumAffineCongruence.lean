import Mathlib
import Omega.Core.Fib
import Omega.Folding.FiberConvolutionKernelZeroSpectrum

namespace Omega.Folding

private lemma card_range_filter_modEq (n q r : ℕ) (hq : q ∣ n) :
    ((Finset.range n).filter fun a => a ≡ r [MOD q]).card = n / q := by
  rcases hq with ⟨m, rfl⟩
  by_cases hq0 : q = 0
  · subst hq0
    simp
  · let r0 := r % q
    have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
    have hr0_lt : r0 < q := Nat.mod_lt _ hqpos
    have hr0_mod : r0 ≡ r [MOD q] := by
      dsimp [r0]
      exact Nat.mod_modEq _ _
    calc
      ((Finset.range (q * m)).filter fun a => a ≡ r [MOD q]).card = (Finset.range m).card := by
        refine (Finset.card_bij (s := Finset.range m)
          (t := (Finset.range (q * m)).filter fun a => a ≡ r [MOD q])
          (i := fun k _ => r0 + q * k) ?_ ?_ ?_).symm
        · intro k hk
          rw [Finset.mem_filter, Finset.mem_range]
          refine ⟨?_, ?_⟩
          · have hk' : k < m := Finset.mem_range.mp hk
            have hk1 : k + 1 ≤ m := Nat.succ_le_of_lt hk'
            calc
              r0 + q * k < q + q * k := Nat.add_lt_add_right hr0_lt _
              _ = q * (k + 1) := by rw [Nat.add_comm, Nat.mul_add, Nat.mul_one]
              _ ≤ q * m := Nat.mul_le_mul_left q hk1
          · have hmul : r0 + q * k ≡ r0 [MOD q] := by
              simpa [Nat.mul_comm] using
                (Nat.ModEq.add_right r0 ((dvd_mul_right q k).modEq_zero_nat))
            exact hmul.trans hr0_mod
        · intro a ha b hb hab
          dsimp at hab
          rw [Nat.mul_comm q a, Nat.mul_comm q b] at hab
          exact Nat.mul_right_cancel hqpos (Nat.add_left_cancel hab)
        · intro a ha
          rw [Finset.mem_filter] at ha
          have hmod : a % q = r0 := by
            exact Nat.mod_eq_of_modEq (ha.2.trans hr0_mod.symm) hr0_lt
          refine ⟨a / q, ?_, ?_⟩
          · rw [Finset.mem_range]
            by_contra hnot
            have hm_le : m ≤ a / q := Nat.not_lt.mp hnot
            have : q * m ≤ a := by
              calc
                q * m ≤ q * (a / q) := Nat.mul_le_mul_left q hm_le
                _ ≤ q * (a / q) + a % q := Nat.le_add_right _ _
                _ = a := by simpa [Nat.add_comm] using (Nat.mod_add_div a q)
            exact (Nat.not_le_of_gt (Finset.mem_range.mp ha.1)) this
          · have hdecomp : a = r0 + q * (a / q) := by
              simpa [hmod, Nat.add_comm] using (Nat.mod_add_div a q).symm
            exact hdecomp.symm
      _ = m := by simp
      _ = (q * m) / q := by
        symm
        exact Nat.mul_div_right m hqpos

private lemma card_univ_filter_fin_modEq (M q r : ℕ) (hq : q ∣ M) :
    (Finset.univ.filter (fun k : Fin M => k.1 ≡ r [MOD q])).card = M / q := by
  have hEq :
      (Finset.univ.filter (fun k : Fin M => k.1 ≡ r [MOD q])).image Fin.valEmbedding =
        ((Finset.range M).filter fun a => a ≡ r [MOD q]) := by
    ext a
    constructor
    · intro ha
      rcases Finset.mem_image.mp ha with ⟨k, hk, rfl⟩
      simpa [Finset.mem_filter] using hk
    · intro ha
      simp [Finset.mem_filter] at ha
      rcases ha with ⟨haM, har⟩
      refine Finset.mem_image.mpr ?_
      refine ⟨⟨a, haM⟩, ?_, rfl⟩
      simp [Finset.mem_filter, har]
  calc
    (Finset.univ.filter (fun k : Fin M => k.1 ≡ r [MOD q])).card =
        ((Finset.univ.filter (fun k : Fin M => k.1 ≡ r [MOD q])).image Fin.valEmbedding).card := by
          symm
          exact Finset.card_image_of_injective _ Fin.val_injective
    _ = ((Finset.range M).filter fun a => a ≡ r [MOD q]).card := by rw [hEq]
    _ = M / q := card_range_filter_modEq M q r hq

private lemma foldFiberSingletonZeroCoset_mem_iff (M j : ℕ) (k0 k : Fin M) :
    k ∈ foldFiberSingletonZeroCoset M j k0 ↔
      k.1 ≡ k0.1 [MOD M / Nat.gcd M (Nat.fib (j + 1))] := by
  have hMpos : 0 < M :=
    lt_of_lt_of_le (Nat.zero_lt_succ _) (Nat.succ_le_of_lt k.2)
  have hk :
      (k.1 * Nat.fib (j + 1)) ≡ (k0.1 * Nat.fib (j + 1)) [MOD M] ↔
        k ∈ foldFiberSingletonZeroCoset M j k0 := by
    simp [foldFiberSingletonZeroCoset, Nat.ModEq]
  constructor
  · intro h
    have hmod :
        k.1 * Nat.fib (j + 1) ≡ k0.1 * Nat.fib (j + 1) [MOD M] := by
      exact hk.mpr h
    simpa [Nat.mul_comm] using
      Nat.ModEq.cancel_right_div_gcd hMpos hmod
  · intro h
    have hmod :
        k.1 * Nat.fib (j + 1) ≡ k0.1 * Nat.fib (j + 1) [MOD M] := by
      have h' :
          k.1 ≡ k0.1 [MOD M / Nat.gcd M (Nat.fib (j + 1))] := h
      have hmulg :
          k.1 * Nat.fib (j + 1) ≡ k0.1 * Nat.fib (j + 1)
            [MOD (M / Nat.gcd M (Nat.fib (j + 1))) * Nat.fib (j + 1)] := by
        simpa [Nat.mul_comm] using Nat.ModEq.mul_right' (Nat.fib (j + 1)) h'
      exact hmulg.of_dvd <| by
        refine ⟨Nat.fib (j + 1) / Nat.gcd M (Nat.fib (j + 1)), ?_⟩
        calc
          (M / Nat.gcd M (Nat.fib (j + 1))) * Nat.fib (j + 1)
              = (M / Nat.gcd M (Nat.fib (j + 1))) *
                  ((Nat.fib (j + 1) / Nat.gcd M (Nat.fib (j + 1))) *
                    Nat.gcd M (Nat.fib (j + 1))) := by
                      have hf :
                          Nat.fib (j + 1) =
                            (Nat.fib (j + 1) / Nat.gcd M (Nat.fib (j + 1))) *
                              Nat.gcd M (Nat.fib (j + 1)) :=
                        (Nat.div_mul_cancel (Nat.gcd_dvd_right M (Nat.fib (j + 1)))).symm
                      exact congrArg (fun x => (M / Nat.gcd M (Nat.fib (j + 1))) * x) hf
          _ = ((M / Nat.gcd M (Nat.fib (j + 1))) *
                Nat.gcd M (Nat.fib (j + 1))) *
                  (Nat.fib (j + 1) / Nat.gcd M (Nat.fib (j + 1))) := by ac_rfl
          _ = M * (Nat.fib (j + 1) / Nat.gcd M (Nat.fib (j + 1))) := by
                have hM :
                    (M / Nat.gcd M (Nat.fib (j + 1))) *
                      Nat.gcd M (Nat.fib (j + 1)) = M :=
                  Nat.div_mul_cancel (Nat.gcd_dvd_left M (Nat.fib (j + 1)))
                exact congrArg (fun x => x * (Nat.fib (j + 1) / Nat.gcd M (Nat.fib (j + 1)))) hM
    exact hk.mp hmod

private lemma foldFiberSingletonZeroCoset_card (M j : ℕ) (k0 : Fin M) :
    (foldFiberSingletonZeroCoset M j k0).card = Nat.gcd (Nat.fib (j + 1)) M := by
  let g := Nat.gcd (Nat.fib (j + 1)) M
  let q := M / g
  have hMpos : 0 < M :=
    lt_of_lt_of_le (Nat.zero_lt_succ _) (Nat.succ_le_of_lt k0.2)
  have hg_dvd : g ∣ M := Nat.gcd_dvd_right _ _
  have hq_dvd : q ∣ M := by
    dsimp [q]
    exact Nat.div_dvd_of_dvd hg_dvd
  have hMq : M = q * g := by
    dsimp [q]
    exact Nat.eq_mul_of_div_eq_left hg_dvd rfl
  have hqpos : 0 < q := by
    exact Nat.pos_of_ne_zero fun hq0 =>
      hMpos.ne' <| by simpa [hMq, hq0]
  have hEq :
      foldFiberSingletonZeroCoset M j k0 =
        Finset.univ.filter (fun k : Fin M => k.1 ≡ k0.1 [MOD q]) := by
    ext k
    simpa [q, g, Nat.gcd_comm] using foldFiberSingletonZeroCoset_mem_iff M j k0 k
  calc
    (foldFiberSingletonZeroCoset M j k0).card =
        (Finset.univ.filter (fun k : Fin M => k.1 ≡ k0.1 [MOD q])).card := by rw [hEq]
    _ = M / q := card_univ_filter_fin_modEq M q k0.1 hq_dvd
    _ = g := by
      rw [hMq]
      simpa [Nat.mul_comm] using (Nat.mul_div_left g hqpos)

private lemma foldFiberSingletonZeroSet_nonempty_iff_gcd_dvd_half (M j : ℕ) (hMpos : 0 < M) :
    (foldFiberSingletonZeroSet M j).Nonempty ↔ Nat.gcd (Nat.fib (j + 1)) M ∣ M / 2 := by
  let w := Nat.fib (j + 1)
  let g := Nat.gcd w M
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right _ hMpos
  constructor
  · intro hne
    rcases hne with ⟨k, hk⟩
    have hmod : k.1 * w ≡ M / 2 [MOD M] := by
      have hhalf_lt : M / 2 < M := Nat.div_lt_self hMpos (by decide)
      simpa [foldFiberSingletonZeroSet, foldFiberHalfResidue, Nat.ModEq,
        Nat.mod_eq_of_lt hhalf_lt] using hk
    have hmodg : k.1 * w ≡ M / 2 [MOD g] := by
      exact hmod.of_dvd (Nat.gcd_dvd_right _ _)
    have hw0 : k.1 * w ≡ 0 [MOD g] := by
      exact Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right (Nat.gcd_dvd_left _ _) _)
    have hhalf0 : M / 2 ≡ 0 [MOD g] := hmodg.symm.trans hw0
    exact Nat.modEq_zero_iff_dvd.mp hhalf0
  · intro hgHalf
    by_cases hq1 : M / g = 1
    · have hM_eq_g : M = g := by
        exact (Nat.eq_mul_of_div_eq_left (Nat.gcd_dvd_right w M) hq1).trans (by simpa [g])
      have hM_one : M = 1 := by
        by_contra hMne
        have hMgt1 : 1 < M := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hMpos)
          (show 1 ≠ M from fun h => hMne h.symm)
        have hhalf_pos : 0 < M / 2 := Nat.div_pos hMgt1 (by decide)
        have hdvd : M ∣ M / 2 := by
          have hdvd' : g ∣ M / 2 := hgHalf
          rw [hM_eq_g.symm] at hdvd'
          exact hdvd'
        have hle : M ≤ M / 2 := Nat.le_of_dvd hhalf_pos hdvd
        have hlt : M / 2 < M := Nat.div_lt_self hMpos (by decide)
        omega
      refine ⟨⟨0, by omega⟩, ?_⟩
      simp [foldFiberSingletonZeroSet, foldFiberHalfResidue, hM_one]
    · let q := M / g
      let u := w / g
      have hq_gt1 : 1 < q := by
        have hqpos : 0 < q := by
          have hMq : M = q * g := by
            dsimp [q]
            exact Nat.eq_mul_of_div_eq_left (Nat.gcd_dvd_right w M) rfl
          exact Nat.pos_of_ne_zero fun hq0 => hMpos.ne' <| by simpa [hMq, hq0]
        have hqne : q ≠ 1 := by simpa [q] using hq1
        exact Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hqpos) hqne.symm
      have hcop : u.Coprime q := by
        dsimp [u, q, g]
        simpa [Nat.gcd_comm] using Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right w hMpos)
      obtain ⟨inv, hinv_lt, hinv⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hq_gt1
      rcases hgHalf with ⟨r, hr⟩
      let kNat := ((M / 2) / g * inv) % q
      have hkNat_lt_q : kNat < q := Nat.mod_lt _ (Nat.lt_trans Nat.zero_lt_one hq_gt1)
      have hq_le_M : q ≤ M := by
        dsimp [q, g]
        exact Nat.div_le_self _ _
      have hkNat_lt_M : kNat < M := lt_of_lt_of_le hkNat_lt_q hq_le_M
      have hqmod :
          ((M / 2) / g * inv) ≡ kNat [MOD q] := by
        dsimp [kNat]
        exact (Nat.mod_modEq _ _).symm
      have hinvMod : u * inv ≡ 1 [MOD q] := by
        have h1_lt : 1 < q := hq_gt1
        simpa [Nat.ModEq, Nat.mod_eq_of_lt h1_lt] using hinv
      have hsol_q : kNat * u ≡ (M / 2) / g [MOD q] := by
        have hmul : ((M / 2) / g) * (u * inv) ≡ ((M / 2) / g) * 1 [MOD q] := by
          exact Nat.ModEq.mul_left ((M / 2) / g) hinvMod
        have hmul' : ((M / 2) / g * inv) * u ≡ ((M / 2) / g) [MOD q] := by
          simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul
        exact (Nat.ModEq.mul_right u hqmod).symm.trans hmul'
      have hsol_M : kNat * w ≡ M / 2 [MOD M] := by
        have hmulg :
            g * (kNat * u) ≡ g * ((M / 2) / g) [MOD g * q] := Nat.ModEq.mul_left' g hsol_q
        have hrhs : g * ((M / 2) / g) = M / 2 := by
          simpa [Nat.mul_comm] using
            (Nat.eq_mul_of_div_eq_left (show g ∣ M / 2 from ⟨r, hr⟩) rfl).symm
        have hw : w = g * u := Nat.eq_mul_of_div_eq_right (Nat.gcd_dvd_left w M) rfl
        have hMq : g * q = M := by
          dsimp [q]
          rw [Nat.mul_comm, Nat.div_mul_cancel (Nat.gcd_dvd_right w M)]
        have hmulg' : kNat * (g * u) ≡ M / 2 [MOD g * q] := by
          simpa [hrhs, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmulg
        have hsol' : kNat * w ≡ M / 2 [MOD g * q] := by simpa [hw] using hmulg'
        simpa [hMq] using hsol'
      have hhalf_lt : M / 2 < M := Nat.div_lt_self hMpos (by decide)
      refine ⟨⟨kNat, hkNat_lt_M⟩, ?_⟩
      have hkEq : kNat * w % M = M / 2 := Nat.mod_eq_of_modEq hsol_M hhalf_lt
      simpa [foldFiberSingletonZeroSet, foldFiberHalfResidue, Nat.ModEq] using hkEq

/-- Paper label: `thm:killo-fold-zero-spectrum-affine-congruence`. -/
theorem paper_killo_fold_zero_spectrum_affine_congruence (m j : ℕ) :
    let M := Nat.fib (m + 2)
    let g := Nat.fib (Nat.gcd (j + 1) (m + 2))
    ((foldFiberSingletonZeroSet M j).Nonempty ↔ g ∣ M / 2) ∧
      (∀ k0 : Fin M, k0 ∈ foldFiberSingletonZeroSet M j →
        (foldFiberSingletonZeroSet M j).card = g) := by
  dsimp
  have hgcd : Nat.gcd (Nat.fib (j + 1)) (Nat.fib (m + 2)) = Nat.fib (Nat.gcd (j + 1) (m + 2)) := by
    simpa using (Omega.fib_gcd (j + 1) (m + 2))
  have hMpos : 0 < Nat.fib (m + 2) := Nat.fib_pos.mpr (by omega)
  refine ⟨?_, ?_⟩
  · simpa [hgcd] using
      foldFiberSingletonZeroSet_nonempty_iff_gcd_dvd_half (Nat.fib (m + 2)) j hMpos
  · intro k0 hk0
    have hEq := foldFiberSingletonZeroSet_eq_coset (Nat.fib (m + 2)) j k0 hk0
    calc
      (foldFiberSingletonZeroSet (Nat.fib (m + 2)) j).card
          = (foldFiberSingletonZeroCoset (Nat.fib (m + 2)) j k0).card := by simp [hEq]
      _ = Nat.gcd (Nat.fib (j + 1)) (Nat.fib (m + 2)) := foldFiberSingletonZeroCoset_card _ _ _
      _ = Nat.fib (Nat.gcd (j + 1) (m + 2)) := hgcd

end Omega.Folding
