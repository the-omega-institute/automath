import Mathlib.Tactic

namespace Omega.Conclusion

private lemma add_pow_lt_of_pos {a b q : Nat} (ha : 0 < a) (hb : 0 < b) (hq : 2 ≤ q) :
    a ^ q + b ^ q < (a + b) ^ q := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hq
  induction n with
  | zero =>
      have hab : 0 < a * b + b * a := by
        exact lt_of_lt_of_le (Nat.mul_pos ha hb) (Nat.le_add_right (a * b) (b * a))
      calc
        a ^ 2 + b ^ 2 < a ^ 2 + b ^ 2 + (a * b + b * a) := Nat.lt_add_of_pos_right hab
        _ = (a + b) ^ 2 := by ring
  | succ n ih =>
      have hsum_pos : 0 < a + b := lt_of_lt_of_le ha (Nat.le_add_right a b)
      have ih' : a ^ (n + 2) + b ^ (n + 2) < (a + b) ^ (n + 2) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (by omega)
      have hleft : a ^ (n + 2) * a < a ^ (n + 2) * (a + b) := by
        exact Nat.mul_lt_mul_of_pos_left (Nat.lt_add_of_pos_right hb) (pow_pos ha _)
      have hright : b ^ (n + 2) * b < b ^ (n + 2) * (a + b) := by
        exact Nat.mul_lt_mul_of_pos_left (Nat.lt_add_of_pos_left ha) (pow_pos hb _)
      have hmiddle :
          a ^ (n + 2) * (a + b) + b ^ (n + 2) * (a + b) < (a + b) ^ (n + 2) * (a + b) := by
        simpa [Nat.add_mul, add_comm, add_left_comm, add_assoc] using
          (Nat.mul_lt_mul_of_pos_right ih' hsum_pos)
      calc
        a ^ (2 + (n + 1)) + b ^ (2 + (n + 1)) = a ^ (n + 2) * a + b ^ (n + 2) * b := by
          simp [pow_succ, Nat.add_assoc, Nat.add_comm, Nat.mul_comm]
        _ < a ^ (n + 2) * (a + b) + b ^ (n + 2) * (a + b) := add_lt_add hleft hright
        _ < (a + b) ^ (n + 2) * (a + b) := hmiddle
        _ = (a + b) ^ (2 + (n + 1)) := by
          simp [pow_succ, Nat.add_assoc, Nat.add_comm, Nat.mul_comm]

private lemma add_pow_le {a b q : Nat} (hq : 2 ≤ q) : a ^ q + b ^ q ≤ (a + b) ^ q := by
  have hq0 : q ≠ 0 := by omega
  by_cases ha : a = 0
  · simp [ha, hq0]
  by_cases hb : b = 0
  · simp [hb, hq0]
  exact Nat.le_of_lt (add_pow_lt_of_pos (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb) hq)

private lemma sum_pow_le_pow_sum_finset {ι : Type*} {q : Nat}
    (s : Finset ι) (a : ι → Nat) (hq : 2 ≤ q) :
    s.sum (fun i => a i ^ q) ≤ (s.sum fun i => a i) ^ q := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      calc
        (insert i s).sum (fun j => a j ^ q) = a i ^ q + s.sum (fun j => a j ^ q) := by simp [hi]
        _ ≤ a i ^ q + (s.sum fun j => a j) ^ q := Nat.add_le_add_left ih _
        _ ≤ (a i + s.sum (fun j => a j)) ^ q := add_pow_le hq
        _ = ((insert i s).sum fun j => a j) ^ q := by simp [hi]

private def coarseningFiberEquiv
    {Omega X Y : Type*} [DecidableEq X]
    (f : Omega → X) (g : X → Y) (y : Y) :
    {w : Omega // g (f w) = y} ≃ Σ x : {x : X // g x = y}, {w : Omega // f w = x.1} where
  toFun w := ⟨⟨f w.1, w.2⟩, ⟨w.1, rfl⟩⟩
  invFun z := ⟨z.2.1, by simpa [z.2.2] using z.1.2⟩
  left_inv w := by
    cases w
    rfl
  right_inv z := by
    rcases z with ⟨⟨x, hx⟩, ⟨w, hw⟩⟩
    cases hw
    rfl

/-- Paper-facing rigidity criterion for a single Rényi moment under coarsening.
    thm:conclusion-single-renyi-rigidity-for-coarsening -/
theorem paper_conclusion_single_renyi_rigidity_for_coarsening
    {Omega X Y : Type*} [Fintype Omega] [Fintype X] [Fintype Y]
    [DecidableEq Omega] [DecidableEq X] [DecidableEq Y]
    (f : Omega → X) (g : X → Y) (q : Nat) (hq : 2 ≤ q)
    (hSq : (∑ y : Y, (Fintype.card {w : Omega // g (f w) = y}) ^ q) =
      ∑ x : X, (Fintype.card {w : Omega // f w = x}) ^ q) :
    (∀ {x1 x2 : X}, 0 < Fintype.card {w : Omega // f w = x1} →
        0 < Fintype.card {w : Omega // f w = x2} → g x1 = g x2 → x1 = x2) ∧
      (∀ T : Nat, (∑ y : Y, Nat.min (Fintype.card {w : Omega // g (f w) = y}) T) =
        ∑ x : X, Nat.min (Fintype.card {w : Omega // f w = x}) T) := by
  let A : X → Nat := fun x => Fintype.card {w : Omega // f w = x}
  let B : Y → Nat := fun y => Fintype.card {w : Omega // g (f w) = y}
  have hB :
      ∀ y : Y, B y = ∑ x : {x : X // g x = y}, A x := by
    intro y
    calc
      B y = Fintype.card (Σ x : {x : X // g x = y}, {w : Omega // f w = x.1}) := by
        unfold B
        exact Fintype.card_congr (coarseningFiberEquiv f g y)
      _ = ∑ x : {x : X // g x = y}, A x := by
        simp [A, Fintype.card_sigma]
  have hregroup :
      (∑ y : Y, ∑ x : {x : X // g x = y}, A x ^ q) = ∑ x : X, A x ^ q := by
    simpa [A] using (Fintype.sum_fiberwise (g := g) (f := fun x : X => A x ^ q))
  have hlocal_le :
      ∀ y : Y, (∑ x : {x : X // g x = y}, A x ^ q) ≤ B y ^ q := by
    intro y
    rw [hB y]
    simpa using
      (sum_pow_le_pow_sum_finset (s := (Finset.univ : Finset {x : X // g x = y}))
        (a := fun x : {x : X // g x = y} => A x) hq)
  have hInjective :
      ∀ {x1 x2 : X}, 0 < A x1 → 0 < A x2 → g x1 = g x2 → x1 = x2 := by
    intro x1 x2 hx1 hx2 hgx
    by_contra hne
    let y0 : Y := g x1
    let z1 : {x : X // g x = y0} := ⟨x1, rfl⟩
    let z2 : {x : X // g x = y0} := ⟨x2, hgx.symm⟩
    let s : Finset {x : X // g x = y0} := Finset.univ.erase z1
    let rest : Nat := s.sum fun z => A z
    let restPow : Nat := s.sum fun z => A z ^ q
    have hz2_mem : z2 ∈ s := by
      simp [s, z1, z2, hne, eq_comm]
    have hrest_ge : A x2 ≤ rest := by
      dsimp [rest, s]
      simpa [z2] using
        (Finset.single_le_sum (f := fun z : {x : X // g x = y0} => A z)
          (fun _ _ => Nat.zero_le _) hz2_mem)
    have hrest_pos : 0 < rest := lt_of_lt_of_le hx2 hrest_ge
    have hsplit_card :
        (∑ z : {x : X // g x = y0}, A z) = A x1 + rest := by
      dsimp [rest, s, z1]
      simpa [add_comm, add_left_comm, add_assoc] using
        ((Finset.sum_erase_add (s := (Finset.univ : Finset {x : X // g x = y0}))
          (f := fun z : {x : X // g x = y0} => A z) (by simp : z1 ∈ Finset.univ))).symm
    have hsplit_pow :
        (∑ z : {x : X // g x = y0}, A z ^ q) = A x1 ^ q + restPow := by
      dsimp [restPow, s, z1]
      simpa [add_comm, add_left_comm, add_assoc] using
        ((Finset.sum_erase_add (s := (Finset.univ : Finset {x : X // g x = y0}))
          (f := fun z : {x : X // g x = y0} => A z ^ q) (by simp : z1 ∈ Finset.univ))).symm
    have hrestPow_le : restPow ≤ rest ^ q := by
      dsimp [restPow, rest]
      exact sum_pow_le_pow_sum_finset s (fun z : {x : X // g x = y0} => A z) hq
    have hstrict_local :
        (∑ z : {x : X // g x = y0}, A z ^ q) < B y0 ^ q := by
      calc
        (∑ z : {x : X // g x = y0}, A z ^ q) = A x1 ^ q + restPow := hsplit_pow
        _ ≤ A x1 ^ q + rest ^ q := Nat.add_le_add_left hrestPow_le _
        _ < (A x1 + rest) ^ q := add_pow_lt_of_pos hx1 hrest_pos hq
        _ = B y0 ^ q := by rw [← hsplit_card, ← hB y0]
    have hsum_lt :
        (∑ y : Y, ∑ x : {x : X // g x = y}, A x ^ q) < ∑ y : Y, B y ^ q := by
      classical
      simpa using
        (Finset.sum_lt_sum (s := (Finset.univ : Finset Y))
          (f := fun y : Y => ∑ x : {x : X // g x = y}, A x ^ q)
          (g := fun y : Y => B y ^ q)
          (by intro y hy; exact hlocal_le y)
          ⟨y0, by simp [y0], hstrict_local⟩)
    have : (∑ x : X, A x ^ q) < ∑ x : X, A x ^ q := by
      calc
        (∑ x : X, A x ^ q) = (∑ y : Y, ∑ x : {x : X // g x = y}, A x ^ q) := hregroup.symm
        _ < ∑ y : Y, B y ^ q := hsum_lt
        _ = ∑ x : X, A x ^ q := by
          simpa [A, B] using hSq
    exact absurd this (lt_irrefl _)
  refine ⟨?_, ?_⟩
  · intro x1 x2 hx1 hx2 hgx
    simpa [A] using hInjective hx1 hx2 hgx
  · intro T
    have hmin_local :
        ∀ y : Y, Nat.min (B y) T = ∑ x : {x : X // g x = y}, Nat.min (A x) T := by
      intro y
      by_cases hpos : ∃ x : {x : X // g x = y}, 0 < A x
      · rcases hpos with ⟨x0, hx0⟩
        let s : Finset {x : X // g x = y} := Finset.univ.erase x0
        have hzero_rest : ∀ z ∈ s, A z = 0 := by
          intro z hz
          by_cases hzpos : 0 < A z
          · have hz_eq : z = x0 := by
              apply Subtype.ext
              exact hInjective (x1 := z) (x2 := x0) hzpos hx0 (by simpa using z.2.trans x0.2.symm)
            have : z ∉ s := by simp [s, hz_eq]
            exact False.elim (this hz)
          · exact Nat.eq_zero_of_not_pos hzpos
        have hsum_rest_zero : s.sum (fun z => A z) = 0 := by
          refine Finset.sum_eq_zero ?_
          intro z hz
          exact hzero_rest z hz
        have hsum_rest_min_zero : s.sum (fun z => Nat.min (A z) T) = 0 := by
          refine Finset.sum_eq_zero ?_
          intro z hz
          simp [hzero_rest z hz]
        have hsplit_card :
            (∑ z : {x : X // g x = y}, A z) = A x0 := by
          dsimp [s]
          calc
            (∑ z : {x : X // g x = y}, A z) =
                ((Finset.univ : Finset {x : X // g x = y}).erase x0).sum (fun z => A z) + A x0 := by
              simpa using
                ((Finset.sum_erase_add (s := (Finset.univ : Finset {x : X // g x = y}))
                  (f := fun z : {x : X // g x = y} => A z) (by simp : x0 ∈ Finset.univ)).symm)
            _ = A x0 := by rw [hsum_rest_zero, zero_add]
        have hsplit_min :
            (∑ z : {x : X // g x = y}, Nat.min (A z) T) = Nat.min (A x0) T := by
          dsimp [s]
          calc
            (∑ z : {x : X // g x = y}, Nat.min (A z) T) =
                ((Finset.univ : Finset {x : X // g x = y}).erase x0).sum
                    (fun z => Nat.min (A z) T) + Nat.min (A x0) T := by
              simpa using
                ((Finset.sum_erase_add (s := (Finset.univ : Finset {x : X // g x = y}))
                  (f := fun z : {x : X // g x = y} => Nat.min (A z) T)
                  (by simp : x0 ∈ Finset.univ)).symm)
            _ = Nat.min (A x0) T := by rw [hsum_rest_min_zero, zero_add]
        rw [hsplit_min, ← hsplit_card, ← hB y]
      · have hzero_all : ∀ x : {x : X // g x = y}, A x = 0 := by
          intro x
          by_cases hx : 0 < A x
          · exact False.elim (hpos ⟨x, hx⟩)
          · exact Nat.eq_zero_of_not_pos hx
        have hsum_zero : (∑ x : {x : X // g x = y}, A x) = 0 := by
          classical
          refine Finset.sum_eq_zero ?_
          intro x hx
          exact hzero_all x
        have hsum_min_zero : (∑ x : {x : X // g x = y}, Nat.min (A x) T) = 0 := by
          classical
          refine Finset.sum_eq_zero ?_
          intro x hx
          simp [hzero_all x]
        have hBy_zero : B y = 0 := by rw [hB y, hsum_zero]
        rw [hBy_zero, hsum_min_zero]
        simp
    calc
      (∑ y : Y, Nat.min (B y) T) = ∑ y : Y, ∑ x : {x : X // g x = y}, Nat.min (A x) T := by
        classical
        simpa using
          (Finset.sum_congr rfl (fun y _ => hmin_local y) :
            (Finset.univ : Finset Y).sum (fun y => Nat.min (B y) T) =
              (Finset.univ : Finset Y).sum
                (fun y => ∑ x : {x : X // g x = y}, Nat.min (A x) T))
      _ = ∑ x : X, Nat.min (A x) T := by
        simpa [A] using (Fintype.sum_fiberwise (g := g) (f := fun x : X => Nat.min (A x) T))

private lemma conclusion_strict_coarsening_exact_bit_budget_loss_min_add_le_add_min
    (a b T : Nat) :
    Nat.min (a + b) T ≤ Nat.min a T + Nat.min b T := by
  by_cases ha : a ≤ T
  ·
    by_cases hb : b ≤ T
    · have hright : Nat.min a T + Nat.min b T = a + b := by
        simp [Nat.min_eq_left ha, Nat.min_eq_left hb]
      calc
        Nat.min (a + b) T ≤ a + b := Nat.min_le_left _ _
        _ = Nat.min a T + Nat.min b T := hright.symm
    · have hTb : T ≤ b := by omega
      have hright : Nat.min a T + Nat.min b T = a + T := by
        simp [Nat.min_eq_left ha, Nat.min_eq_right hTb]
      have hleft : Nat.min (a + b) T ≤ T := Nat.min_le_right _ _
      calc
        Nat.min (a + b) T ≤ T := hleft
        _ ≤ a + T := by omega
        _ = Nat.min a T + Nat.min b T := hright.symm
  · have hTa : T ≤ a := by omega
    have hright : Nat.min a T + Nat.min b T = T + Nat.min b T := by
      simp [Nat.min_eq_right hTa]
    have hleft : Nat.min (a + b) T ≤ T := Nat.min_le_right _ _
    calc
      Nat.min (a + b) T ≤ T := hleft
      _ ≤ T + Nat.min b T := Nat.le_add_right _ _
      _ = Nat.min a T + Nat.min b T := hright.symm

private lemma conclusion_strict_coarsening_exact_bit_budget_loss_min_sum_le_sum_min
    {ι : Type*} (s : Finset ι) (a : ι → Nat) (T : Nat) :
    Nat.min (s.sum a) T ≤ s.sum fun i => Nat.min (a i) T := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      calc
        Nat.min ((insert i s).sum a) T =
            Nat.min (a i + s.sum a) T := by simp [hi]
        _ ≤ Nat.min (a i) T + Nat.min (s.sum a) T :=
          conclusion_strict_coarsening_exact_bit_budget_loss_min_add_le_add_min (a i) (s.sum a) T
        _ ≤ Nat.min (a i) T + s.sum (fun j => Nat.min (a j) T) :=
          Nat.add_le_add_left ih _
        _ = (insert i s).sum (fun j => Nat.min (a j) T) := by simp [hi]

private lemma conclusion_strict_coarsening_exact_bit_budget_loss_two_min_gt
    {a b T : Nat} (ha : 0 < a) (hb : 0 < b) (hTpos : 0 < T) (hT : T < a + b) :
    T < Nat.min a T + Nat.min b T := by
  by_cases haT : a ≤ T
  ·
    by_cases hbT : b ≤ T
    · have hright : Nat.min a T + Nat.min b T = a + b := by
        simp [Nat.min_eq_left haT, Nat.min_eq_left hbT]
      simpa [hright] using hT
    · have hTb : T ≤ b := by omega
      have hright : Nat.min a T + Nat.min b T = a + T := by
        simp [Nat.min_eq_left haT, Nat.min_eq_right hTb]
      calc
        T < a + T := by omega
        _ = Nat.min a T + Nat.min b T := hright.symm
  · have hTa : T ≤ a := by omega
    have hmina : Nat.min a T = T := Nat.min_eq_right hTa
    by_cases hbT : b ≤ T
    · have hright : Nat.min a T + Nat.min b T = T + b := by
        simp [hmina, Nat.min_eq_left hbT]
      calc
        T < T + b := by omega
        _ = Nat.min a T + Nat.min b T := hright.symm
    · have hTb : T ≤ b := by omega
      have hright : Nat.min a T + Nat.min b T = T + T := by
        simp [hmina, Nat.min_eq_right hTb]
      calc
        T < T + T := by omega
        _ = Nat.min a T + Nat.min b T := hright.symm

/-- Paper label: `cor:conclusion-strict-coarsening-exact-bit-budget-loss`. A strict
coarsening that merges two nonempty fibers whose combined size exceeds the dyadic cap strictly
reduces the capped capacity sum at that cap. -/
theorem paper_conclusion_strict_coarsening_exact_bit_budget_loss
    {Omega X Y : Type*} [Fintype Omega] [Fintype X] [Fintype Y] [DecidableEq X]
    [DecidableEq Y] (f : Omega → X) (g : X → Y) (B : ℕ) {x1 x2 : X} (hne : x1 ≠ x2)
    (hg : g x1 = g x2) (h1 : 0 < Fintype.card {w : Omega // f w = x1})
    (h2 : 0 < Fintype.card {w : Omega // f w = x2})
    (hT : 2 ^ B <
      Fintype.card {w : Omega // f w = x1} + Fintype.card {w : Omega // f w = x2}) :
    (∑ y : Y, Nat.min (Fintype.card {w : Omega // g (f w) = y}) (2 ^ B)) <
      ∑ x : X, Nat.min (Fintype.card {w : Omega // f w = x}) (2 ^ B) := by
  classical
  let A : X → Nat := fun x => Fintype.card {w : Omega // f w = x}
  let C : Y → Nat := fun y => Fintype.card {w : Omega // g (f w) = y}
  let T : Nat := 2 ^ B
  have hC :
      ∀ y : Y, C y = ∑ x : {x : X // g x = y}, A x := by
    intro y
    calc
      C y = Fintype.card (Σ x : {x : X // g x = y}, {w : Omega // f w = x.1}) := by
        unfold C
        exact Fintype.card_congr (coarseningFiberEquiv f g y)
      _ = ∑ x : {x : X // g x = y}, A x := by
        simp [A, Fintype.card_sigma]
  have hlocal_le :
      ∀ y : Y, Nat.min (C y) T ≤ ∑ x : {x : X // g x = y}, Nat.min (A x) T := by
    intro y
    rw [hC y]
    exact conclusion_strict_coarsening_exact_bit_budget_loss_min_sum_le_sum_min
      (Finset.univ : Finset {x : X // g x = y}) (fun x => A x) T
  let y0 : Y := g x1
  let z1 : {x : X // g x = y0} := ⟨x1, rfl⟩
  let z2 : {x : X // g x = y0} := ⟨x2, hg.symm⟩
  have hz_ne : z2 ≠ z1 := by
    intro hz
    exact hne (Subtype.ext_iff.mp hz).symm
  have htwo_min_gt : T < Nat.min (A z1) T + Nat.min (A z2) T := by
    exact conclusion_strict_coarsening_exact_bit_budget_loss_two_min_gt
      (by simpa [A, z1] using h1) (by simpa [A, z2] using h2)
      (by simp [T]) (by simpa [A, T] using hT)
  have htwo_le_sum :
      Nat.min (A z1) T + Nat.min (A z2) T ≤
        ∑ x : {x : X // g x = y0}, Nat.min (A x) T := by
    let s : Finset {x : X // g x = y0} := Finset.univ.erase z1
    have hz2_mem : z2 ∈ s := by
      simp [s, hz_ne]
    have hsecond :
        Nat.min (A z2) T ≤ s.sum (fun x => Nat.min (A x) T) :=
      Finset.single_le_sum (f := fun x : {x : X // g x = y0} => Nat.min (A x) T)
        (fun _ _ => Nat.zero_le _) hz2_mem
    calc
      Nat.min (A z1) T + Nat.min (A z2) T ≤
          Nat.min (A z1) T + s.sum (fun x => Nat.min (A x) T) :=
        Nat.add_le_add_left hsecond _
      _ = ∑ x : {x : X // g x = y0}, Nat.min (A x) T := by
        dsimp [s]
        simpa [add_comm, add_left_comm, add_assoc] using
          (Finset.sum_erase_add (s := (Finset.univ : Finset {x : X // g x = y0}))
            (f := fun x : {x : X // g x = y0} => Nat.min (A x) T)
            (by simp : z1 ∈ Finset.univ))
  have hpair_le_C : A z1 + A z2 ≤ C y0 := by
    let s : Finset {x : X // g x = y0} := Finset.univ.erase z1
    have hz2_mem : z2 ∈ s := by
      simp [s, hz_ne]
    have hsecond : A z2 ≤ s.sum (fun x => A x) :=
      Finset.single_le_sum (f := fun x : {x : X // g x = y0} => A x)
        (fun _ _ => Nat.zero_le _) hz2_mem
    calc
      A z1 + A z2 ≤ A z1 + s.sum (fun x => A x) := Nat.add_le_add_left hsecond _
      _ = ∑ x : {x : X // g x = y0}, A x := by
        dsimp [s]
        simpa [add_comm, add_left_comm, add_assoc] using
          (Finset.sum_erase_add (s := (Finset.univ : Finset {x : X // g x = y0}))
            (f := fun x : {x : X // g x = y0} => A x)
            (by simp : z1 ∈ Finset.univ))
      _ = C y0 := (hC y0).symm
  have hCy0_cap : T ≤ C y0 := by
    exact le_trans (Nat.le_of_lt (by simpa [A, T, z1, z2] using hT)) hpair_le_C
  have hstrict_local :
      Nat.min (C y0) T < ∑ x : {x : X // g x = y0}, Nat.min (A x) T := by
    calc
      Nat.min (C y0) T = T := Nat.min_eq_right hCy0_cap
      _ < Nat.min (A z1) T + Nat.min (A z2) T := htwo_min_gt
      _ ≤ ∑ x : {x : X // g x = y0}, Nat.min (A x) T := htwo_le_sum
  have hsum_lt :
      (∑ y : Y, Nat.min (C y) T) <
        ∑ y : Y, ∑ x : {x : X // g x = y}, Nat.min (A x) T := by
    simpa using
      (Finset.sum_lt_sum (s := (Finset.univ : Finset Y))
        (f := fun y : Y => Nat.min (C y) T)
        (g := fun y : Y => ∑ x : {x : X // g x = y}, Nat.min (A x) T)
        (by intro y _; exact hlocal_le y)
        ⟨y0, by simp [y0], hstrict_local⟩)
  calc
    (∑ y : Y, Nat.min (Fintype.card {w : Omega // g (f w) = y}) (2 ^ B)) =
        ∑ y : Y, Nat.min (C y) T := by
      simp [C, T]
    _ < ∑ y : Y, ∑ x : {x : X // g x = y}, Nat.min (A x) T := hsum_lt
    _ = ∑ x : X, Nat.min (A x) T := by
      simpa [A] using (Fintype.sum_fiberwise (g := g) (f := fun x : X => Nat.min (A x) T))
    _ = ∑ x : X, Nat.min (Fintype.card {w : Omega // f w = x}) (2 ^ B) := by
      simp [A, T]

end Omega.Conclusion
