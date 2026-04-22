import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace Omega.POM

open FreeMonoid

def pomPrimeTraceHom {α : Type*} (code : α → ℕ) : FreeMonoid α →* FreeMonoid ℕ :=
  FreeMonoid.map code

noncomputable def pomTraceLedger : List ℕ → ℕ →₀ ℕ
  | [] => 0
  | n :: ns => Finsupp.single n 1 + pomTraceLedger ns

@[simp] theorem pomTraceLedger_nil : pomTraceLedger [] = 0 := rfl

@[simp] theorem pomTraceLedger_cons (n : ℕ) (ns : List ℕ) :
    pomTraceLedger (n :: ns) = Finsupp.single n 1 + pomTraceLedger ns := rfl

theorem pomTraceLedger_append (xs ys : List ℕ) :
    pomTraceLedger (xs ++ ys) = pomTraceLedger xs + pomTraceLedger ys := by
  induction xs with
  | nil =>
      simp [pomTraceLedger]
  | cons x xs ih =>
      simp [pomTraceLedger, ih, add_assoc]

noncomputable def pomPrimeTraceSupport {α : Type*} (code : α → ℕ) (w : FreeMonoid α) : ℕ →₀ ℕ :=
  pomTraceLedger (FreeMonoid.toList (pomPrimeTraceHom code w))

def pomValidPrimeTrace {α : Type*} (code : α → ℕ) (w : FreeMonoid ℕ) : Prop :=
  ∀ n ∈ FreeMonoid.toList w, n ∈ Set.range code

theorem pomPrimeTraceHom_valid {α : Type*} (code : α → ℕ) (w : FreeMonoid α) :
    pomValidPrimeTrace code (pomPrimeTraceHom code w) := by
  intro n hn
  have hn' : n ∈ (FreeMonoid.toList w).map code := by
    simpa [pomPrimeTraceHom, FreeMonoid.toList_map] using hn
  rcases List.mem_map.mp hn' with ⟨a, ha, rfl⟩
  exact ⟨a, rfl⟩

lemma pomEncodeDecodeList {α : Type*} [DecidableEq α] [Nonempty α] (code : α → ℕ) (xs : List ℕ)
    (hxs : ∀ n ∈ xs, n ∈ Set.range code) :
    (xs.map (Function.invFun code)).map code = xs := by
  induction xs with
  | nil =>
      rfl
  | cons n ns ih =>
      have hn : ∃ a, code a = n := hxs n (by simp)
      have hns : ∀ m ∈ ns, m ∈ Set.range code := by
        intro m hm
        exact hxs m (by simp [hm])
      simp [Function.invFun_eq hn, ih hns]

lemma pomDecodeEncodeList {α : Type*} [DecidableEq α] [Nonempty α] (code : α → ℕ)
    (hcode : Function.Injective code)
    (xs : List α) :
    (xs.map code).map (Function.invFun code) = xs := by
  induction xs with
  | nil =>
      rfl
  | cons a as ih =>
      simp [Function.leftInverse_invFun hcode a, ih]

def pomPrimeTraceShiftFreeMonoidStatement {α : Type*} [DecidableEq α] (code : α → ℕ) : Prop :=
  let T := pomPrimeTraceHom code
  (∀ x y, T (x * y) = T x * T y) ∧
    (∀ x y, pomPrimeTraceSupport code (x * y) = pomPrimeTraceSupport code x + pomPrimeTraceSupport code y) ∧
    Function.Injective T ∧
    Function.Surjective
      (fun x =>
        (⟨T x, pomPrimeTraceHom_valid code x⟩ :
          {w : FreeMonoid ℕ // pomValidPrimeTrace code w}))

theorem paper_pom_prime_trace_shift_free_monoid {α : Type*} [DecidableEq α] (code : α → ℕ)
    (hcode : Function.Injective code) : pomPrimeTraceShiftFreeMonoidStatement code := by
  dsimp [pomPrimeTraceShiftFreeMonoidStatement]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    exact (pomPrimeTraceHom code).map_mul x y
  · intro x y
    simp [pomPrimeTraceSupport, FreeMonoid.toList_mul, pomTraceLedger_append]
  · intro x y hxy
    apply FreeMonoid.toList.injective
    have hlist : FreeMonoid.toList (pomPrimeTraceHom code x) = FreeMonoid.toList (pomPrimeTraceHom code y) := by
      simpa [pomPrimeTraceHom] using congrArg FreeMonoid.toList hxy
    have hmap : (FreeMonoid.toList x).map code = (FreeMonoid.toList y).map code := by
      simpa [pomPrimeTraceHom, FreeMonoid.toList_map] using hlist
    exact (List.map_injective_iff.2 hcode) hmap
  · intro w
    by_cases hα : Nonempty α
    · letI := hα
      let decode : FreeMonoid α := FreeMonoid.ofList (FreeMonoid.toList w.1 |>.map (Function.invFun code))
      refine ⟨decode, ?_⟩
      have hdecode :
          List.map code ((FreeMonoid.toList w.1).map (Function.invFun code)) = FreeMonoid.toList w.1 :=
        pomEncodeDecodeList code (FreeMonoid.toList w.1) w.2
      apply Subtype.ext
      apply FreeMonoid.toList.injective
      simpa [decode, pomPrimeTraceHom, FreeMonoid.toList_map] using hdecode
    · letI : IsEmpty α := not_nonempty_iff.mp hα
      have hnil : FreeMonoid.toList w.1 = [] := by
        cases hw : FreeMonoid.toList w.1 with
        | nil =>
            exact rfl
        | cons n ns =>
            exfalso
            have hn : n ∈ Set.range code := w.2 n (by simp [hw])
            rcases hn with ⟨a, _⟩
            exact IsEmpty.false a
      have hw_one : w.1 = 1 := FreeMonoid.toList.injective hnil
      refine ⟨(1 : FreeMonoid α), ?_⟩
      apply Subtype.ext
      simpa [pomPrimeTraceHom] using hw_one.symm

end Omega.POM
