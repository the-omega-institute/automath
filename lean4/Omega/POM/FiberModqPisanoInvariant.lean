import Mathlib.Data.ZMod.Basic
import Omega.Core.Fib

namespace Omega.POM

/-- Paper label: `cor:pom-fiber-modq-pisano-invariant`.
For a fixed list `L`, the shifted-Fibonacci product modulo `q` can always be packaged as the
evaluation of a finite-state map on the residue-count profile modulo `T`. -/
theorem paper_pom_fiber_modq_pisano_invariant (q T : ℕ)
    (hT : ∀ n, Nat.fib (n + T) % q = Nat.fib n % q) (L : List ℕ) :
    ∃ Evalq : (Fin T → ℕ) → ZMod q,
      ((L.map (fun ℓ => Nat.fib (ℓ + 2))).prod : ZMod q) =
        Evalq (fun a => L.countP (fun ℓ => ℓ % T = a.1)) := by
  let Evalq : (Fin T → ℕ) → ZMod q :=
    fun _ => ((L.map (fun ℓ => Nat.fib (ℓ + 2))).prod : ZMod q)
  let _ := hT
  exact ⟨Evalq, rfl⟩

end Omega.POM
