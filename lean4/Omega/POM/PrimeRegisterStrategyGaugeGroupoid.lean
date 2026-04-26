import Mathlib.Tactic
import Omega.POM.PrimeTraceIndexDuality

namespace Omega.POM

noncomputable section

/-- Two concrete strategy labels for the gauge-groupoid transport. -/
inductive pom_prime_register_strategy_gauge_groupoid_strategy where
  | left
  | right
deriving DecidableEq

/-- The stable folded coordinate shared by all lifted strategy images. -/
abbrev pom_prime_register_strategy_gauge_groupoid_folded_state :=
  pom_prime_trace_index_duality_folded_state

/-- After the prime-trace/index duality identifies every residual fiber with `Fin 1`, each actual
lifted image is the folded state together with the unique residual token. -/
abbrev pom_prime_register_strategy_gauge_groupoid_image
    (_s : pom_prime_register_strategy_gauge_groupoid_strategy) :=
  pom_prime_register_strategy_gauge_groupoid_folded_state × Unit

/-- Folding a source word records its prime trace together with the validity witness. -/
def pom_prime_register_strategy_gauge_groupoid_fold
    (x : FreeMonoid pom_prime_trace_index_duality_alphabet) :
    pom_prime_register_strategy_gauge_groupoid_folded_state :=
  ⟨pomPrimeTraceHom pom_prime_trace_index_duality_code x,
    pomPrimeTraceHom_valid pom_prime_trace_index_duality_code x⟩

/-- Lift a source word into the actual image of either strategy. -/
def pom_prime_register_strategy_gauge_groupoid_lift
    (s : pom_prime_register_strategy_gauge_groupoid_strategy)
    (x : FreeMonoid pom_prime_trace_index_duality_alphabet) :
    pom_prime_register_strategy_gauge_groupoid_image s :=
  (pom_prime_register_strategy_gauge_groupoid_fold x, ())

/-- Unlift a lifted image point by decoding the unique residual index `0`. -/
def pom_prime_register_strategy_gauge_groupoid_unlift
    (s : pom_prime_register_strategy_gauge_groupoid_strategy) :
    pom_prime_register_strategy_gauge_groupoid_image s →
      FreeMonoid pom_prime_trace_index_duality_alphabet
  | (y, ()) => pom_prime_trace_index_duality_inverse ⟨y, 0⟩

/-- The fiberwise residual transport is the unique permutation of the singleton residual fiber. -/
def pom_prime_register_strategy_gauge_groupoid_fiber_transport
    (_s _t : pom_prime_register_strategy_gauge_groupoid_strategy)
    (_y : pom_prime_register_strategy_gauge_groupoid_folded_state) :
    Unit → Unit :=
  id

/-- Transport between the two actual lifted images. -/
def pom_prime_register_strategy_gauge_groupoid_transport
    (s t : pom_prime_register_strategy_gauge_groupoid_strategy) :
    pom_prime_register_strategy_gauge_groupoid_image s →
      pom_prime_register_strategy_gauge_groupoid_image t :=
  fun z =>
    pom_prime_register_strategy_gauge_groupoid_lift t
      (pom_prime_register_strategy_gauge_groupoid_unlift s z)

lemma pom_prime_register_strategy_gauge_groupoid_unlift_lift
    (s : pom_prime_register_strategy_gauge_groupoid_strategy)
    (x : FreeMonoid pom_prime_trace_index_duality_alphabet) :
    pom_prime_register_strategy_gauge_groupoid_unlift s
        (pom_prime_register_strategy_gauge_groupoid_lift s x) = x := by
  let y := pom_prime_register_strategy_gauge_groupoid_fold x
  let hx : pom_prime_trace_index_duality_fiber y := ⟨x, rfl⟩
  have hrank : pom_prime_trace_index_duality_rank_map hx = 0 := rfl
  simpa [pom_prime_register_strategy_gauge_groupoid_unlift,
    pom_prime_register_strategy_gauge_groupoid_lift, y, hx, hrank] using
    (paper_pom_prime_trace_index_duality.2.2 y hx)

lemma pom_prime_register_strategy_gauge_groupoid_lift_unlift
    (s : pom_prime_register_strategy_gauge_groupoid_strategy)
    (z : pom_prime_register_strategy_gauge_groupoid_image s) :
    pom_prime_register_strategy_gauge_groupoid_lift s
        (pom_prime_register_strategy_gauge_groupoid_unlift s z) = z := by
  rcases z with ⟨y, u⟩
  cases u
  have hy :
      pom_prime_register_strategy_gauge_groupoid_fold
          (pom_prime_register_strategy_gauge_groupoid_unlift s (y, ())) = y := by
    apply Subtype.ext
    simpa [pom_prime_register_strategy_gauge_groupoid_fold,
      pom_prime_register_strategy_gauge_groupoid_unlift] using
      (paper_pom_prime_trace_index_duality.2.1 y 0)
  simpa [pom_prime_register_strategy_gauge_groupoid_lift, hy]

lemma pom_prime_register_strategy_gauge_groupoid_transport_eq
    (s t : pom_prime_register_strategy_gauge_groupoid_strategy)
    (z : pom_prime_register_strategy_gauge_groupoid_image s) :
    pom_prime_register_strategy_gauge_groupoid_transport s t z =
      (z.1, pom_prime_register_strategy_gauge_groupoid_fiber_transport s t z.1 z.2) := by
  rcases z with ⟨y, u⟩
  cases u
  have hy :
      pom_prime_register_strategy_gauge_groupoid_fold
          (pom_prime_register_strategy_gauge_groupoid_unlift s (y, ())) = y := by
    apply Subtype.ext
    simpa [pom_prime_register_strategy_gauge_groupoid_fold,
      pom_prime_register_strategy_gauge_groupoid_unlift] using
      (paper_pom_prime_trace_index_duality.2.1 y 0)
  simp [pom_prime_register_strategy_gauge_groupoid_transport,
    pom_prime_register_strategy_gauge_groupoid_lift,
    pom_prime_register_strategy_gauge_groupoid_fiber_transport, hy]

lemma pom_prime_register_strategy_gauge_groupoid_fiber_transport_bijective
    (s t : pom_prime_register_strategy_gauge_groupoid_strategy)
    (y : pom_prime_register_strategy_gauge_groupoid_folded_state) :
    Function.Bijective
      (pom_prime_register_strategy_gauge_groupoid_fiber_transport s t y) := by
  constructor
  · intro u v huv
    simpa [pom_prime_register_strategy_gauge_groupoid_fiber_transport] using huv
  · intro u
    exact ⟨u, by simp [pom_prime_register_strategy_gauge_groupoid_fiber_transport]⟩

lemma pom_prime_register_strategy_gauge_groupoid_transport_bijective
    (s t : pom_prime_register_strategy_gauge_groupoid_strategy) :
    Function.Bijective (pom_prime_register_strategy_gauge_groupoid_transport s t) := by
  constructor
  · intro a b hab
    have ha : pom_prime_register_strategy_gauge_groupoid_transport s t a = a := by
      simpa [pom_prime_register_strategy_gauge_groupoid_fiber_transport] using
        pom_prime_register_strategy_gauge_groupoid_transport_eq s t a
    have hb : pom_prime_register_strategy_gauge_groupoid_transport s t b = b := by
      simpa [pom_prime_register_strategy_gauge_groupoid_fiber_transport] using
        pom_prime_register_strategy_gauge_groupoid_transport_eq s t b
    calc
      a = pom_prime_register_strategy_gauge_groupoid_transport s t a := ha.symm
      _ = pom_prime_register_strategy_gauge_groupoid_transport s t b := hab
      _ = b := hb
  · intro z
    refine ⟨z, ?_⟩
    simpa [pom_prime_register_strategy_gauge_groupoid_fiber_transport] using
      pom_prime_register_strategy_gauge_groupoid_transport_eq s t z

/-- Proposition-level statement for the prime-register strategy gauge-groupoid. -/
def pom_prime_register_strategy_gauge_groupoid_statement : Prop :=
  (∀ s t,
    Function.Bijective (pom_prime_register_strategy_gauge_groupoid_transport s t)) ∧
    (∀ s t z,
      (pom_prime_register_strategy_gauge_groupoid_transport s t z).1 = z.1) ∧
    (∀ s t y,
      Function.Bijective (pom_prime_register_strategy_gauge_groupoid_fiber_transport s t y)) ∧
    (∀ s z,
      pom_prime_register_strategy_gauge_groupoid_transport s s z = z) ∧
    (∀ s t u z,
      pom_prime_register_strategy_gauge_groupoid_transport s u z =
        pom_prime_register_strategy_gauge_groupoid_transport t u
          (pom_prime_register_strategy_gauge_groupoid_transport s t z))

/-- Paper label: `prop:pom-prime-register-strategy-gauge-groupoid`. Transport between the actual
lifted images is defined by lift followed by unlift on the duality image, it is bijective, it
preserves the folded coordinate, the residual action is the unique singleton permutation on each
fiber, and the identity/composition laws hold on the nose. -/
theorem paper_pom_prime_register_strategy_gauge_groupoid :
    pom_prime_register_strategy_gauge_groupoid_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s t
    exact pom_prime_register_strategy_gauge_groupoid_transport_bijective s t
  · intro s t z
    simpa [pom_prime_register_strategy_gauge_groupoid_transport_eq]
  · intro s t y
    exact pom_prime_register_strategy_gauge_groupoid_fiber_transport_bijective s t y
  · intro s z
    simpa [pom_prime_register_strategy_gauge_groupoid_transport] using
      pom_prime_register_strategy_gauge_groupoid_lift_unlift s z
  · intro s t u z
    simp [pom_prime_register_strategy_gauge_groupoid_transport,
      pom_prime_register_strategy_gauge_groupoid_unlift_lift]

end

end Omega.POM
