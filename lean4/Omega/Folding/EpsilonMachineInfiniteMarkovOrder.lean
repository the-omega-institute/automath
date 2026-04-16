import Omega.Folding.EpsilonMachineSynchronizingWord

namespace Omega.Folding

/-- Paper-facing data for the infinite Markov order / countably infinite epsilon-machine wrapper.
    The fields record the synchronizing-word package, the encoded predictive states `R_n`, and
    the mismatch of the next-symbol laws after the histories `00111 0^(k+1)` and
    `00111 0^(k+2)`. -/
structure EpsilonMachineInfiniteMarkovOrderData where
  isFiniteOrderMarkov : Prop
  hasCountablyInfiniteEpsilonMachine : Prop
  posteriorStateUpdate : Prop
  deterministicPosterior : Prop
  countableUnifilarWrapper : Prop
  update_witness : posteriorStateUpdate
  deterministic_of_update : posteriorStateUpdate → deterministicPosterior
  wrapper_of_deterministic : deterministicPosterior → countableUnifilarWrapper
  predictiveState : Nat → Nat
  predictiveState_injective : Function.Injective predictiveState
  nextSymbolLaw : Nat → Nat
  nextSymbolLaw_mismatch : ∀ k, nextSymbolLaw (k + 1) ≠ nextSymbolLaw (k + 2)
  finiteOrder_forces_eventual_agreement :
    isFiniteOrderMarkov → ∃ N, ∀ k ≥ N, nextSymbolLaw k = nextSymbolLaw (k + 1)
  countablyInfinite_from_wrapper_and_states :
    countableUnifilarWrapper → Function.Injective predictiveState →
      hasCountablyInfiniteEpsilonMachine

/-- Publication-facing wrapper: the synchronizing word yields a countable unifilar presentation,
the Fibonacci/Mobius seeds index the predictive states `R_n`, and the zero-run law mismatch
precludes any finite Markov order. Consequently the epsilon-machine has countably many predictive
states. `thm:fold-gauge-anomaly-epsilon-machine-infinite-markov-order` -/
theorem paper_fold_gauge_anomaly_epsilon_machine_infinite_markov_order
    (h : EpsilonMachineInfiniteMarkovOrderData) :
    ¬ h.isFiniteOrderMarkov ∧ h.hasCountablyInfiniteEpsilonMachine := by
  have hSync :=
    paper_fold_epsilon_machine_synchronizing_word
      h.posteriorStateUpdate
      h.deterministicPosterior
      h.countableUnifilarWrapper
      h.update_witness
      h.deterministic_of_update
      h.wrapper_of_deterministic
  have hFibSeeds := paper_fold_epsilon_machine_fibonacci_mobius_seeds
  have hInfiniteSeeds := paper_fold_epsilon_machine_infinite_markov_order_seeds
  have hStep : ∀ N : Nat, N + 1 > N := hInfiniteSeeds.2.1
  have hWrap : h.countableUnifilarWrapper := hSync.2.2.2.2
  constructor
  · intro hFinite
    obtain ⟨N, hAgree⟩ := h.finiteOrder_forces_eventual_agreement hFinite
    have hTail : h.nextSymbolLaw (N + 1) = h.nextSymbolLaw (N + 2) := by
      exact hAgree (N + 1) (Nat.le_of_lt (hStep N))
    exact h.nextSymbolLaw_mismatch N hTail
  · exact h.countablyInfinite_from_wrapper_and_states hWrap h.predictiveState_injective

end Omega.Folding
