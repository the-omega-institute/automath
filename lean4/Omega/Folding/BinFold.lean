import Omega.Folding.FiberSpectrum
import Omega.Folding.HammingDist

/-! ### Binary Fold: folding integers via Zeckendorf projection -/

namespace Omega

/-- BinFold: project a natural number onto X_m via Zeckendorf truncation.
    cor:stable-add-computable -/
def cBinFold (m N : Nat) : X m := X.ofNat m N

/-- The BinFold fiber multiplicity. -/
def cBinFiberMult (m : Nat) (x : X m) : Nat :=
  (Finset.range (2 ^ m)).filter (fun N => cBinFold m N = x) |>.card

/-- The BinFold fiber histogram.
    thm:terminal-foldbin6-64-to-21-hist -/
def cBinFiberHist (m k : Nat) : Nat :=
  (@Finset.univ (X m) (fintypeX m)).filter (fun x => cBinFiberMult m x = k) |>.card

/-! ### m = 6 BinFold histogram -/

theorem cBinFiberHist_6_0 : cBinFiberHist 6 0 = 0 := by native_decide
theorem cBinFiberHist_6_1 : cBinFiberHist 6 1 = 0 := by native_decide
/-- thm:terminal-foldbin6-hist-2 -/
theorem cBinFiberHist_6_2 : cBinFiberHist 6 2 = 8 := by native_decide
/-- thm:terminal-foldbin6-hist-3 -/
theorem cBinFiberHist_6_3 : cBinFiberHist 6 3 = 4 := by native_decide
/-- thm:terminal-foldbin6-hist-4 -/
theorem cBinFiberHist_6_4 : cBinFiberHist 6 4 = 9 := by native_decide

/-- cor:terminal-foldbin6-certificate -/
theorem binFold6_histogram_certificate : 8 * 2 + 4 * 3 + 9 * 4 = 64 := by omega

/-- cor:terminal-foldbin6-distinct-multiplicities -/
theorem binFold6_distinct_multiplicities :
    cBinFiberHist 6 2 + cBinFiberHist 6 3 + cBinFiberHist 6 4 = 21 := by
  rw [cBinFiberHist_6_2, cBinFiberHist_6_3, cBinFiberHist_6_4]

theorem binFold6_sum_check :
    cBinFiberHist 6 0 * 0 + cBinFiberHist 6 1 * 1 + cBinFiberHist 6 2 * 2 +
    cBinFiberHist 6 3 * 3 + cBinFiberHist 6 4 * 4 = 64 := by
  rw [cBinFiberHist_6_0, cBinFiberHist_6_1, cBinFiberHist_6_2,
    cBinFiberHist_6_3, cBinFiberHist_6_4]

/-! ### m = 7 BinFold histogram -/

/-- thm:terminal-foldbin-hist -/
theorem cBinFiberHist_7_0 : cBinFiberHist 7 0 = 0 := by native_decide
/-- thm:terminal-foldbin-hist -/
theorem cBinFiberHist_7_1 : cBinFiberHist 7 1 = 0 := by native_decide
/-- thm:terminal-foldbin-hist -/
theorem cBinFiberHist_7_2 : cBinFiberHist 7 2 = 0 := by native_decide
/-- thm:terminal-foldbin-hist -/
theorem cBinFiberHist_7_3 : cBinFiberHist 7 3 = 13 := by native_decide
/-- thm:terminal-foldbin-hist -/
theorem cBinFiberHist_7_4 : cBinFiberHist 7 4 = 16 := by native_decide
/-- thm:terminal-foldbin-hist -/
theorem cBinFiberHist_7_5 : cBinFiberHist 7 5 = 5 := by native_decide

/-- thm:terminal-foldbin-hist -/
theorem binFold7_histogram_certificate : 13 * 3 + 16 * 4 + 5 * 5 = 128 := by omega

/-- Total stable words at m=7: |X_7| = 34.
    thm:terminal-foldbin-hist -/
theorem window7_histogram_count_sum :
    cBinFiberHist 7 3 + cBinFiberHist 7 4 + cBinFiberHist 7 5 = 34 := by
  rw [cBinFiberHist_7_3, cBinFiberHist_7_4, cBinFiberHist_7_5]

/-- Fiber sum at m=7: 13·3 + 16·4 + 5·5 = 128 = 2^7.
    thm:terminal-foldbin-hist -/
theorem window7_histogram_fiber_sum :
    cBinFiberHist 7 3 * 3 + cBinFiberHist 7 4 * 4 + cBinFiberHist 7 5 * 5 = 128 := by
  rw [cBinFiberHist_7_3, cBinFiberHist_7_4, cBinFiberHist_7_5]

/-- Collision dimension at m=7: Σ h_k · k² = 498.
    thm:terminal-foldbin-hist -/
theorem window7_collision_dimension :
    cBinFiberHist 7 3 * 3 ^ 2 + cBinFiberHist 7 4 * 4 ^ 2 + cBinFiberHist 7 5 * 5 ^ 2 = 498 := by
  rw [cBinFiberHist_7_3, cBinFiberHist_7_4, cBinFiberHist_7_5]; omega

/-! ### m = 8 BinFold histogram -/

set_option maxHeartbeats 800000 in
/-- thm:terminal-foldbin-hist -/
theorem cBinFiberHist_8_3 : cBinFiberHist 8 3 = 21 := by native_decide
set_option maxHeartbeats 800000 in
/-- thm:terminal-foldbin-hist -/
theorem cBinFiberHist_8_5 : cBinFiberHist 8 5 = 11 := by native_decide
set_option maxHeartbeats 800000 in
/-- thm:terminal-foldbin-hist -/
theorem cBinFiberHist_8_6 : cBinFiberHist 8 6 = 23 := by native_decide

/-- thm:terminal-foldbin-hist -/
theorem window8_histogram_count_sum :
    cBinFiberHist 8 3 + cBinFiberHist 8 5 + cBinFiberHist 8 6 = 55 := by
  rw [cBinFiberHist_8_3, cBinFiberHist_8_5, cBinFiberHist_8_6]

/-- thm:terminal-foldbin-hist -/
theorem window8_histogram_fiber_sum :
    cBinFiberHist 8 3 * 3 + cBinFiberHist 8 5 * 5 + cBinFiberHist 8 6 * 6 = 256 := by
  rw [cBinFiberHist_8_3, cBinFiberHist_8_5, cBinFiberHist_8_6]

/-- thm:conclusion-window8-groupoid-collision-dimension-identity -/
theorem window8_collision_dimension :
    cBinFiberHist 8 3 * 3 ^ 2 + cBinFiberHist 8 5 * 5 ^ 2 + cBinFiberHist 8 6 * 6 ^ 2 = 1292 := by
  rw [cBinFiberHist_8_3, cBinFiberHist_8_5, cBinFiberHist_8_6]; omega

/-! ### Edge separation at m = 6 -/

/-- BinFold separates hypercube edges at m = 6: flipping any single bit always
    changes the BinFold image.
    thm:terminal-foldbin6-cube-edge-separation -/
theorem binFold6_edge_separation :
    ∀ N : Fin 64, ∀ k : Fin 6,
      cBinFold 6 N.val ≠ cBinFold 6 (N.val ^^^ (2 ^ k.val)) := by native_decide

/-! ### Linear kernel obstacle -/

/-- There exists a stable word with BinFold multiplicity 3 (not a power of 2).
    cor:terminal-foldbin6-mult-three-exists -/
theorem binFold6_mult_three_exists : cBinFiberMult 6 (X.ofNat 6 9) = 3 := by native_decide

/-- Not all BinFold fiber multiplicities are equal (some are 2, some 3, some 4).
    cor:terminal-foldbin6-no-uniform-fibers -/
theorem binFold6_no_uniform_fibers :
    cBinFiberHist 6 2 ≠ 0 ∧ cBinFiberHist 6 3 ≠ 0 ∧ cBinFiberHist 6 4 ≠ 0 := by
  rw [cBinFiberHist_6_2, cBinFiberHist_6_3, cBinFiberHist_6_4]; omega

/-! ### Intra-fiber Hamming distance -/

/-- Convert a natural number to a Word m (big-endian binary).
    def:terminal-foldbin6-int-to-word -/
def intToWord (m : Nat) (N : Nat) : Word m :=
  fun i => decide (N / 2 ^ (m - 1 - i.val) % 2 = 1)

/-- Minimum Hamming distance within a BinFold fiber.
    def:terminal-foldbin6-min-hamming -/
def cBinFiberMinHamming (m : Nat) (x : X m) : Nat :=
  let preimages := (Finset.range (2 ^ m)).filter (fun N => cBinFold m N = x)
  let pairs := preimages.product preimages |>.filter (fun (a, b) => a < b)
  if h : pairs.Nonempty then
    pairs.inf' h (fun (a, b) => hammingDist (intToWord m a) (intToWord m b))
  else 0

/-- Histogram of intra-fiber minimum Hamming distances.
    def:terminal-foldbin6-min-hamming-hist -/
def cBinFiberMinHammingHist (m d : Nat) : Nat :=
  (@Finset.univ (X m) (fintypeX m)).filter (fun x => cBinFiberMinHamming m x = d) |>.card

/-- At m = 6, intra-fiber min Hamming distances take values 2, 3, 5.
    thm:terminal-foldbin6-fiber-hamming-three-valued-2 -/
theorem binFiber6_minHamming_hist_2 : cBinFiberMinHammingHist 6 2 = 13 := by native_decide
/-- thm:terminal-foldbin6-fiber-hamming-three-valued-3 -/
theorem binFiber6_minHamming_hist_3 : cBinFiberMinHammingHist 6 3 = 6 := by native_decide
/-- thm:terminal-foldbin6-fiber-hamming-three-valued-5 -/
theorem binFiber6_minHamming_hist_5 : cBinFiberMinHammingHist 6 5 = 2 := by native_decide

theorem binFiber6_minHamming_total :
    cBinFiberMinHammingHist 6 2 + cBinFiberMinHammingHist 6 3 +
    cBinFiberMinHammingHist 6 5 = 21 := by
  rw [binFiber6_minHamming_hist_2, binFiber6_minHamming_hist_3, binFiber6_minHamming_hist_5]

/-! ### Affine flat classification -/

/-- Test whether a BinFold fiber is an affine flat (3-point XOR closure).
    def:terminal-foldbin6-fiber-is-affine -/
def cBinFiberIsAffine (m : Nat) (x : X m) : Bool :=
  let preimages := ((Finset.range (2 ^ m)).filter (fun N => cBinFold m N = x)).sort (· ≤ ·)
  preimages.all fun a =>
    preimages.all fun b =>
      preimages.all fun c =>
        decide (cBinFold m (a ^^^ b ^^^ c) = x)

/-- Count of affine fibers at resolution m.
    def:terminal-foldbin6-affine-flat-count -/
def cAffineFlatCount (m : Nat) : Nat :=
  (@Finset.univ (X m) (fintypeX m)).filter (fun x => cBinFiberIsAffine m x) |>.card

/-- At m = 6, exactly 11 fibers are affine flats.
    thm:terminal-foldbin6-fiber-affine-geometry -/
theorem cAffineFlatCount_six : cAffineFlatCount 6 = 11 := by native_decide

/-- The non-affine fibers at m = 6: 21 - 11 = 10 fibers are non-affine.
    cor:terminal-foldbin6-non-affine-fiber-count -/
theorem nonAffineFiber_count_six : 21 - cAffineFlatCount 6 = 10 := by
  rw [cAffineFlatCount_six]

/-! ### Geometric stabilizer -/

/-- The geometric stabilizer at m = 6: the only δ ∈ {0,...,63} with
    BinFold(N) = BinFold(N ⊕ δ) for all N is δ = 0 (trivial stabilizer).
    cor:terminal-foldbin6-geo-stabilizer-trivial -/
theorem geoStabilizer_trivial :
    (Finset.range 64).filter (fun δ =>
      ∀ N : Fin 64, cBinFold 6 N.val = cBinFold 6 (N.val ^^^ δ)) = {0} := by
  native_decide

/-- The geometric stabilizer has order 1 (trivial).
    cor:terminal-foldbin6-geo-stabilizer-order -/
theorem geoStabilizer_order_one :
    ((Finset.range 64).filter (fun δ =>
      ∀ N : Fin 64, cBinFold 6 N.val = cBinFold 6 (N.val ^^^ δ))).card = 1 := by
  native_decide

/-! ### Type adjacency and Markov kernel

The type adjacency count A(x,y) counts the number of hypercube edges between
the BinFold fibers of x and y. This defines a symmetric weighted graph on X_m
(the "type graph") whose properties encode the Markov kernel of the folding. -/

/-- Type adjacency count: number of hypercube edges from fiber(x) to fiber(y).
    def:terminal-foldbin6-type-adj-count -/
def cTypeAdjCount (m : Nat) (x y : X m) : Nat :=
  let preX := (Finset.range (2 ^ m)).filter (fun N => cBinFold m N = x)
  preX.sum fun N =>
    (Finset.range m).filter (fun k =>
      cBinFold m (N ^^^ (2 ^ k)) = y) |>.card

/-- Type adjacency is symmetric at m = 6: A(x,y) = A(y,x).
    Quantified over stable value indices 0..20 to avoid noncomputable Fintype.
    thm:terminal-foldbin6-pushforward-markov-symm -/
theorem cTypeAdjCount_symm_six :
    ∀ i j : Fin 21,
      cTypeAdjCount 6 (X.ofNat 6 i) (X.ofNat 6 j) =
        cTypeAdjCount 6 (X.ofNat 6 j) (X.ofNat 6 i) := by native_decide

/-- Row sum of type adjacency equals 6 · d(x) at m = 6.
    thm:terminal-foldbin6-pushforward-markov-rowsum -/
theorem cTypeAdjCount_row_sum_six :
    ∀ i : Fin 21,
      (Finset.univ : Finset (Fin 21)).sum (fun j =>
        cTypeAdjCount 6 (X.ofNat 6 i) (X.ofNat 6 j)) =
        6 * cBinFiberMult 6 (X.ofNat 6 i) := by native_decide

/-- The type adjacency graph is nondegenerate: there exist adjacent type pairs.
    thm:terminal-foldbin6-pushforward-markov-nonzero -/
theorem cTypeAdjCount_nonzero_exists :
    cTypeAdjCount 6 (X.ofNat 6 0) (X.ofNat 6 1) > 0 := by native_decide

/-! ### Local/global separation -/

/-- Minimum BinFold fiber multiplicity at resolution m.
    def:conclusion-window6-bin-fiber-min-max -/
def cBinFiberMin (m : Nat) : Nat :=
  (@Finset.univ (X m) (fintypeX m)).inf' (@Finset.univ_nonempty _ (fintypeX m) (X.instNonempty m))
    (fun x => cBinFiberMult m x)

/-- Maximum BinFold fiber multiplicity at resolution m. -/
def cBinFiberMax (m : Nat) : Nat :=
  (@Finset.univ (X m) (fintypeX m)).sup' (@Finset.univ_nonempty _ (fintypeX m) (X.instNonempty m))
    (fun x => cBinFiberMult m x)

/-- Minimum BinFold multiplicity at m = 6 is 2.
    thm:conclusion-window6-local-index-global-compression-separation -/
theorem cBinFiberMin_six : cBinFiberMin 6 = 2 := by native_decide

/-- Maximum BinFold multiplicity at m = 6 is 4.
    thm:conclusion-window6-bin-fiber-max-six -/
theorem cBinFiberMax_six : cBinFiberMax 6 = 4 := by native_decide

/-- Local index < global compression: min_mult × |X_6| < 2^6.
    thm:conclusion-window6-local-index-lt-global-compression -/
theorem local_index_lt_global_compression :
    cBinFiberMin 6 * 21 < 2 ^ 6 := by
  rw [cBinFiberMin_six]; omega

/-- Total hidden dimensions at m = 6: 2^6 - |X_6| = 43.
    thm:conclusion-window6-total-hidden-dims -/
theorem total_hidden_dims_six : 2 ^ 6 - 21 = 43 := by omega

/-- The compression ratio bounds: min ≤ 2^m / |X_m| ≤ max.
    thm:conclusion-window6-compression-bounds -/
theorem compression_bounds_six :
    cBinFiberMin 6 ≤ 64 / 21 ∧ 64 / 21 ≤ cBinFiberMax 6 := by
  rw [cBinFiberMin_six, cBinFiberMax_six]; omega

/-- The multiplicity spread at m = 6: max - min = 2.
    thm:conclusion-window6-multiplicity-spread -/
theorem multiplicity_spread_six : cBinFiberMax 6 - cBinFiberMin 6 = 2 := by
  rw [cBinFiberMax_six, cBinFiberMin_six]

-- ══════════════════════════════════════════════════════════════
-- Phase R22: Three rigidity scales (conclusion chapter)
-- ══════════════════════════════════════════════════════════════

/-- Histogram entry: no stable words with BinFold multiplicity 5 at m=6.
    cor:conclusion-window6-three-rigidity-scales -/
theorem cBinFiberHist_6_5 : cBinFiberHist 6 5 = 0 := by native_decide

/-- Three rigidity scales at m=6: max fiber mult < |X_6| < 2^6.
    cor:conclusion-window6-three-rigidity-scales -/
theorem three_rigidity_scales_six :
    cBinFiberMax 6 < Fintype.card (X 6) ∧
    Fintype.card (X 6) < 2 ^ 6 := by
  constructor
  · rw [cBinFiberMax_six, X.card_eq_fib]; native_decide
  · rw [X.card_eq_fib]; native_decide

-- ══════════════════════════════════════════════════════════════
-- Phase R102: Window-6 capacity bifurcation
-- ══════════════════════════════════════════════════════════════

/-- Window-6 capacity formula C_6(B) = 8·min(2,2^B) + 4·min(3,2^B) + 9·min(4,2^B)
    evaluates to 21 at B=0, 42 at B=1, and saturates at 64 for all B ≥ 2.
    thm:conclusion-window6-capacity-bifurcation -/
theorem conclusion_window6_capacity_bifurcation :
    8 * min 2 (2 ^ 0) + 4 * min 3 (2 ^ 0) + 9 * min 4 (2 ^ 0) = 21 ∧
    8 * min 2 (2 ^ 1) + 4 * min 3 (2 ^ 1) + 9 * min 4 (2 ^ 1) = 42 ∧
    (∀ B : Nat, 2 ≤ B →
      8 * min 2 (2 ^ B) + 4 * min 3 (2 ^ B) + 9 * min 4 (2 ^ B) = 64) := by
  refine ⟨by omega, by omega, fun B hB => ?_⟩
  have h4 : 4 ≤ 2 ^ B := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ B := Nat.pow_le_pow_right (by omega) hB
  have hmin2 : min 2 (2 ^ B) = 2 := Nat.min_eq_left (by omega)
  have hmin3 : min 3 (2 ^ B) = 3 := Nat.min_eq_left (by omega)
  have hmin4 : min 4 (2 ^ B) = 4 := Nat.min_eq_left h4
  rw [hmin2, hmin3, hmin4]

-- ══════════════════════════════════════════════════════════════
-- Phase R23: Index-compression gap
-- ══════════════════════════════════════════════════════════════

/-- Max fiber mult × |X_6| ≠ 2^6 (non-uniform compression).
    thm:conclusion-window6-local-index-global-compression-separation -/
theorem local_index_ne_global_compression_six :
    cBinFiberMax 6 * Fintype.card (X 6) ≠ 2 ^ 6 := by
  rw [cBinFiberMax_six, X.card_eq_fib]; native_decide

/-- Max fiber mult > floor(2^6 / |X_6|).
    thm:conclusion-window6-local-index-global-compression-separation -/
theorem local_index_gt_global_ratio_six :
    cBinFiberMax 6 > 2 ^ 6 / Fintype.card (X 6) := by
  rw [cBinFiberMax_six, X.card_eq_fib]; native_decide

/-- Index-compression gap: max_mult × |X_6| - 2^6 = 20.
    thm:conclusion-window6-local-index-global-compression-separation -/
theorem index_compression_gap_six :
    cBinFiberMax 6 * Fintype.card (X 6) - 2 ^ 6 = 20 := by
  rw [cBinFiberMax_six, X.card_eq_fib]; native_decide

-- ══════════════════════════════════════════════════════════════
-- Phase R25: m=7 BinFold separation + three rigidity scales
-- ══════════════════════════════════════════════════════════════

/-- Maximum BinFold multiplicity at m=7 is 5.
    cor:conclusion-window6-three-rigidity-scales -/
theorem cBinFiberMax_seven : cBinFiberMax 7 = 5 := by native_decide

/-- Minimum BinFold multiplicity at m=7 is 3.
    cor:conclusion-window6-three-rigidity-scales -/
theorem cBinFiberMin_seven : cBinFiberMin 7 = 3 := by native_decide

/-- Three rigidity scales at m=7: max fiber mult < |X_7| < 2^7.
    cor:conclusion-window6-three-rigidity-scales -/
theorem three_rigidity_scales_seven :
    cBinFiberMax 7 < Fintype.card (X 7) ∧
    Fintype.card (X 7) < 2 ^ 7 := by
  refine ⟨?_, ?_⟩
  · rw [cBinFiberMax_seven, X.card_eq_fib]; native_decide
  · rw [X.card_eq_fib]; native_decide

-- ══════════════════════════════════════════════════════════════
-- Phase R28: m=7 index-compression gap
-- ══════════════════════════════════════════════════════════════

/-- Max fiber mult × |X_7| ≠ 2^7 (non-uniform compression at m=7).
    thm:conclusion-window6-local-index-global-compression-separation -/
theorem local_index_ne_global_compression_seven :
    cBinFiberMax 7 * Fintype.card (X 7) ≠ 2 ^ 7 := by
  rw [cBinFiberMax_seven, X.card_eq_fib]; native_decide

/-- Index-compression gap at m=7: max_mult × |X_7| - 2^7 = 42.
    thm:conclusion-window6-local-index-global-compression-separation -/
theorem index_compression_gap_seven :
    cBinFiberMax 7 * Fintype.card (X 7) - 2 ^ 7 = 42 := by
  rw [cBinFiberMax_seven, X.card_eq_fib]; native_decide

-- ══════════════════════════════════════════════════════════════
-- Phase R39: BinFold m=8
-- ══════════════════════════════════════════════════════════════

set_option maxHeartbeats 1600000 in
/-- Maximum binary fiber multiplicity at m=8.
    cor:conclusion-window8-max-fiber -/
theorem cBinFiberMax_eight : cBinFiberMax 8 = 6 := by native_decide

set_option maxHeartbeats 1600000 in
/-- Minimum binary fiber multiplicity at m=8.
    cor:conclusion-window8-min-fiber -/
theorem cBinFiberMin_eight : cBinFiberMin 8 = 3 := by native_decide

-- ══════════════════════════════════════════════════════════════
-- Phase R43: BinFold m=8 index-compression gap
-- ══════════════════════════════════════════════════════════════

set_option maxHeartbeats 1600000 in
/-- Max fiber mult x |X_8| ≠ 2^8 (non-uniform compression at m=8).
    thm:conclusion-window8-local-index-global-compression-separation -/
theorem local_index_ne_global_compression_eight :
    cBinFiberMax 8 * Fintype.card (X 8) ≠ 2 ^ 8 := by
  rw [cBinFiberMax_eight, X.card_eq_fib]; native_decide

set_option maxHeartbeats 1600000 in
/-- Index-compression gap at m=8: max_mult x |X_8| - 2^8 = 74.
    thm:conclusion-window8-local-index-global-compression-separation -/
theorem index_compression_gap_eight :
    cBinFiberMax 8 * Fintype.card (X 8) - 2 ^ 8 = 74 := by
  rw [cBinFiberMax_eight, X.card_eq_fib]; native_decide

-- ══════════════════════════════════════════════════════════════
-- Phase R104: nonexchangeable resources
-- ══════════════════════════════════════════════════════════════

/-- Window-6 resource allocation is nonexchangeable: |X_6| = 21 ≠ 2,
    the saturated capacity uses full coefficient ranges,
    and partial allocations produce 21 and 42.
    thm:conclusion-window6-nonexchangeable-resources -/
theorem conclusion_window6_nonexchangeable_resources :
    (21 : Nat) ≠ 2 ∧
    8 * 2 + 4 * 3 + 9 * 4 = 2 ^ 6 ∧
    8 * 1 + 4 * 1 + 9 * 1 = 21 ∧
    8 * 2 + 4 * 2 + 9 * 2 = 42 := by
  refine ⟨by omega, by omega, by omega, by omega⟩

end Omega
