import Mathlib.Data.Int.Basic

namespace Omega.POM

/-- Audited recurrence tables for the collision moments `S_q(m)`, in the form
`S_q(m) = Σ_i c_i S_q(m - i)` for `q = 2, ..., 23`. -/
def auditedMomentRecurrences : List (Nat × List ℤ) :=
  [ (2, [2, 2, -2])
  , (3, [2, 4, -2])
  , (4, [2, 7, 0, 2, -2])
  , (5, [2, 11, 8, 20, -10])
  , (6, [2, 17, 28, 88, -26, 4, -4])
  , (7, [2, 26, 74, 311, -34, 84, -42])
  , (8, [2, 40, 174, 969, 2, 428, -174, 4, -4])
  , (9, [2, 62, 386, 2819, 62, 900, -450])
  , (10, [2, 96, 830, 7945, 2, 1852, -830, 4, -4])
  , (11, [2, 153, 1740, 21249, -9432, -86213, -1484, -18348, 9174])
  , (12, [2, 243, 3608, 56447, -61236, -667319, 3608, -9582, 61242, 15404, -7216, 8, -8])
  , (13, [2, 388, 7414, 148038, -317916, -4165856, 136252, 1565891, 318938, 289380, -144690])
  , (14, [2, 621, 15140, 385463, -1443744, -22761161, 15140, -2116566, 1443750, 63044, -30280,
      8, -8])
  , (15, [2, 1000, 30766, 994458, -6188172, -119408756, 8289820, 134208623, 6186122, 16637076,
      -8318538])
  , (16, [2, 1611, 62312, 2559407, -24862788, -585266591, 62312, -44606766, 24862794, 255692,
      -124624, 8, -8])
  , (17, [2, 2599, 125872, 6569850, -96034590, -2764163954, -643026032, -15022392733, 769974566,
      15329386299, 642908352, 1347896340, -673948170])
  , (18, [2, 4196, 253750, 16841706, -359838840, -12680716224, -10092724500, -275807280985,
      -359838838, -45547388948, 10093485750, -1371988544, 719677692, 2063568, -1015000, 16,
      -16])
  , (19, [2, 6782, 510722, 43115177, -1319512222, -57102085832, -103492425230, -3287973427007,
      70431413590, 1820299893334, 141396315958, 1490826289911, -69111868602, 75808868436,
      -37904434218])
  , (20, [2, 10964, 1026646, 110369322, -4747929480, -252584574960, -930476920260,
      -34979269477849, -4747929478, -2366125043732, 930480000198, -18550240640, 9495858972,
      8300880, -4106584, 16, -16])
  , (21, [2, 17730, 2061690, 282555981, -16835263662, -1102832042704, -7541355704902,
      -337018569789879, -4580907037962, -178299513045558, 19655380096446, 491312623390091,
      4597742367158, 24228053037540, -12114026518770])
  , (22, [2, 28676, 4136950, 723669546, -58977801240, -4764905230944, -56923673862900,
      -3036610091030425, -58977801238, -123377166461588, 56923686273750, -233016526784,
      117955602492, 33325008, -16547800, 16, -16])
  , (23, [2, 46389, 8295828, 1854356343, -204594953196, -20423908865911, -406371384219676,
      -25926856168486983, 4571341699730040, 246398742959564703, 33380612780988, 1761279457237853,
      -8364467395452148, -214666561582310301, 372990762880716, -7586660581874892,
      3793330290937446]) ]

/-- Primitive recursive odd-lag sum. -/
def oddLagCoeffSumAux : Bool → List ℤ → ℤ
  | _, [] => 0
  | true, c :: cs => c + oddLagCoeffSumAux false cs
  | false, _ :: cs => oddLagCoeffSumAux true cs

/-- The sum of the odd-lag recurrence coefficients. -/
def oddLagCoeffSum (coeffs : List ℤ) : ℤ :=
  oddLagCoeffSumAux true coeffs

/-- Sum `c₁ x^e + c₂ x^(e-1) + ...` for a coefficient list. -/
def coeffWeightedSum : List ℤ → ℤ → Nat → ℤ
  | [], _, _ => 0
  | c :: cs, x, e => c * x ^ e + coeffWeightedSum cs x (e - 1)

/-- Evaluate `P_q(x) = x^d - c₁ x^(d-1) - ... - c_d` without constructing a polynomial object. -/
def momentCharpolyEval (coeffs : List ℤ) (x : ℤ) : ℤ :=
  x ^ coeffs.length - coeffWeightedSum coeffs x (coeffs.length - 1)

/-- The parity audit value `P_q(1) + P_q(-1)`. -/
def momentCharpolyParity (coeffs : List ℤ) : ℤ :=
  momentCharpolyEval coeffs 1 + momentCharpolyEval coeffs (-1)

/-- Across the audited range `q = 2, ..., 23`, every recurrence has odd order, the odd-lag
coefficient sum vanishes, and equivalently the characteristic-polynomial parity audit
`P_q(1) + P_q(-1)` is zero. `prop:pom-moment-odd-lag-neutrality` -/
theorem paper_pom_moment_odd_lag_neutrality :
    auditedMomentRecurrences.map Prod.fst = List.range' 2 22 ∧
      auditedMomentRecurrences.map (fun entry => entry.snd.length % 2) = List.replicate 22 1 ∧
      auditedMomentRecurrences.map (fun entry => oddLagCoeffSum entry.snd) =
        List.replicate 22 (0 : ℤ) ∧
      auditedMomentRecurrences.map (fun entry => momentCharpolyParity entry.snd) =
        List.replicate 22 (0 : ℤ) := by
  decide

end Omega.POM
