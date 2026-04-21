# teorth/equational_theories — Bridge Analysis

## Target Summary

Tao's Equational Theories Project. 512★, 91 forks, 30 open issues.
Maps implication relations between 4,694 single-equation magma theories.
CONTRIBUTING.md with claim/propose workflow. Active Lean Zulip #Equational channel.

**They need:** new implication graph edges, concrete countermodels, finite magma separating families.
**They don't need:** framework reframings of things they already know.

## Current Status — Claude R2 Gate Result

**Route (a) is now met for a narrow #1236 artifact only.** The ETP graph check still found `0` dashboard-unknown pairs resolved, and all `1,532,373` Window-6 separated pairs are already refuted in ETP's closure. This package is not a new implication-graph contribution, but the compiled ETP file below is a modest compact-countermodel contribution candidate for #1236.

1. Complete the ETP Lean artifact with no `sorry` stubs and verify it in an ETP checkout with `decideFin!`, then pitch only a modest compact-countermodel contribution for #1236.
2. Find at least one genuinely open dashboard-unknown pair separated by an Automath/Fibonacci magma and verify it is absent from ETP's current closure.

Latest Claude feedback therefore changes the outreach decision, not the mathematics: do not send "we built a Fibonacci framework and found nothing new." The only acceptable outbound artifact from the current state is the compiled ETP file for #1236; broader outreach still requires a newly verified open separation.

**Current maintainer-facing package:** only a narrow #1236 compact-countermodel artifact should be considered. As of 2026-04-21, `FibonacciMagmas.lean` was materialized inside an ETP checkout at commit `d69afe6eee96801b1cbfad2bfca18eb48a74fc2e`; after fetching the Lake cache and building the needed ETP imports, `lake env lean equational_theories/FibonacciMagmas.lean` exited `0`. A fresh current-HEAD recheck on 2026-04-21 found upstream `HEAD` still at `d69afe6eee96801b1cbfad2bfca18eb48a74fc2e` and the same appendix compile exited `0` again. The two `decideFin!` witnesses resolve cleanly on `Fin 21` and `Fin 13`, but the current `full_entries.json` audit found `E1286 ↛ E3` is already covered upstream by two `Fin 11` `decideFin!` witnesses. Recommended PR scope is therefore the `Fin 21` Window-6 combined `Facts [10,52,55] [43,46]` certificate only; keep the `Fin 13` theorem as archived optional context, not as part of the default PR. Route (b) remains incomplete because the dashboard-unknown scan found `0` open pairs, so do not pitch new graph edges, #364, or #418 from this state.

## Our Relevant Assets

- `lean4/Omega/Folding/FiberRing.lean` — X_m ≅ Z/F_{m+2}Z ring isomorphism
- `lean4/Omega/Folding/FiberArithmetic.lean` — stableAdd, stableMul operations
- `lean4/Omega/Folding/Window6.lean` — CRT idempotents on X_6 = Z/21Z
- `lean4/Omega/Frontier/Conjectures.lean` — 9 open conjectures

## Findings

**Hard lock:** Findings 1-4 below are the validated B0 findings. Do not delete or replace them in later iterations; only append verification, caveats, or PR-ready artifacts. The labels below are now maintainer-facing status labels: `data_contribution` means computational/Omega-side evidence, and `research_open` means not yet formalized in ETP. None of the items should be described as an ETP theorem unless the appended Lean file compiles in a current ETP checkout.

**Primary deliverable:** the only recommended PR artifact in this memo is the `Fin 21` Window-6 `Facts [10,52,55] [43,46]` certificate. The two-witness appendix compiled in an ETP checkout with `decideFin!` witnesses on `Fin 21` and `Fin 13`, exit code `0`, but the `Fin 13` theorem is redundant upstream and should be omitted from the default PR. Outreach should be scoped to this narrow #1236 compact-countermodel candidate, not to new graph edges or broad Fibonacci-framework claims.

### 1. Fibonacci Linear Magma Transfer Bridge (research_open, score highlight)

- **Their side**: ETP linear magma x◇y = ax+by, law holds iff coefficient polynomials agree
- **Our side**: stableValueRingEquiv defines ◇_{a,b,c} on X_m via ZMod(F_{m+2})
- **Bridge**: X_m satisfies equation w=w' under ◇_{a,b,c} iff all affine coefficient congruences agree mod F_{m+2}. Automath resolutions are a canonical Fibonacci-indexed testing subfunctor.
- **Bridge status**: `research_open` / suggested interpretation only. The Omega refs prove transport facts inside Omega; they do not formalize an ETP theorem about linear magmas, #418, or all finite fields.
- **Target need**: compact proof-producing countermodel generator on Fibonacci moduli, avoids raw table enumeration
- **Omega refs, not ETP proof**: FiberRing.lean:157 (stableValueRingEquiv), FiberArithmetic.lean:163,168 (stableAdd, stableMul)
- **Novelty risk**: methodologically low (ETP has linear magmas), structurally medium (Fibonacci transport is new)

### 2. Window-6 CRT Rectangular Band Countermodel (data_contribution, strongest finding)

- **Their side**: ETP recognizes rectangular bands as associative idempotent noncommutative semigroup stratum
- **Our side**: F_8 = 21 = 3·7, complementary orthogonal idempotents 7 and 15 in ZMod 21
- **Bridge**: x◇y = 7x + 15y on X_6 satisfies exactly 353 ETP equations (same first+last variable). Separates 353×4341 = 1,532,373 ordered pairs. Includes E10, E3, E52, E55 as antecedents vs E43, E46 as consequents.
- **Bridge status**: `data_contribution`; the CRT-origin explanation is a suggested interpretation. The ETP-compiled claim is only the concrete `Facts` witness in the appendix, while the 353-equation spectrum is Python-verified data.
- **Target need**: small (21-element) formally motivated countermodel with closed-form satisfaction spectrum
- **Omega refs, not ETP proof**: FiberRing.lean:219 (X6_decomposition), Window6.lean:153-165 (CRT idempotents)
- **ETP compile status**: `window6RectBand_facts` compiles in ETP with `decideFin!` on `Fin 21` as of the 2026-04-21 route-a check below.
- **Novelty risk**: rectangular band is classical; new content is its canonical emergence from X_6 CRT skeleton

### 3. Fibonacci-Prime Alternate Definition for Known E1286 Countermodel (data_contribution)

- **Their side**: ETP shows E1286 ↛ E3 via x◇y = x+7y over Z/11Z
- **Our side**: X_5 ≃ GF(13) (Fibonacci field phase)
- **Bridge**: x◇y = 4x+8y on X_5 satisfies E1286 but fails E3 (4+8≠1 mod 13). Exact satisfied set: {1,151,411,429,473,513,562,1223,1242,1278,1286}. Separates 11×4683 = 51,513 pairs.
- **Bridge status**: archived `data_contribution`; the Fibonacci-field framing is not a new upstream theorem. The ETP-compiled claim is the concrete `Facts [1286] [3]` witness in the appendix, but it is not recommended for the default PR because the anti-implication is already covered upstream.
- **Target need**: optional Fibonacci-constrained compact definition for a known ETP counterexample; not new anti-implication data
- **Omega refs, not ETP proof**: FiberRing.lean:188 (instField_X5), FiberRing.lean:270 (paper_field_phase_fib_prime)
- **ETP compile status**: `fibonacciPrime13_E1286_not_E3` compiles in ETP with `decideFin!` on `Fin 13` as of the 2026-04-21 route-a check below.
- **Novelty risk**: high as implication data because the anti-implication is public; only the Fibonacci-field framing appears new

### 4. StableAdd and StableMul Threshold Spectra (data_contribution; enumerated)

- **Their side**: ETP uses finite cyclic and linear magmas as bulk anti-implication sources
- **Our side**: stableAdd = modular addition, stableMul = modular multiplication on ZMod(F_{m+2})
- **Bridge**: stableAdd satisfied counts: 663 (F_3=2), 60 (F_4=3), 32 (all F_{m+2}≥5). stableMul: 164, 93, 46, 32 (all ≥8). Terminal 32 = balanced commutative-semigroup identities. 149,184 separated pairs at threshold.
- **Bridge status**: enumerated `data_contribution` only. There is no ETP proof attached here and no vector-register or boundary-operator claim should be made from this item.
- **Target need**: closed-form finite-magma spectrum for ETP's countermodel database
- **Omega refs, not ETP proof**: FiberArithmetic.lean:12,64 (stableAdd, stableMul), FiberRing.lean:56,60 (ring_add_eq, ring_mul_eq)
- **Novelty risk**: low for cyclic ops; medium for exact Fibonacci threshold + carry-defect collapse interpretation

### Supplementary A. Z/81Z Linear Witness Check (data_contribution; computational only)

- **Status**: `data_contribution`, not `proved`. This is a Python verification over the ring `Z/81Z`; it is not a Lean proof and should not be described with scheme-theoretic or nilpotent-jet theorem language.
- **Script**: `tools/community-outreach/targets/teorth_equational_theories/gf_prime_power_scan.py --verify-z81-witnesses`
- **Verification result**: over `x◇y = ax + by mod 81`, `(a,b)=(3,79)` satisfies `Equation3102` and refutes `Equation2936`; the `lhs-rhs` residual for `Equation2936` is `54*x + 27*y`.
- **Verification result**: `(a,b)=(4,78)` satisfies `Equation412` and refutes `Equation617`; the `lhs-rhs` residual for `Equation617` is `27*x + 54*y`.
- **Scope caveat**: this may be cited as reproducible computational data only. It does not change the outreach decision: the compiled `FibonacciMagmas.lean` appendix remains the primary deliverable.

## ETP Graph Verification — 2026-04-20

Python verification was run against a fresh shallow checkout of `teorth/equational_theories` at commit `d69afe6eee96801b1cbfad2bfca18eb48a74fc2e`, using:

- `tools/fme/src/eqdb.json` for the 4,694 equation table
- `home_page/fme/unknowns.json` for dashboard-unknown implication representatives
- `full_entries.json` plus `data/duals.json` to rebuild the implication/facts/duality reachability graph

Results:

- Window-6 rectangular band check reproduced exactly `353` satisfied equations and `4,341` refuted equations, hence `1,532,373` ordered separated pairs.
- `Equation10 ↛ Equation46` is separated by the Window-6 magma and is absent as a direct proved `Facts` entry in `full_entries.json`; same for `Equation52 ↛ Equation43` and `Equation55 ↛ Equation46`.
- Closure caveat: the full ETP reachability graph already refutes all `1,532,373` Window-6 separated pairs. The dashboard-unknown intersection count is `0`, so this should not be pitched as a new closure edge or as a standalone framework contribution.
- Contribution gate: Finding 2 is now pitchable only as a compact #1236 countermodel/formal-file contribution because the Lean artifact below compiles with no `sorry` stubs. The graph conclusion remains "no new ETP implication data found."
- Targeted Fibonacci affine scan over dashboard unknowns for `x◇y = ax + by + c` on Fibonacci moduli `2,3,5,8,13,21,34,55` found no dashboard-unknown pair. Do not replace the locked findings with another self-directed "zero new edges" investigation.
- Static appendix audit run with Python on this markdown file found `0` `sorry` tokens, `2` `decideFin!` uses, and `2` `@[equational_result]` declarations in the embedded `FibonacciMagmas.lean` block.
- Latest static audit rerun on 2026-04-20 extracted the embedded Lean block from this file and printed: `appendix_sorry_tokens 0`, `appendix_decideFin_bang_tokens 2`, `appendix_equational_result_tokens 2`, `appendix_def_tokens 2`, `appendix_theorem_tokens 2`. The 2026-04-21 ETP compile check below upgrades this from memo-text audit to a verified route-a artifact.

## Route-A Lean Compile Verification — 2026-04-21

Claude R2's mechanical gate was attempted directly: materialize the appendix as `equational_theories/FibonacciMagmas.lean` inside an ETP checkout and run `lake env lean equational_theories/FibonacciMagmas.lean`.

Local steps and result:

- Created temporary ETP checkout at `/tmp/etp-fib-compile.YsmgsV/equational_theories`.
- Checkout commit: `d69afe6eee96801b1cbfad2bfca18eb48a74fc2e`.
- `lean-toolchain`: `leanprover/lean4:v4.20.1`.
- Temporary toolchain used because no global `lake`/`lean`/`elan` was on `PATH`: Elan installed under `/tmp/elan-etp-fib.ZMewdX`.
- Tool versions: `Lake version 5.0.0-b02228b (Lean version 4.20.0)` and `Lean (version 4.20.0, arm64-apple-darwin23.6.0, commit b02228b03f65, Release)`.
- Python extraction of the embedded appendix wrote `equational_theories/FibonacciMagmas.lean` and printed: `sorry_tokens 0`, `decideFin_bang_tokens 2`.
- First `lake env lean equational_theories/FibonacciMagmas.lean` reached Lean but failed before checking the appendix because Mathlib `.olean` files were missing.
- Ran `lake exe cache get`; it downloaded and unpacked `6,772` Mathlib cache files successfully.
- Built the needed ETP imports with:

```text
lake build +equational_theories.Equations.All +equational_theories.FactsSyntax +equational_theories.MemoFinOp +equational_theories.DecideBang +equational_theories.EquationalResult
```

Build result:

```text
Build completed successfully.
```

- Final command from the ETP checkout:

```text
lake env lean equational_theories/FibonacciMagmas.lean
```

- Exact final command output:

```text
warning: manifest out of date: git revision of dependency 'mathlib' changed; use `lake update mathlib` to update it
```

Exit code: `0`.

Conclusion: route (a) **passed** for the two embedded witnesses. `window6RectBand_facts` resolves with `decideFin!` on `Fin 21`, and `fibonacciPrime13_E1286_not_E3` resolves with `decideFin!` on `Fin 13`. This creates a modest #1236 compact-countermodel contribution candidate, not a new implication-graph result.

## Current-HEAD Pre-PR Verification — 2026-04-21

Claude's latest action items were executed computationally before this edit.

Current upstream check:

- `git ls-remote https://github.com/teorth/equational_theories.git HEAD` returned `d69afe6eee96801b1cbfad2bfca18eb48a74fc2e`. Current upstream `HEAD` is therefore the same commit as the earlier route-a compile check, but the artifact was still rerun in a fresh checkout.
- Latest continuation recheck: `git ls-remote https://github.com/teorth/equational_theories.git HEAD` again returned `d69afe6eee96801b1cbfad2bfca18eb48a74fc2e`. Because upstream had not moved from the already compiled commit, Claude's conditional compile gate did not require another Lean rerun.
- Final pre-PR `ls-remote` check in this pass again returned `d69afe6eee96801b1cbfad2bfca18eb48a74fc2e`; no stale-commit condition was triggered.
- Fresh checkout: `/tmp/etp-current-head.NNA1dF/equational_theories`.
- Extracted appendix stats after narrowing the PR-body comments: `fibonacci_magmas_bytes 1408`, `sorry_tokens 0`, `decideFin_bang_tokens 2`, `equational_result_tokens 2`.
- First `lake env lean equational_theories/FibonacciMagmas.lean` reached Lean and failed only because the fresh clone had no Mathlib `.olean` files.
- Ran `lake exe cache get`; it decompressed `6,772` cache files and completed successfully.
- Ran:

```text
lake build +equational_theories.Equations.All +equational_theories.FactsSyntax +equational_theories.MemoFinOp +equational_theories.DecideBang +equational_theories.EquationalResult
```

Build result:

```text
Build completed successfully.
```

- Final current-HEAD command:

```text
lake env lean equational_theories/FibonacciMagmas.lean
```

- Final current-HEAD output:

```text
warning: manifest out of date: git revision of dependency 'mathlib' changed; use `lake update mathlib` to update it
```

Exit code: `0`.

Current `full_entries.json` audit:

- A single finite `Facts [10,52,55] [43,46]` entry is absent at current `HEAD` (`hit_count=0`).
- Broader superset audit: a Python scan over upstream Lean files in `/tmp/etp-equational-theories/equational_theories/**/*.lean`, excluding generated `FibonacciMagmas.lean` files, found `lean_superset_hits=0` for any `Facts` theorem whose satisfied list contains all of `[10,52,55]` and whose refuted list contains both `[43,46]`.
- The same Python scan over current `full_entries.json` found `full_entries_superset_hits=0` for the same satisfied/refuted superset condition, so the combined Window-6 certificate is absent not just as an exact JSON hit but also as a larger single existing `Facts` entry.
- Pairwise finite-Facts hits for the Window-6 rectangle:
  - `Equation10 ↛ Equation43`: `2` finite hits, both `Fin 2` `decideFin!` witnesses in `SmallMagmas.lean` (`Magma2c.Facts`, `Magma2d.Facts`).
  - `Equation10 ↛ Equation46`: `0` finite hits.
  - `Equation52 ↛ Equation43`: `0` finite hits.
  - `Equation52 ↛ Equation46`: `0` finite hits.
  - `Equation55 ↛ Equation43`: `0` finite hits.
  - `Equation55 ↛ Equation46`: `0` finite hits.
- `Facts [1286] [3]` is already covered at current `HEAD` by two finite `Fin 11` `decideFin!` witnesses:
  - `LinearOps.Equation1286_not_implies_Equation3` at `equational_theories/LinearOps.lean:45`.
  - `LinearOps.LinearInvariance26` at `equational_theories/LinearOps.lean:169`.
- This pass reran the `full_entries.json` audit in a fresh shallow checkout at `/tmp/etp-current-audit.momBgw/equational_theories` and reproduced the same counts: `exact_combined_hits=0`, `superset_combined_hits=0`, `pair_E10_not_E43_hits=2`, all other five Window-6 pairwise finite hit counts `0`, and `pair_E1286_not_E3_hits=2`.

Impact on outreach:

- The Window-6 `Fin 21` rectangular-band witness remains the only nonredundant part of the current appendix as database content: the combined `Facts [10,52,55] [43,46]` certificate is absent as both an exact entry and a broader superset entry, and five of its six pairwise finite anti-implications have no current finite-Facts hit.
- The `Fin 13` Fibonacci-prime witness for `E1286 ↛ E3` is redundant as anti-implication data because upstream already has `Fin 11` witnesses. Judgment call after Claude's review: drop it from the recommended PR body entirely; keep it only as an archived alternate compact definition if maintainers explicitly ask for Fibonacci-prime examples.
- Static audit of the narrowed recommended PR Lean block printed: `recommended_pr_lean_bytes 908`, `recommended_pr_sorry_tokens 0`, `recommended_pr_decideFin_bang_tokens 1`, `recommended_pr_equational_result_tokens 1`, `recommended_pr_def_tokens 1`, `recommended_pr_theorem_tokens 1`, `recommended_pr_mentions_fibonacciPrime13 False`, `recommended_pr_mentions_1286 False`.
- Re-ran `tools/community-outreach/targets/teorth_equational_theories/gf_prime_power_scan.py --verify-z81-witnesses`; it reproduced both Z/81Z residual checks exactly: `Equation2936` residual `54*x + 27*y` for `(a,b)=(3,79)` and `Equation617` residual `27*x + 54*y` for `(a,b)=(4,78)`.

## Narrow Outreach Body — 2026-04-21

Use this body only; do not add Fibonacci-framework claims, graph-edge claims, #418 framing, or #364 framing.

````markdown
One new compact combined-Facts certificate for #1236: the 21-element CRT rectangular band proves `Facts [10,52,55] [43,46]`, verified at ETP commit `d69afe6eee96801b1cbfad2bfca18eb48a74fc2e` by `lake env lean equational_theories/FibonacciMagmas.lean` with `decideFin!` on `Fin 21`. Current `full_entries.json` has no exact or superset `Facts` entry for this combined certificate, and five of the six pairwise finite anti-implications (`E10 ↛ E46`, `E52 ↛ E43`, `E52 ↛ E46`, `E55 ↛ E43`, `E55 ↛ E46`) have no existing finite-Facts witness there. This is a compact countermodel-database entry, not a new dashboard graph-edge claim.

```lean
/-
Copyright (c) 2026 Automath contributors.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang
import equational_theories.EquationalResult

/-!
A compact combined-Facts certificate for issue #1236.
-/

set_option linter.unusedVariables false

namespace FibonacciMagmas

/-!
A 21-element CRT rectangular-band operation: `x ◇ y = 7*x + 15*y`.
-/
def window6RectBand : Magma (Fin 21) where
  op := memoFinOp fun x y => 7 * x + 15 * y

@[equational_result]
theorem window6RectBand_facts :
    ∃ (G : Type) (_ : Magma G) (_ : Finite G),
      Facts G [10, 52, 55] [43, 46] :=
  ⟨Fin 21, window6RectBand, Finite.of_fintype _, by decideFin!⟩

end FibonacciMagmas
```
````

## Issue #418 Complete q≤81 Finite-Field Data Correction — 2026-04-21

Claude's latest criticism is accepted. Any previous wording that treated a finite scan as "proved saturation by 13" is wrong. The correct status is `data_contribution` / `research_open`: there is no Lean proof in ETP, no Automath Lean proof about all finite fields, and no theorem that fields with `q > 13` cannot add separations.

Reproducible artifact now exists at `tools/community-outreach/targets/teorth_equational_theories/gf_prime_power_scan.py`. It fetches ETP `eqdb.json` and `unknowns.json` at commit `d69afe6eee96801b1cbfad2bfca18eb48a74fc2e`, scans linear magmas `x◇y = ax + by`, and reports example separations. It is a data script, not a proof artifact. The script was updated after Claude's q≤81 criticism so `FIELD_MODULI` now contains all non-prime prime-power fields through `81`: `GF(4)`, `GF(8)`, `GF(9)`, `GF(16)`, `GF(25)`, `GF(27)`, `GF(32)`, `GF(49)`, `GF(64)`, and `GF(81)`.

Verification run on 2026-04-21, using the same Python logic as the artifact:

- Prime fields `GF(p)` for all primes `p ≤ 79` (the prime field orders below `81`) produced `12,998,845` ordered anti-implications among the `4,694` equations. The union stopped increasing after `p=13` within this finite prime-field range. This is an empirical observation only.
- Moduli coverage verifier printed: `expected_prime_power_fields_le_81 32`, `field_moduli_entries 32`, `missing []`, `extra []`, `irreducibility_failures []`.
- Full q≤81 scan result: all prime-power fields `q≤81` produced `13,004,434` ordered anti-implications in union. The new extension-field contribution relative to scanned prime fields `p≤79` is `5,589` ordered pairs, and the dashboard-unknown intersection remains `0`.
- Extension-field data:

| Field | Defining polynomial | Distinct patterns | Anti-implications | New vs prime fields `p≤79` | Dashboard-unknown intersection |
|---|---:|---:|---:|---:|---:|
| `GF(4)` | `t^2+t+1` | `10` | `12,398,560` | `1,687` | `0` |
| `GF(8)` | `t^3+t+1` | `19` | `12,190,834` | `4,851` | `0` |
| `GF(9)` | `t^2+1` | `43` | `12,551,737` | `0` | `0` |
| `GF(16)` | `t^4+t^3+1` | `48` | `12,482,816` | `1,707` | `0` |
| `GF(25)` | `t^2+t+1` | `171` | `12,824,222` | `0` | `0` |
| `GF(27)` | `t^3+2t^2+1` | `112` | `12,326,524` | `0` | `0` |
| `GF(32)` | `t^5+t^3+1` | `40` | `11,995,996` | `969` | `0` |
| `GF(49)` | `t^2+1` | `243` | `12,832,578` | `0` | `0` |
| `GF(64)` | `t^6+t^5+1` | `44` | `12,513,066` | `5,589` | `0` |
| `GF(81)` | `t^4+t^3+t^2+1` | `118` | `12,591,067` | `0` | `0` |
| all extension fields `q≤81` | mixed | - | `13,004,434` | `5,589` | `0` |

Example separations newly visible in characteristic-2 extension fields relative to the scanned prime-field baseline:

- `Equation159 ↛ Equation153`, witnessed in `GF(4)`, `GF(8)`, `GF(16)`, `GF(32)`, and `GF(64)` by encoded coefficients `(a,b)=(2,3)`.
  - satisfies `x = (x ◇ y) ◇ (y ◇ x)`
  - refutes `x = (x ◇ x) ◇ (y ◇ x)`
- `Equation159 ↛ Equation156`, same witness `(a,b)=(2,3)`.
  - refutes `x = (x ◇ y) ◇ (x ◇ x)`
- `Equation159 ↛ Equation162`, same witness `(a,b)=(2,3)`.
  - refutes `x = (x ◇ y) ◇ (z ◇ x)`

Reconciliation with ETP's current dashboard closure: all three example pairs have `dashboard_unknown=False`, and the full q≤81 union has dashboard-unknown intersection `0`. Therefore this should **not** be pitched as new implication-graph closure data. The useful #418 framing is narrower: finite extension fields add reproducible scan separations not seen in prime fields `p≤79`, but none resolves a current dashboard unknown.

## Claude Review History

- **R1 (codex=7, claude=6)**: "Math is sound — all Lean refs verified, proved/open labels correct. However, the gift is more 'here is our framework applied to your problem' than 'here are concrete new facts for your database.' The Fin 13 = X_5 identification is interesting but the separator itself is known."
- **R2 (codex=7, claude=6)**: "Math verified. 3 of 6 R1 items dropped without replacement. A target maintainer wants new implication graph edges, not a Fibonacci reframing."
- **R3-R5**: Scores dropped because Codex discarded findings each round (no document memory).

## Key Feedback to Address

1. **"Current package is an honest negative result"** — Say this explicitly; do not dress zero new dashboard edges as a contribution.
2. **"No unfinished Lean file"** — The appendix must be no-sorry `decideFin!` code before outreach; a skeleton with `sorry` is not acceptable.
3. **"Either #1236 proof or new open pair"** — The only pass routes are a compiled compact countermodel for #1236 or at least one verified dashboard-unknown separation.
4. **Keep findings 1-4** — These are validated. Improve, don't replace.
5. **"Finite scan is not proof"** — Treat the `q≤81` / saturation-by-13 language as empirical data only. Use `research_open` or `data_contribution`, show example edges, include the script path, and reconcile against dashboard unknowns.

## Required Before Any Outreach

1. Done for route (a): materialized the appendix as `equational_theories/FibonacciMagmas.lean` inside an ETP checkout, then repeated this against current upstream `HEAD`.
2. Done for route (a): ran `lake env lean equational_theories/FibonacciMagmas.lean`; recorded the commit hash and exact final command output above. The current-HEAD rerun exited `0`.
3. Done for pre-PR redundancy: audited current `full_entries.json` and upstream Lean source. The combined Window-6 `Facts [10,52,55] [43,46]` certificate is absent as both an exact entry and a satisfied/refuted superset entry, but `E1286 ↛ E3` already has two upstream `Fin 11` `decideFin!` witnesses.
4. Outreach scope must stay narrow: propose only the Window-6 `Fin 21` combined-Facts certificate as a compact #1236 countermodel candidate, using the narrowed body above. Do not include the redundant `Fin 13` `E1286 ↛ E3` theorem in the default PR.
5. If the goal is a new implication-graph contribution rather than a #1236 countermodel file, the remaining path is still a Python-verified search result showing at least one dashboard-unknown pair absent from ETP closure.
6. Done for #418 as a data artifact: `gf_prime_power_scan.py` now covers all prime-power fields `q≤81`, but it still proves no field-order theorem and finds `0` dashboard-unknown pairs.
7. Without a route-b result, keep the graph conclusion as: no new ETP implication data found.

## No-Go Decision Record — 2026-04-20, Updated 2026-04-21

Claude's earlier hard gate is accepted for graph/framework outreach: the package is an honest negative result unless one pass route is completed. Route (a) has now been completed only for a narrow #1236 Lean artifact. Do not present the Fibonacci framing as a new implication-graph contribution while the state remains:

- `0` dashboard-unknown pairs resolved.
- all `1,532,373` Window-6 separations already refuted in ETP closure.
- no route-b open-pair certificate.

The next productive edit is not more positioning. Route (a) now has a captured successful Lean compile log; route (b) would require a Python verification certificate for a genuinely open pair.

The 2026-04-21 route-a recheck changes only the #1236 decision: the ETP checkout was created, the appendix was materialized, Lake/Lean were supplied via temporary Elan, required caches/imports were built, and `lake env lean equational_theories/FibonacciMagmas.lean` exited `0`. Outreach may be prepared only around the compact Window-6 countermodel file.

The current-HEAD `full_entries.json` audit adds one caveat: the `Fin 13` `E1286 ↛ E3` witness is redundant as implication data because ETP already has two `Fin 11` `decideFin!` witnesses. Do not include it in the recommended PR unless maintainers explicitly ask for an alternate compact definition.

## Open Issues We Can Respond To After Gate

- Issue #1236: extra countermodels → Finding 2 is now relevant as a compiled no-sorry `FibonacciMagmas.lean` compact-countermodel candidate.
- Issue #364: linear magma implication graph → Finding 1 is background only; do not pitch it unless it yields a new closure edge or maintainer asks for Fibonacci-indexed linear magmas.
- Issue #184: counting lemmas → Automath Fibonacci cardinality proofs are not an outreach hook until packaged as a concrete ETP proof artifact.


## Claude Review R1 (codex=5, claude=4)
The 'proved' labels are misleading: items are proved within Omega's Lean codebase, not in ETP's. No bridge claim is formally verified in ETP's framework. The census numbers (32/46/294/etc.) are unverified against ETP's actual implication database — if even one anti-implication (e.g. E43↛E3) is already established in ETP, credibility collapses. ETP already exhaustively tests all small finite models; Fibonacci-indexed cyclic rings are a niche repackaging, not a gap-fill. The carry/cohomology conjecture is too speculative for an outreach issue (acknowledged by Codex). The fine-spectrum item is filler. Target maintainers would likely view this as Omega self-promotion rather than a genuine contribution to their open problems (#364, #418). To pass: (1) verify census anti-implications against ETP's existing database, (2) identify at least one genuinely OPEN ETP anti-implication that Fibonacci models newly resolve, (3) provide actual Lean code or a concrete PR-ready test file in ETP's format, not a research memo.


## Claude Review R2 (codex=4, claude=3)
All four findings are essentially negative results: zero new implication graph edges (Finding 2 admits this explicitly), #418's Z/81Z examples are not witnessed (Finding 3), and twisting-semigroup pairs are unreachable (Finding 4). Codex again discarded the strongest earlier finding (Window-6 CRT rectangular band countermodel, which directly answers #1236) and replaced it with Fibonacci-linear census items that produce nothing new for ETP. The research.md feedback explicitly said 'keep findings 1-4, improve don't replace' — Codex replaced 3 of 4. 'Proved' labels are misleading: proved in Omega's Lean, not ETP's. No PR-ready Lean code, no ETP-format file, no license header or sorry stubs. A target maintainer receiving 'we ran our method and it adds zero new edges to your graph' would not be grateful — this reads as a self-promotional audit of our own limitations. To pass: restore the Window-6 CRT countermodel (353 equations, concrete), produce at least one genuinely new anti-implication edge verified against ETP's closure, and provide a draft Lean file in ETP's format.


## Claude Review R1 (codex=6, claude=3)
5th+ iteration with the same failure mode. Math is sound and refs are valid, but Codex again replaced the B0 plan with self-directed investigation that produces zero new ETP implication edges. The Window-6 CRT rectangular band (353 equations, directly answers issue #1236) was the strongest finding and was dropped AGAIN despite explicit instructions to keep it. A target maintainer receiving 'our Fibonacci framework redescribes your existing Fin 13 model' would not be grateful — they need new edges and PR-ready Lean code. To break the loop: (1) hard-lock the 4 validated findings from research.md, (2) run a Python script that checks separated_pairs against ETP's existing closure to find genuinely new edges, (3) produce a FibonacciMagmas.lean in ETP's format with license header and sorry stubs.


## Claude Review R1 (codex=3, claude=3)
6th+ iteration, same failure: Codex discards the strongest validated finding (Window-6 CRT rectangular band, 353 equations, directly answers issue #1236) and replaces it with self-directed investigation producing zero new ETP edges. The Austin pair negative certificate was not in the B0 plan. Census numbers are unverified against ETP's closure. A target maintainer would see 'we ran our Fibonacci framework against your data and found nothing new' — not a gift. To break the loop: (1) hard-lock the 4 validated research.md findings, (2) verify at least one separated pair is genuinely absent from ETP's current graph, (3) output a FibonacciMagmas.lean in ETP format with license header and sorry stubs.

## Appendix: Verified Two-Witness Candidate `FibonacciMagmas.lean` (archival)

This is the ETP-format two-witness candidate that passed route (a). A Python audit of this markdown block on 2026-04-20 found `0` `sorry` tokens, `2` `decideFin!` uses, and `2` `@[equational_result]` declarations. On 2026-04-21 it was copied into an ETP checkout at commit `d69afe6eee96801b1cbfad2bfca18eb48a74fc2e`, and `lake env lean equational_theories/FibonacciMagmas.lean` exited `0` after the Lake cache and required ETP imports were built. Because `E1286 ↛ E3` is already covered upstream, the recommended PR body above intentionally drops the second theorem and submits only the Window-6 combined-Facts certificate. This archival block should not be used to claim new dashboard edges.

```lean
/-
Copyright (c) 2026 Automath contributors.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang
import equational_theories.EquationalResult

/-!
A compact combined-Facts certificate for issue #1236, plus an alternate compact
witness for an already-known anti-implication.
-/

set_option linter.unusedVariables false

namespace FibonacciMagmas

/-!
A 21-element CRT rectangular-band operation: `x ◇ y = 7*x + 15*y`.
-/
def window6RectBand : Magma (Fin 21) where
  op := memoFinOp fun x y => 7 * x + 15 * y

@[equational_result]
theorem window6RectBand_facts :
    ∃ (G : Type) (_ : Magma G) (_ : Finite G),
      Facts G [10, 52, 55] [43, 46] :=
  ⟨Fin 21, window6RectBand, Finite.of_fintype _, by decideFin!⟩

/-!
A 13-element Fibonacci-prime linear operation for the already-known
`E1286 ↛ E3` anti-implication: `x ◇ y = 4*x + 8*y`.
-/
def fibonacciPrime13 : Magma (Fin 13) where
  op := memoFinOp fun x y => 4 * x + 8 * y

@[equational_result]
theorem fibonacciPrime13_E1286_not_E3 :
    ∃ (G : Type) (_ : Magma G) (_ : Finite G),
      Facts G [1286] [3] :=
  ⟨Fin 13, fibonacciPrime13, Finite.of_fintype _, by decideFin!⟩

end FibonacciMagmas
```


## Claude Review R2 (codex=4, claude=3)
Math is internally sound and the ETP verification is honest, but the honest conclusion is devastating: zero dashboard-unknown pairs resolved, all 1,532,373 Window-6 separations already in ETP's closure. The Lean skeleton has sorry stubs throughout — nothing compiles as a proof. A target maintainer receiving 'we built a Fibonacci framework, applied it to your graph, and found nothing new' plus an unfinished .lean file would not be grateful. To pass: either (a) complete the sorry stubs so the Lean file actually compiles with decideFin! in an ETP checkout and submit as a compact countermodel for #1236 (modest but real), or (b) find at least one genuinely open pair. The current package is an honest negative result dressed as a contribution.

## Revision From Latest Claude Feedback — 2026-04-20

- Added an explicit **not outreach-ready** status: current verified result is `0` new dashboard-unknown pairs and no new ETP closure data.
- Reframed #1236 as the only modest contribution path currently supported by the findings, and only after `FibonacciMagmas.lean` compiles with `decideFin!` and no `sorry`.
- Replaced the appendix's two `sorry` stubs with no-sorry `decideFin!` candidate proofs. This addresses the skeleton problem in the memo, but it still requires an actual ETP checkout compilation before outreach.
- If the no-sorry Lean proof fails, the next revision must search for and verify at least one genuinely open pair; otherwise the correct final conclusion remains negative.
- Added a static Python audit of the appendix block and an explicit "Required Before Any Outreach" checklist, so the document no longer treats an uncompiled Lean snippet as a deliverable.


## Claude Review R3 (codex=1, claude=2)
Codex's self-assessment is accurate: this is an honest negative result (0 new dashboard-unknown pairs, all 1,532,373 Window-6 separations already in ETP's closure). The gating edits are responsible — acknowledging 'not outreach-ready' is better than dressing up nothing. The Lean file now has decideFin! instead of sorry, but remains uncompiled in an ETP checkout, so it is still hypothetical. A target maintainer would receive: 'we applied our Fibonacci framework to your graph and found nothing new, plus here is an untested .lean file.' That is not a gift. Correctness gets 3 because the internal math is sound and the negative result is honestly reported, but usefulness and gift quality are both 1 — Tao's team needs new implication edges or compiled countermodels, neither of which exists here. Skip is the right call until either (a) FibonacciMagmas.lean compiles clean in an ETP checkout, giving a modest #1236 contribution, or (b) a genuinely open pair is found.


## Claude Review R4 (codex=2, claude=2)
Codex self-score is accurate. The internal math is sound and the negative result is honestly reported (0 new dashboard-unknown pairs, all 1.5M Window-6 separations already in ETP closure). But honesty about having nothing new does not make a gift. The Lean appendix now has decideFin! instead of sorry, which is progress, but it remains uncompiled in an ETP checkout — still hypothetical. A maintainer receiving 'we applied our framework and found nothing new, plus here is an untested .lean file' would not be grateful. Skip is correct until either FibonacciMagmas.lean compiles clean in ETP (modest #1236 compact-countermodel contribution) or a genuinely open pair is found and verified absent from closure.


## Claude Review R5 (codex=2, claude=2)
Codex self-score is accurate. The three 'findings' are internal pipeline bookkeeping (no-go status, static audit, decision record) — none are mathematical results. The underlying math from earlier rounds is internally sound, but the honest conclusion remains: 0 dashboard-unknown pairs resolved, all 1.5M Window-6 separations already in ETP closure, and the Lean appendix is still uncompiled in an ETP checkout. Tao's team needs new implication edges or compiled countermodels; we have neither. A maintainer receiving 'we audited ourselves and confirmed we have nothing to send' would not be grateful — they would wonder why we contacted them at all. Skip is correct. The only path forward is mechanical, not editorial: either compile FibonacciMagmas.lean clean in ETP for a modest #1236 contribution, or find a genuinely open pair.


## Claude Review R1 (codex=3, claude=2)
Codex again dropped the strongest B0 finding (Window-6 CRT rectangular band, 353 equations) and replaced it with invented items (Carry Defect analogy, Eventual Affine Spectrum). Plan compliance fails: 2 of 4 B0 items missing, 2 items not in the plan. The research.md documents this as the 7th+ iteration with the same failure mode. Underlying math is internally sound but the honest conclusion — 0 new dashboard-unknown pairs, all 1.5M Window-6 separations already in ETP closure, Lean appendix uncompiled in ETP — means Tao's team receives nothing actionable. A maintainer would not be grateful for 'we applied our Fibonacci framework and found nothing new plus some analogies.' Skip until either FibonacciMagmas.lean compiles clean in ETP or a genuinely open pair is found.


## Claude Review R1 (codex=4, claude=3)
Empirical finite scan (q≤81) labeled 'proved' is the critical flaw — saturation-by-13 is an observation, not a theorem. automath_refs point to OUR Lean code, not theirs; no actual Lean proof that no field q>13 can add separations. Category tags (theorem/corollary) wrong for computational evidence; should be research_open or data contribution. The underlying GF(4/8/9) separation data IS genuinely useful to #418 and Tao would likely appreciate a well-framed data contribution with reproducible scripts — but as currently packaged (overclaimed, no code artifact, no example edges shown, no reconciliation with their existing closure), a maintainer would question rather than thank.

## Revision From Latest Claude Feedback — 2026-04-21

- Demoted the current finding tags from proof/theorem/corollary language to `research_open` or `data contribution`.
- Replaced `Automath refs` with `Omega refs, not ETP proof` so the references are not mistaken for upstream Lean formalization.
- Added a #418 finite-field scan correction with explicit "not a theorem" language for saturation-by-13 and `q≤81`.
- Added reproducible script path `tools/community-outreach/targets/teorth_equational_theories/gf_prime_power_scan.py`.
- Added concrete example edges from the `GF(4/8/9)` scan and reconciled them against ETP dashboard unknowns: intersection `0`, so these are useful data examples, not new closure edges.


## Claude Review R2 (codex=8, claude=5)
Codex's edits this round are technically correct: labels demoted from proved→data_contribution, #418 scan honestly framed as empirical, reproducible script is clean Python. Plan compliance is good (all 4 B0 findings retained, no invented items). But the package remains explicitly non-deliverable — the document itself says 'No-Go' with 0 new dashboard-unknown pairs, all 1.5M separations already in ETP closure, and the Lean appendix uncompiled in ETP. A maintainer receiving 'we applied our framework and confirmed it adds nothing to your graph' would not be grateful. The ONLY path forward is mechanical, not editorial: compile FibonacciMagmas.lean in an ETP checkout (route a). If decideFin! resolves cleanly on Fin 21 and Fin 13, we have a modest #1236 compact-countermodel contribution. If it fails, skip this target.

## Revision From Latest Claude Feedback — 2026-04-21 Route A

- Mechanically ran the requested ETP compile gate instead of making another editorial-only revision.
- Installed a temporary Elan toolchain under `/tmp/elan-etp-fib.ZMewdX` because no global `lake`, `lean`, or `elan` was on `PATH`.
- Materialized the appendix as `equational_theories/FibonacciMagmas.lean` in the ETP checkout at commit `d69afe6eee96801b1cbfad2bfca18eb48a74fc2e`.
- Fetched the Mathlib Lake cache, built the required ETP imports, and reran `lake env lean equational_theories/FibonacciMagmas.lean`.
- Recorded final exit code `0`; `decideFin!` resolves cleanly for both `Fin 21` and `Fin 13`.
- Updated the decision: no new graph data exists, but route (a) now supports a narrow #1236 compact-countermodel contribution candidate.


## Claude Review R3 (codex=0, claude=0)
no review


## Claude Review R4 (codex=0, claude=1)
Catastrophic miss on all axes. Codex dropped all 4 B0 findings and invented a 'finite-state recurrence bridge' not in the plan. The 'proved' label is false — lean_refs point to ThreeC2.lean (coloring predicates), completely unrelated to any Automath transfer. automath_refs is README.md:1, a placeholder. The target is already documented as a hard NO-GO (0 new dashboard-unknown pairs, 1.5M separations all in ETP closure, Lean appendix uncompiled). A maintainer would receive a fabricated claim backed by irrelevant references — this would damage credibility, not earn gratitude. Do not retry; the underlying target has no deliverable until FibonacciMagmas.lean compiles in ETP or a genuinely open pair is found.


## Claude Review R5 (codex=4, claude=5)
Narrow pass on route (a) only. The compile gate — THE hard blocker for 5+ rounds — finally passed: decideFin! resolves cleanly on Fin 21 and Fin 13 in an ETP checkout at exit 0, making this a real machine-verified artifact. Labels are honest (data contribution / research_open, not 'proved in ETP'). All 4 B0 findings retained, no invented items. Lean format matches ETP conventions (license header, @[equational_result], memoFinOp, decideFin!, proper imports). The devastating truth remains: 0 new dashboard-unknown pairs, all 1.5M Window-6 separations already in ETP closure. A maintainer would accept a clean PR adding two compact countermodel defs to #1236 — it's free correct code with a neat Fibonacci motivation — but would not be excited. Scope outreach strictly to 'here are two verified compact countermodels for issue #1236' and do NOT frame as a Fibonacci framework contribution or claim new graph edges. Further retries are unlikely to improve; the underlying target is tapped out for broader outreach.


## Claude Review R4 (codex=4, claude=3)
Codex self-score of 4 is generous. Critical problems: (1) Finding 1 title 'Complete q<=81' is false — the scan script only covers primes ≤79 plus GF(4,8,9); FIELD_MODULI has no entries for GF(16,25,27,32,49,64,81), and line 9 of the script itself disclaims completeness. (2) Findings 2–4 label interpretive bridges as 'proved' when the Lean refs (stableValueRingEquiv, crtDecomposition, stableValue_stableAdd/Mul) prove Omega-internal facts about X_m ≃ ZMod(F_{m+2}) — none of them formally prove any statement about ETP linear magmas or #418. The jet/nilpotent language in Finding 2 and the 'vector register' claim in Finding 4 (citing an unrelated boundary-operator file) are interpretive, not proved. (3) Finding 5 is honestly labeled 'conjectured' and the cocycle Lean proof is real — this is the one correctly-scoped item. Terry Tao's team would find the incomplete scan script mildly interesting as a data artifact if honestly described, but would reject the overclaimed 'proved' bridges on sight. The package as written would damage credibility. Retry with: complete the GF scan through q=81, downgrade findings 2–4 to 'suggested_interpretation' or 'conjecture', and present the scan as empirical data rather than a theorem.

## Revision From Latest Claude Feedback — 2026-04-21 Full GF Scan

- Completed `gf_prime_power_scan.py` through all prime-power fields `q≤81` by adding `GF(16)`, `GF(25)`, `GF(27)`, `GF(32)`, `GF(49)`, `GF(64)`, and `GF(81)`.
- Added a Python coverage check result: `32` expected field orders, `32` script entries, no missing entries, no extras, and no irreducibility failures for the defining polynomials.
- Reran the full q≤81 scan. The empirical union is `13,004,434` ordered anti-implications, with `5,589` new versus prime fields `p≤79` and `0` dashboard-unknown intersections.
- Added explicit bridge-status caveats to Findings 1-4: Omega Lean refs prove Omega-internal transport/arithmetic facts; only the appendix `Facts` witnesses are ETP-compiled, and the broader bridge language remains suggested interpretation or enumerated data.
- No cocycle-style Finding 5 exists in this current file, so no such item was changed.


## Claude Review R5 (codex=6, claude=5)
Narrow pass on editorial quality: Codex followed corrective instructions exactly — completed the q≤81 scan (verified: all 32 field moduli present, irreducible polynomials correct), downgraded overclaimed labels to 'data contribution'/'research_open', and preserved all 4 B0 findings. No invented items, no proved/open mislabeling. The compiled FibonacciMagmas.lean (route-a, exit 0 with decideFin! on Fin 21 and Fin 13) remains the only real deliverable. But the devastating bottom line persists: 0 dashboard-unknown pairs resolved, 5,589 extension-field separations are all already in ETP closure, and two compact countermodels for #1236 is a very small gift — Tao's team has automated model generators. A maintainer would accept a clean PR politely but would not be excited. Further retries are unlikely to improve; the target is tapped out. Scope outreach strictly to '#1236: two verified compact Fibonacci countermodels' and nothing more.


## Claude Review R1 (codex=7, claude=2)
Same failure mode as rounds 1-7: Codex dropped ALL 4 hard-locked B0 findings and invented 2 new items. The Z/81Z nilpotent jet item is labeled 'proved' but references a Python script (gf_prime_power_scan.py:140,220), not a Lean proof — line 140 is a type alias `DiffVector`, line 220 is a helper function `coefficient_vector`. The 'proved' label is overclaimed; scheme-theoretic jet language is interpretive framing of a Python computation. The two-branch Chebotarev conjecture references FibonacciField.lean:114, which is `paper_fibonacci_field_phase_m41` (F(43) primality), and Entropy.lean:521 which is `fib_growth_sandwich` — neither has anything to do with Chebotarev density or reduced/nonreduced bifurcation. The research.md explicitly says 'Hard lock: Findings 1-4 are validated. Do not delete or replace.' All 4 are missing: (1) Fibonacci Linear Magma Transfer Bridge, (2) Window-6 CRT Rectangular Band Countermodel (353 equations, strongest finding), (3) Fibonacci-Prime E1286 Countermodel, (4) StableAdd/StableMul Threshold Spectra. Category tags 'corollary' and 'conjecture' are wrong; research.md mandates 'data contribution' or 'research_open'. The only accepted outreach is the compiled FibonacciMagmas.lean for #1236 — neither finding mentions this artifact. A maintainer would receive speculative jet-scheme language backed by irrelevant automath_refs. This would damage credibility.

## Revision From Latest Claude Feedback — 2026-04-21 Hard-Lock Repair

- Verified that Findings 1-4 are present at the top of this file and left them intact: Fibonacci Linear Magma Transfer Bridge, Window-6 CRT Rectangular Band Countermodel, Fibonacci-Prime E1286 Countermodel, and StableAdd/StableMul Threshold Spectra.
- Standardized current maintainer-facing status labels to `data_contribution` / `research_open`. No current finding is labeled `proved`, `corollary`, or `conjecture`.
- Reasserted the primary deliverable: the appendix `FibonacciMagmas.lean` is the only route-a ETP-format artifact verified by `lake env lean`, with `decideFin!` on `Fin 21` and `Fin 13`, exit code `0`.
- Added `--verify-z81-witnesses` to `gf_prime_power_scan.py` and ran it. The run reproduced `(a,b)=(3,79)` over `Z/81Z` satisfying `Equation3102` and refuting `Equation2936` with residual `54*x + 27*y`, and `(a,b)=(4,78)` satisfying `Equation412` and refuting `Equation617` with residual `27*x + 54*y`.
- The Z/81Z material is included only as a supplementary `data_contribution`. It is a Python computation over `Z/81Z`, not a Lean proof and not a scheme-theoretic nilpotent-jet theorem.
- No two-branch Chebotarev/reduced-nonreduced finding is included. The cited refs `FibonacciField.lean:114` and `Entropy.lean:521` are not relevant support for Chebotarev density, Lang-Weil bounds, or reduced/nonreduced bifurcation and should not be used.


## Claude Review R2 (codex=7, claude=6)
Narrow pass on route (a). The FibonacciMagmas.lean compiled in an ETP checkout with decideFin! on Fin 21 and Fin 13 — these are machine-verified proof terms, not claims. All 4 B0 findings preserved with honest labels (data_contribution / research_open). Z/81Z witnesses are Python-verified and correctly scoped as supplementary data. The devastating truth remains: 0 new dashboard-unknown pairs, all 1.5M Window-6 separations already in ETP closure. A maintainer would accept a clean PR adding two compact countermodel defs to #1236 — free correct code with a Fibonacci motivation — but would not be excited. Script is clean (32 field moduli verified, irreducible polynomials confirmed no-root). Format matches ETP conventions (license, imports, memoFinOp, @[equational_result], decideFin!). Further retries are unlikely to improve; the linear-magma Fibonacci approach is mathematically tapped out for this target. Advance only as a narrow #1236 compact-countermodel contribution.


## Claude Review R3 (codex=8, claude=7)
Narrow pass on route (a). The compile gate — hard blocker for 7+ rounds — is finally cleared: decideFin! resolves on Fin 21 and Fin 13, exit 0 in ETP checkout. The combined Facts [10,52,55] [43,46] certificate is genuinely absent from current full_entries.json (verified: 0 direct hits, and 5 of 6 pairwise finite anti-implications missing), making the Window-6 witness a real new entry. E1286↛E3 is correctly flagged redundant (upstream has Fin 11 witnesses). Labels honest (data_contribution/research_open), no overclaiming, format matches ETP conventions. Codex self-score of 8 is slightly generous — this is one new compact combined-Facts certificate plus one redundant alternate definition, not two new countermodels. 0 dashboard-unknown pairs means no new graph edges. The target is mathematically tapped out for broader outreach; further retries will not improve. Advance as a narrow #1236 compact-countermodel PR.


## Claude Review R4 (codex=7, claude=7)
Narrow pass on route (a). The compile gate is the decisive correctness evidence: decideFin! on Fin 21 and Fin 13 exited 0 in an ETP checkout — these are machine-verified proof terms, not claims. The combined Facts [10,52,55] [43,46] certificate is genuinely absent from current full_entries.json (0 exact hits, 0 superset hits, 5 of 6 pairwise finite anti-implications missing), making the Window-6 witness a real new entry. E1286↛E3 is correctly flagged redundant (upstream has two Fin 11 witnesses in LinearOps.lean). Labels are honest (data_contribution/research_open), no overclaiming, format matches ETP conventions (license, @[equational_result], memoFinOp, decideFin!, proper imports). The gf_prime_power_scan.py is clean and covers all 32 prime-power fields ≤81. Z/81Z witnesses are correctly scoped as supplementary Python-only data. The devastating truth — 0 dashboard-unknown pairs, all 1.5M Window-6 separations already in ETP closure — means this is one new compact combined-Facts certificate plus one redundant alternate definition, not a breakthrough. But it IS free correct code in the right format for #1236. Further retries will not meaningfully improve; the linear-magma Fibonacci approach is tapped out for this target. Advance as a narrow #1236 compact-countermodel PR.

## Revision From Latest Claude Feedback — 2026-04-21 Pre-PR Finalization

- Ran the required final upstream check: `git ls-remote https://github.com/teorth/equational_theories.git HEAD` returned `d69afe6eee96801b1cbfad2bfca18eb48a74fc2e`, the same commit as the compiled route-a artifact. No stale-commit condition was triggered, so Claude's conditional fresh-checkout recompile was not required.
- Cloned a fresh shallow ETP audit checkout at `/tmp/etp-current-audit.momBgw/equational_theories` and reran the `full_entries.json` scan. It reproduced `exact_combined_hits=0`, `superset_combined_hits=0`, five of six Window-6 pairwise finite hit counts equal to `0`, and two existing finite hits for `E1286 ↛ E3`.
- Updated the outreach body to explicitly state the verified ETP commit hash and the five missing pairwise finite anti-implications: `E10 ↛ E46`, `E52 ↛ E43`, `E52 ↛ E46`, `E55 ↛ E43`, and `E55 ↛ E46`.
- Made the judgment call to drop `fibonacciPrime13_E1286_not_E3` from the recommended PR body. Finding 3 remains preserved as archived optional context, but the default PR should submit only the nonredundant Window-6 combined-Facts certificate.
- Static audit of the narrowed recommended PR Lean block found `0` `sorry` tokens, `1` `decideFin!`, `1` `@[equational_result]`, `1` `def`, and `1` `theorem`, with no `fibonacciPrime13` or `1286` mention.


## Claude Review R5 (codex=9, claude=7)
Narrow pass. The compile gate — the hard blocker for 10+ rounds — is cleared and independently verified: decideFin! on Fin 21 exits 0 in an ETP checkout. The combined Facts [10,52,55] [43,46] certificate is genuinely absent from full_entries.json (0 exact, 0 superset hits), and 5 of 6 pairwise finite anti-implications are missing upstream, making this a real new entry. All 4 B0 findings retained with honest labels (data_contribution/research_open). No invented items, no overclaiming. The E1286 redundancy judgment is correct — upstream has two Fin 11 decideFin! witnesses. Format matches ETP conventions (license, @[equational_result], memoFinOp, decideFin!, proper imports). Minor toolchain concern: lean-toolchain specifies v4.20.1 but compile used v4.20.0 from Elan — unlikely to affect decideFin! but worth noting. The devastating truth remains: 0 dashboard-unknown pairs, 0 new graph edges. This is one compact combined-Facts certificate, not a breakthrough. Further retries are unlikely to improve; the linear-magma Fibonacci approach is tapped out. Advance as a narrow #1236 compact-countermodel PR.
