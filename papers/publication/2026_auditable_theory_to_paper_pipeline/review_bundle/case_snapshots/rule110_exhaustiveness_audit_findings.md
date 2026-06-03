# Manifest exhaustiveness audit findings

`tools/manifest_exhaustiveness_audit.c` compares finite closure slices with the
assertion inputs listed in `.enum.ct` manifests. The audit treats each manifest
input as a GroundCompiler display stream and reports whether every generated
slice instance is present in the manifest.

## Target set

The audit set contains thirty-one concrete targets:

| target | closure slice | manifest cases | covered | status |
|---|---:|---:|---:|---|
| `BMark / msame_refl` | 2 | 2 | 2/2 | PASS |
| `BMark / msame_symm` | 4 | 4 | 4/4 | PASS |
| `BMark / msame_trans` | 8 | 8 | 8/8 | PASS |
| `BMark / msame_no_confusion` | 2 | 2 | 2/2 | PASS |
| `BHist / hsame_refl` | 3 | 5 | 3/3 | PASS |
| `BHist / hsame_symm` | 9 | 13 | 9/9 | PASS |
| `BHist / hsame_trans` | 27 | 8 | 6/27 | CONVENTION BOUND |
| `BHist / hsame_empty_inversion` | 5 | 5 | 5/5 | PASS |
| `BHist / hsame_constructor_distinct` | 6 | 12 | 6/6 | PASS |
| `Ext / ext_step` | 6 | 10 | 6/6 | PASS |
| `SigRel / sigrel_basic` | 27 | 9 | 0/27 | CONVENTION BOUND |
| `SameSig / samesig_equiv` | 27 | 9 | 0/27 | CONVENTION BOUND |
| `Cont / cont_basic` | 9 | 15 | 9/9 | PASS |
| `Unary / unary_basic` | 7 | 15 | 7/7 | PASS |
| `Ask / ask_basic` | 24 | 12 | 8/24 | CONVENTION BOUND |
| `ExternalBinary / external_binary_basic` | 9 | 17 | 9/9 | PASS |
| `GroundCompiler / flow_round_trip` | 3 | 5 | 3/3 | PASS |
| `GroundCompiler / bhist_injectivity` | 9 | 6 | 4/9 | CONVENTION BOUND |
| `GroundCompiler / reject_reasons` | 6 | 6 | 6/6 | PASS |
| `CircleModN / modn_classifier_concrete_rows` | 3 | 4 | 3/3 | PASS |
| `CircleModN / modn_singleton_operation_descent` | 3 | 4 | 3/3 | PASS |
| `CircleS1 / s1_e1_components_carrier_exactness` | 9 | 4 | 2/9 | CONVENTION BOUND |
| `FoldMomentKernelUp / fold_round_trip` | 3 | 3 | 1/3 | CONVENTION BOUND |
| `FoldMomentKernelUp / fold_tag_layout` | 3 | 3 | 1/3 | CONVENTION BOUND |
| `FoldMomentKernelUp / fold_event_flow_injective` | 3 | 3 | 1/3 | CONVENTION BOUND |
| `MetaCICAtom / inferAtom` | 20 | 7 | 6/20 | CONVENTION BOUND |
| `MetaCICBHist / bhistLen_natToBHist` | 4 | 5 | 4/4 | PASS |
| `MetaCICBHist / bhistToTerm_injective` | 12 | 8 | 6/12 | CONVENTION BOUND |
| `TopologyCarrier / finite_base_append_decomposition` | 18 | 5 | 1/18 | CONVENTION BOUND |
| `TopologyCarrier / finite_base_carrier_meet_scope` | 18 | 4 | 1/18 | CONVENTION BOUND |
| `TopologyLedgerRow / ledger_constructor_tags` | 21 | 9 | 9/21 | CONVENTION BOUND |

Summary:

```text
31 audit targets
17 strict PASS
14 convention bound
0 partial coverage
0 parse/enumeration failure
```

## Closure depths

`BMark` is nullary, so depth `1` is the full closed domain. Recursive `BHist`
targets use depth `1` unless a unary predicate needs the first mixed
depth-`2` slice. Relational fixtures such as `Ext`, `Cont`, and
`ExternalBinary` enumerate positive closure witnesses over source/input
histories up to depth `1`. GroundCompiler reject reasons are a closed
six-case decoder taxonomy.

Beyond-FKernel targets use the same explicit finite-slice convention. ModN
rows enumerate unary modulus values through depth `2` with singleton carrier
operands. S1 rows enumerate depth-`1` e1-component tails. FoldMomentKernelUp
rows enumerate a depth-`1` window-varying nine-field carrier surface. MetaCIC
rows enumerate bounded atom contexts, all-e0 `natToBHist` rows, and a mixed
closed/injective BHist term-embedding surface. Topology rows enumerate bounded
finite-base bundles and the six closed ledger constructor tags.

The audit target set only includes targets with an implemented C enumerator.
The tag-heavy fixture manifests for `Bundle`, `Gap`, `Package`, `NameCert`,
and `Settled` are not counted in the strict denominator here.

## Strict slices

Eight recursive or derived targets are strict finite slices because the missing
closure side is small and matches the manifest schema directly:

```text
BHist / hsame_symm: 6 closure cases, Lean BHist.Empty/e0/e1 and hsame := Eq
Ext / ext_step: 2 closure cases, Lean Ext.e0 and Ext.e1 constructors
Cont / cont_basic: 5 closure cases, Lean Cont h k r := r = append h k
Unary / unary_basic: 1 closure case, Lean UnaryHistory rejects e0 tails
ExternalBinary / external_binary_basic: 5 closure cases, Lean BWord := BHist and append reuse
CircleModN / modn_classifier_concrete_rows: 3 unary modulus cases with singleton carrier fields
CircleModN / modn_singleton_operation_descent: 3 unary modulus cases with Empty operation results
MetaCICBHist / bhistLen_natToBHist: 4 all-e0 rows through depth 3
```

Classification count:

```text
A: 8
B: 0
C: 14
```

No target uses a smaller closure depth. The partial targets are either small
enough for exact manifest coverage at their current depth or large enough to
require an explicit finite-witness convention bound.

## Convention bounds

Convention-bound targets are explicit finite-witness boundaries. They remain in
the audit denominator, print their closure and manifest counts, and do not make
strict mode fail.

`BHist / hsame_trans` is bounded because `BHist` is the recursive
`Empty/e0/e1` inductive and ordered triples grow cubically with the bounded
history slice; depth `1` has `27` triples and the manifest records `8`
representative equality and vacuity triples.

`SigRel / sigrel_basic` is bounded because Lean `SigRel` recurses over
`ProbeBundle` and delegates each cons step to abstract `AskSetup` evidence.
The manifest records `9` semantic examples, while the depth-`1`
bundle/history/result fixture closure has `27` triples.

`SameSig / samesig_equiv` is bounded because Lean `SameSig` is defined through
two `SigRel` witnesses and `hsame` on their results. It uses the same
depth-`1` fixture closure as `SigRel`, with `9` representative equivalence
examples against `27` generated triples.

`Ask / ask_basic` is bounded because Lean `AskSetup` supplies abstract
`ProbeName`, `Evidence`, and `Ask` fields. The C manifest fixes one executable
policy and lists `12` examples; the depth-`1` probe/history/mark/evidence
fixture closure has `24` tuples with `8` covered by the manifest.

`GroundCompiler / bhist_injectivity` is bounded because
`channel_encoding_bijection` and `legal_stream_completeness` range over
recursive BHist event streams. The manifest records `6` representative rows
against the `9` ordered depth-`1` BHist pairs, with `4` rows covered by the
generated closure.

`CircleS1 / s1_e1_components_carrier_exactness` is bounded because the Lean
carrier ranges over recursive rational component tails. The manifest records
`4` positive e1-component rows against the depth-`1` dx/dy tail surface, with
`2` rows covered by the generated closure.

The three `FoldMomentKernelUp` targets are bounded because the Lean carrier is
a nine-field recursive BHist product. The manifest records three visible kernel
flows, while the audit uses a depth-`1` slice that varies the first field and
keeps the other eight fields at `Empty`; each target covers `1/3`.

`MetaCICAtom / inferAtom` is bounded because context length and variable index
grow independently. The audit enumerates sort and var atoms over sort-only
contexts through length `3`; the manifest records `7` representative rows and
covers `6/20`.

`MetaCICBHist / bhistToTerm_injective` is bounded because the manifest combines
single-history closedness rows with pairwise injectivity rows. The generated
mixed surface has `12` inputs and the manifest covers `6`.

The two `TopologyCarrier` targets are bounded because finite-base bundles are
recursive and the Lean carrier is parametric in the ball predicate. The audit
uses left/right bundle length at most `1` with depth-`1` BHist items; the
manifests cover `1/18` representative rows.

`TopologyLedgerRow / ledger_constructor_tags` is bounded because the six
constructor tags are closed but full pairwise no-confusion has fifteen
unordered pairs. The manifest covers all six positive tag rows plus three
representative no-confusion rows, for `9/21`.

## Gate behavior

Default `make test` runs the audit in reporting mode and exits zero when the
tool parses and enumerates successfully. `make test-exhaustiveness` runs strict
mode and exits nonzero only on parse failures or unclassified partial coverage.
