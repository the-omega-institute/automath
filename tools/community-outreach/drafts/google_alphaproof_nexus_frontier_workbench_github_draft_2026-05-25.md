# Draft: GitHub Routing Question

Target: `google-deepmind/alphaproof-nexus-results` first; if maintainers point
elsewhere, move to `google-deepmind/formal-conjectures` Discussions.

Status: draft, do not post without final review.

## Title

Machine-usable Lean frontier workbench for AlphaProof-style proof search

## Body

Dear AlphaProof Nexus maintainers,

We read the AlphaProof Nexus paper with interest. We are pursuing a closely
related direction: building a machine-oriented Lean research environment for
active conjecture programs, where proof-search agents can consume formal
statements, verified intermediate artifacts, candidate certificate obligations,
route refutations, localized blockers, and explicit claim-state metadata.

Concretely, we have two public Lean libraries built for this purpose:

- **Automath / Omega**: https://github.com/the-omega-institute/automath  
  A Lean 4.28 library for finite algebraic, cubical, combinatorial, and
  proof-search-facing artifacts developed around active frontier programs.
- **NewMath / BEDC**: https://github.com/the-omega-institute/newmath  
  A Lean 4.28 library for reflective / compiler-style machine mathematics,
  designed to support derived-index analysis, ground-compilation style
  artifacts, and Automath-to-NewMath bridge tasks.

We are preparing a curated public surface around these libraries so machines and
agents can inspect, replay, prune, and continue the frontier programs directly.
The surface consists of build cards, selected Lean shards, program manifests,
claim-state metadata, and source-replay obligations.

The reason for contacting this repository is that the current state is already
structured in a machine-usable way:

- the Lean projects are buildable under Lean 4.28;
- intermediate reductions are separated from unresolved conjectural steps;
- failed routes are recorded as pruning information rather than discarded;
- candidate certificates are represented with source-replay obligations;
- each program carries a claim state such as `verified_reduction`,
  `candidate_certificate_source_replay_pending`, `route_refutation`,
  or `frontier_localization`.

Three current frontier programs illustrate the intended use.

1. A higher-rank same-W / finite-monodromy certificate candidate.
   - status: candidate certificate, source replay pending;
   - includes verified reductions around geometric-origin summands and
     p-curvature transport;
   - explicitly blocks the invalid shortcut
     `psi_p(W)=0 => psi_p(H)=0`;
   - current target is an A5 Godeaux-Serre rank-4 standard summand replay.

2. A representation-placement route refutation.
   - status: negative route audit / multiplicity zero for the current bridge;
   - records a KP2 stabilizer-fiber bridge failure where the actual fiber has
     unipotent generator action while the target representation has involutive
     generator action;
   - exposes the failed bridge as reusable proof-search pruning state.

3. A common finite-etale-cover frontier localization.
   - status: frontier localized to a primitive C4-cover blocker;
   - degree-2 and order-3 ledgers are closed;
   - remaining blocker is a `J_Y[4]` divisor-basis certificate and C4 Prym audit.

The contribution we want to make available is a machine-usable research
substrate:

```text
a stateful Lean proof-search workbench for frontier conjecture programs,
where each task has verified artifacts, blocked shortcuts, candidate certificate
obligations, route-refutation records, and localized blockers.
```

We would like to contribute this work in a form that is useful for
AlphaProof-style systems. A practical first step could be a small public
repository with:

- a build card for the Lean 4.28 projects;
- a machine-readable `PROGRAMS.jsonl`;
- selected Lean shards / anchors;
- source-replay obligations;
- route-refutation records;
- claim-state metadata.

We would be glad to hear your thoughts on how this could be made useful to your
proof-search pipeline or adjacent public infrastructure. In particular, we would
appreciate guidance on the most useful collaboration shape: issue discussion, a
separate companion repository, selected Lean shards, metadata formats, or
another route you would prefer.

Best,
lexa
