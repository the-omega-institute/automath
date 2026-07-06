# Novelty Audit: Canonical Zeckendorf Normalization and the Berstel Adder

Date: 2026-07-01

Scope: local audit after the RAIRO referee reports. This is not a replacement
for a full literature review, but it is intended to decide whether the revision
has a defensible novelty spine.

## Executive Verdict

Referee 1 is substantially correct about the main risk. In its submitted form,
the paper overclaimed novelty around phenomena that are already part of the
Fibonacci/confluent numeration and subsequential-transducer literature:

- one-sided non-subsequentiality of Fibonacci normalization,
- need for both left and right subsequential components,
- the classical ten-state Berstel adder,
- nonlocality of canonical normalization in local/parallel settings.

The revised manuscript should not try to defend the original novelty framing.
The viable route is a narrower one:

1. Make the paper a precise, self-contained note about the canonical
   Zeckendorf addition normalizer, with all models and conventions explicit.
2. Present only the following as possible new contributions:
   - explicit coordinatewise LSDF witness families for the ternary canonical
     addition normalizer;
   - exact prefix-destruction index `Delta(n)=n`;
   - restriction of the witness family to actual digitwise sums of admissible
     Zeckendorf representations;
   - residual minimality certificate for the displayed ten-state Berstel
     complete-output subsequential realization under its terminal-output
     convention.
3. Demote the rewrite-system and local-propagation results to self-contained
   setup/background unless a sharper nontrivial statement is added.

This is probably not enough for a normal full RAIRO article unless the revision
can convincingly argue that the exact prefix-destruction and residual
minimality statements were not previously explicit and are useful enough as a
technical note. A short-note framing is safer than a full-article framing.

## Claim-by-Claim Audit

| Claim | Likely status | Closest prior art / risk | Manuscript action |
|---|---|---|---|
| Fibonacci congruence quotient and canonical section | Known / expository | Zeckendorf theorem; Frougny; Sakarovitch; confluent systems | Keep as setup, not contribution. |
| Terminating local rewrite system with admissible irreducibles | Mostly known in spirit | Fibonacci congruence and normalization rewrite literature | Keep only as a self-contained presentation; do not claim confluence or general novelty. |
| LSDF coordinatewise unbounded anticipation for `Fold_infty` on `{0,1,2}` finite-support inputs | Possibly new as an explicit witness theorem, but high prior-art risk | Referee 1: normalization `nu:{0,1}*->{0,1}*` is already neither right nor left subsequential; Sakarovitch/Frougny imply broad obstruction | Reframe as an explicit witness refinement for the ternary canonical addition normalizer, not as a new non-subsequentiality phenomenon. |
| LSDF finite-word `N:{0,1,2}*->{0,1}*` not deterministic subsequential | Likely known or immediate from known normalization obstruction | Sakarovitch decomposition; Frougny normalization results; Mousavi-Schaeffer-Shallit example noted by referee | Do not headline alone. It is useful only when paired with exact witness/index statements. |
| `Delta(n)=n` exact prefix-destruction index | Best candidate for a genuine small contribution | May be implied by known obstruction, but exact named index and tight witness may not be explicitly published | Make this the main new theorem if keeping the paper. Explain why it refines known non-subsequentiality. |
| Witnesses inside genuine addition image `{c+d}` | Possible small strengthening | Could be considered obvious if every ternary witness can be decomposed or if known proofs already use addition words | Keep as a corollary; do not overstate. Emphasize it prevents the obstruction from being an artifact of arbitrary ternary inputs. |
| Ten-state Berstel adder exists | Known | Berstel; Frougny; Labbé--Lepšová | Must not be claimed as new. |
| Residual minimality of displayed ten-state complete-output subsequential realization | Possible contribution, but fragile | Referee 1 suspects Mousavi-Schaeffer-Shallit proof may imply minimality; 16-state automaton correctness does not automatically imply minimality | State narrowly: pairwise inequivalence of the ten displayed residual functions under the terminal-output convention; avoid saying "the Berstel adder is minimally 10 states" without qualifiers. |
| Shortest separating word length at most 1 for residual pairs | Possibly new certificate detail | Not likely a major contribution alone | Fold into the residual minimality theorem as an audit certificate. |
| Local fixed-radius propagation lower bound | Probably known / too close to prior result | Referee 1 says it is Proposition 14 in cited paper; parallel addition literature | Demote or remove. If retained, explicitly say it is included only for self-contained comparison of the same witness family. |

## Deep Dive: `Delta(n)=n`

This is the strongest possible novelty spine because it is not merely the
negative statement "not subsequential." It gives a quantitative, exact
prefix-destruction measure:

`Delta(n)` is the maximum possible loss of common normalized-output prefix when
one input word is a proper prefix of another and the shorter normalized output
has length `n`. The theorem says the trivial upper bound is always attained.

Why it may be defensible:

- Known non-subsequentiality says no finite right-subsequential transducer
  realizes the normalizer.
- `Delta(n)=n` says more: prefix extension can destroy the entire normalized
  output prefix at every output length.
- The submitted proof gives explicit parity-separated witnesses.

Why it may still be considered too small:

- If Sakarovitch/Frougny already give examples equivalent to complete prefix
  destruction, then this is just a renamed corollary.
- Even if not explicitly written, the referee may judge it routine once the
  classical obstruction is known.

How to strengthen it honestly:

- Add a subsection "Relation to known non-subsequentiality" explaining that
  this is a quantitative strengthening, not a new decidability/realizability
  theorem.
- State the theorem before the broad non-subsequential corollary, so the
  qualitative obstruction follows from the exact index.
- Consider defining `Delta` for both `{0,1}` normalization and `{0,1,2}`
  addition normalization; if the exact index differs or the ternary/addition
  case has a sharper form, that would improve novelty. This requires proof,
  not rhetoric.

## Deep Dive: Genuine Addition Image Witnesses

The corollary that the obstruction appears on actual digitwise sums of
admissible Zeckendorf inputs is useful because it prevents a referee from
saying the `{0,1,2}` counterexamples are artificial.

However, it is probably not enough as a main contribution. The witness
decompositions in the proof are simple, and a knowledgeable referee may regard
them as immediate.

Best use:

- Keep as a corollary after `Delta(n)=n`.
- Describe it as "the quantitative obstruction is already present on true
  addition inputs" rather than as a separate new theorem.

## Deep Dive: Berstel Residual Minimality

Correctness of a 16-state automaton does not automatically imply minimality of
the classical 10-state complete-output transducer. It may imply or contain a
minimization certificate if the authors performed state minimization or if the
automaton is presented as minimized, but correctness alone is weaker.

The defensible theorem is:

> For the complete-output subsequential function induced by the displayed
> ten-state Berstel transducer, with terminal output retained as part of the
> output convention, the ten reachable residual functions are pairwise
> inequivalent; indeed all unequal-terminal pairs are separated by the empty
> word and the five equal-terminal pairs are separated by input `0`.

This theorem is precise and checkable. It avoids overclaiming because:

- it does not say the existence of a ten-state adder is new;
- it does not claim minimality for every possible encoding convention;
- it acknowledges that absorbing terminal output can change the state count;
- it frames the result as a residual certificate.

Risk:

- A referee may still consider this too elementary for publication.
- If Berstel or later sources already mention minimality, it is not new.

Recommended action:

- Keep the theorem but make it the second contribution, after `Delta(n)=n`.
- Add a sentence that this is an audit certificate for the displayed kernel,
  not a historical claim about the discovery of the ten-state adder.

## Deep Dive: Local Lower Bound

This is the weakest part as a claimed contribution. Referee 1 explicitly says
the local-function result is already Proposition 14 in a cited paper. Unless
the present theorem differs materially in model, alphabet, radius convention,
or quantitative bound, it should not be a headline result.

Recommended action:

- Demote it to a final "same witness also gives..." proposition.
- Or remove it entirely if space/novelty pressure is high.
- If retained, add a comparison sentence naming the prior proposition and
  explaining the exact difference.

## Recommended Revision Strategy

Choose option B: convert the manuscript into a short technical note or a very
narrow major revision.

The strongest honest framing:

> This note does not rediscover finite-state Fibonacci normalization. It
> isolates the canonical LSDF addition normalizer and records two explicit
> finite-state obstruction certificates: complete prefix destruction at every
> output length, already on genuine addition inputs, and a residual-state
> minimality certificate for the classical Berstel complete-output kernel.

This is more defensible than claiming a new theory of Zeckendorf addition.

## Proposed Main Theorem Package

### Theorem A: Canonical Section and Rewrite Normalization

Expository setup. State as a self-contained construction, not as novelty.

### Theorem B: Exact LSDF Prefix Destruction

For the canonical LSDF finite-word normalizer

`N:{0,1,2}* -> {0,1}*`,

the prefix-destruction index satisfies

`Delta(n)=n` for all `n>=1`.

Consequences:

- no deterministic subsequential realization in LSDF order;
- coordinatewise unbounded anticipation;
- no bounded one-pass delay.

This theorem should be the main novelty candidate.

### Corollary C: The Obstruction Occurs on True Addition Inputs

The prefix-destruction / unbounded anticipation witnesses may be chosen as
digitwise sums of two admissible Zeckendorf representations.

This supports arithmetic relevance.

### Theorem D: Residual Minimality Certificate for the Berstel Kernel

For the displayed ten-state complete-output Berstel transducer, the ten
reachable residual functions are pairwise inequivalent under the stated
terminal-output convention. The five nontrivial equal-terminal pairs are
separated by input `0`.

This is a useful audit certificate, not a claim that the ten-state adder was
previously unknown.

### Optional Proposition E: Local Propagation Witness

Keep only if directly compared to the prior Proposition 14. Otherwise remove
from the main contribution list.

## Bottom Line

The paper can probably be made honest. It may or may not be publishable at
RAIRO. To maximize its chance, the revision must stop defending broad novelty
and instead defend a narrow exact-certificate contribution. If the authors can
verify that `Delta(n)=n` and the ten-state residual certificate are not
explicitly in the prior literature, the paper has a plausible short-note
route. If either of those is already explicitly known, withdrawal or retargeting
is the safer path.
