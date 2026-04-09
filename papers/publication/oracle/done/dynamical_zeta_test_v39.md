<!-- oracle metadata: {"timestamp": "2026-04-03T17:05:39.353659", "model": "o3-mini-high", "response_length": 13234} -->

According to a document from 2026-04-02, your project’s own latest internal framing is already pointing in one direction: the clean scorer is the reference model, richer scorer variants have not beaten it, the temperature sweep is still pending for a fair reranking test, and the strongest paper story is “systematic falsification of conditioning + generate-then-select + data quality beats model complexity + leak-safe benchmark.” 

technical_reference_bilingual

My blunt read: do a short code audit first, but do not bet the project on rescuing Dirichlet flow. The strongest evidence you have today says the generator failure is primarily an architecture/objective mismatch, not simply “no negatives.” Conditioned vs ablated outputs stay 75 to 78 percent identical, PLM prompting improves grammar but not target specificity, and adding pair-bias attention plus an energy head changes performance by essentially zero, with identity moving from 0.123 to 0.122. That is the pattern of a model learning the unconditional TCR prior and failing to transmit target information, not the pattern of a model that merely needs a few negative pairs. 

main

The other hard truth is that your decomposition is still a bit inconsistent. Stage 1 says V/J retrieval fixes the germline loops, but Stage 2 is then asked to regenerate all 6 CDRs. With only 185 structural training examples for the 6-CDR model, that is making the learning problem harder than the biology requires. The 6-CDR results also contain a red flag: CDR1β sits at 3.9 percent, near random, despite being germline-constrained, while CDR2β reaches 22.2 percent. That could reflect an unnecessarily hard objective, a loop-indexing issue, or both. 

technical_reference_bilingual

 

main

On your seven questions:

1. Best diagnosis

My ranking is:

1. Primary: the current generator framework is the wrong interface for this task.
You are forcing a discrete, highly multimodal, strongly conditioned design problem through a 20-dimensional simplex flow with token-level decoding. Your own falsification chain already argues that the conditioning pathway is the bottleneck. I think that is the best overall explanation. 

main

2. Secondary: there may still be a conditioning-path implementation or optimization bug.
I would not ignore this because a literal delta of negative 0.0005 after adding structural features is too clean. But even if there is a bug in G7, B4 and B9 already showed conditioning collapse before that, so a G7 bug cannot explain the whole project. 

DEV_PLAN

3. Secondary: data size is a real constraint, but not the main explanation for the null result.
With 345 complexes, and only 185 structural positives for 6-CDR generation, I would expect weak generalization. I would not expect near-complete indifference to conditioning unless the architecture/objective is also wrong. By contrast, the scorer improves dramatically once the data split is repaired, which tells you data quality matters a lot for discriminative modeling. 

technical_reference_bilingual

4. Tertiary: positive-only training matters, but it is not the main root cause.
Your advisor is directionally right that missing negative signal hurts specificity. But the transfer is not symmetric. A scorer can consume negatives directly with BCE. A generator cannot simply “add negatives” to flow-matching MSE and expect specificity to appear. For generators, negatives help only when turned into contrastive or preference objectives over hidden states or completed sequences.

So my answer is: the main problem is not positive-only training. It is a conditional discrete-generation architecture that is not actually using the condition.

2. Should you audit the code first?

Yes. Absolutely.

I would spend 2 to 3 days on a serious audit before publishing the sentence that the simplex pathway is “information-limited by design.” Right now the evidence is strong enough to justify that as a working hypothesis, but not yet strong enough to justify it as a final causal claim.

The audit I would run is very specific:

Trace the conditioning path end-to-end.
Confirm that pMHC pair features are nonzero after loading, slicing, masking, and normalization.

Measure scale, not just existence.
At each layer, compare the variance of pair_bias to the variance of raw QK^T / sqrt(d) logits. If the bias is two orders of magnitude smaller, G7 was numerically dead even if technically wired correctly.

Hook gradients.
Log gradient norms for pair_bias_proj, the pair-feature embedding, the pMHC encoder, and the energy head. If they are tiny or zero while the unconditional path trains, that is a conditioning-path failure.

Overfit a tiny toy set.
Pick 8 to 16 complexes and force the model to memorize them. If matched vs shuffled pMHC still barely changes the output, you have either a bug or an architecture that cannot carry the signal.

Run a positive-control condition.
Inject an explicit target-ID embedding or even a one-hot complex ID. If the model still cannot condition on that, the problem is in the architecture/code path, not in biological subtlety.

Audit loop indexing and chain mapping.
CDR1β at 3.9 percent and CDR3α at 5.1 percent are suspicious enough to justify checking whether the supervision and region order are exactly what you think they are. 

main

My prior is about 60 percent real architecture bottleneck, 40 percent implementation attenuation or scale failure. The audit matters, but I would not expect it to fully save the current flow framework.

3. Most promising generator fix

I would stop adding features to Dirichlet flow and switch the generator class.

The most promising replacement, given your data scale and existing codebase, is:

A scaffold-conditioned discrete generator with pMHC cross-attention, trained in two stages.

Concretely:

Keep Stage 1 retrieval. Use BLOSUM62 or scaffold selection to determine the germline background. Your docs already show BLOSUM62 beats ESM-2 + LoRA by 4.3x on V/J retrieval. 

technical_reference_bilingual

Do not freely regenerate all 6 loops. Keep CDR1/2 fixed by scaffold, or allow only a very small edit model on contact residues, especially in CDR2β.

Generate CDR3β + CDR3α, and optionally a tiny editable subset of CDR2β if you want to model the fact that it dominates interface energetics.

Reuse your existing conditional_plm.py path and turn it into either:

a masked infiller for the variable loops, or

an autoregressive decoder with pMHC cross-attention.

Then train with three signals:

Supervised token loss on positive native sequences.

Contrastive matched-vs-mismatched loss on pooled hidden states, so the generator’s internal representation must separate correct from wrong pMHCs.

Preference tuning after warm start, using your scorer as a reward model.

That third step is where negatives should enter. Not as “generate the opposite of this sequence,” but as pairwise preferences. Your own plan already has DPO-style preference fine-tuning on the table, and that is the right place to test your advisor’s intuition. 

DEV_PLAN

One more important change: the reward cannot be plain affinity. Your own scorer passes reranking discrimination but still fails cross-reactivity control on 2 out of 3 targets, and the docs explicitly note that binary labels do not teach exclusivity. So the reward should be something like:

R = S_target - max_offtarget(S_offtarget) - λ * overbinding_penalty - μ * developability_penalty

Without the off-target term, you will optimize “sticky TCRs,” not specific ones. 

technical_reference_bilingual

 

technical_reference_bilingual

4. Should physics be deeply integrated into generation?

Yes, but not as raw end-to-end energy chasing inside the current generator.

EvoDesign proves that physics-based structure reasoning is useful. But your own evaluations also show that fixed-backbone EvoEF2 is miscalibrated: designed energies are about 2x more favorable than native, and fixed-vs-flexible backbone scores are essentially uncorrelated with Spearman rho 0.047. That means “more direct energy guidance” can just teach the wrong objective faster. 

main

 

technical_reference_bilingual

So I would integrate physics in this order:

Proposal arm: EvoDesign remains a strong proposer.

Preference signal: use EvoEF2 as one term in DPO or candidate preference, but clipped or calibrated.

Post hoc validation: ESMFold/PyRosetta flexible validation remains mandatory.

I would not make raw EvoEF2 gradients the center of the new generator. Your energy function is fixed-backbone and over-optimizing. That is a poor objective to backpropagate more efficiently.

Related point: use EvoDesign as one proposer arm, not as the final truth model. It is the best current source of binders, but its over-optimization and target-dependent specificity mean it is not the whole answer. 

main

 

main

5. Is Dirichlet flow matching the wrong framework?

For this project, with this dataset, I think yes.

Not “provably wrong for all protein design.” But wrong as your primary framework.

Why:

discrete sequence design is more naturally modeled with discrete token objectives,

you have tiny conditional data,

you need strong conditioning bandwidth,

you already have evidence that PLM-style sequence priors and ProteinMPNN-like discrete structure models behave more sensibly than the flow model, even when they have their own flaws. 

main

 

main

My ranking of alternatives is:

1. Masked LM infilling.
Best first move. You already have code. It works naturally with fixed scaffolds and masked variable loops.

2. Autoregressive decoder, ProteinMPNN-style.
Also strong. Good conditioning interface. Risk is low diversity, so sample with temperature/top-p and rerank.

3. Discrete diffusion.
Scientifically plausible, but too much engineering for your current time pressure. I would not choose it as the next immediate bet.

The recent internal architecture note is already pointing in that direction by explicitly recommending masked LM or autoregressive generation to avoid the simplex low-dimensional problem. 

DEV_PLAN

6. Minimum viable fix under time pressure

There are really two different “minimum viable fixes.”

Smallest diagnostic fix:
Run the code audit plus a positive-control target-ID conditioning test. That tells you whether the current model can use any condition at all.

Smallest potentially publishable fix on the current codebase:
Use the existing temperature fix to restore diversity, then do off-target-aware DPO on the current generator. Your plan already notes that DPO changes the output distribution directly, unlike the pair-bias path that failed. That makes it the smallest nontrivial rescue attempt. 

DEV_PLAN

 

DEV_PLAN

But my honest view is that the smallest credible replacement is slightly bigger than that:

freeze scaffold,

reuse conditional_plm.py,

generate only CDR3β plus CDR3α, or CDR3β plus a tiny editable window in CDR2β,

add matched-vs-mismatched contrastive training.

That is still much smaller than building a brand-new diffusion system, and much more likely to show real condition use.

I would define success very modestly. You do not need native-like identity first. You need evidence that the generator is using pMHC:

null-input identity should drop well below 75 to 78 percent,

matched vs shuffled pMHC should measurably change outputs,

target-minus-off-target score margin should improve on at least 2 out of 3 targets,

candidate diversity should remain nontrivial after sampling.

7. Paper strategy

Do not wait months trying to resurrect the current flow generator before submitting something.

The strongest publishable story you have right now is:

Leak-safe evaluation and data-quality lesson.
Your scorer improved more from better split hygiene than from architecture complexity. That is a real field contribution. 

technical_reference_bilingual

Systematic falsification of conditional generation.
B4, B9, and G7 are not random failures. They form a coherent diagnostic program. 

main

 

main

DeepEvoDesign scorer as the main positive result.
Recent docs mark the clean scorer as the default reference model and the best current component. 

technical_reference_bilingual

Generate-then-select as the practical replacement.
The internal reference already recommends exactly this framing. 

technical_reference_bilingual

Design requirements for a next-gen generator.
Not “we failed.” Rather: “we ruled out one plausible generator family and derived a better decomposition.”

That is publishable if you restructure hard and stop pretending the old 3-stage flow narrative is still the paper’s center.

My only caution: until you finish the audit, I would soften the strongest claim. In the manuscript, say the results are consistent with an architectural bottleneck. After the audit, if the conditioning path is confirmed live and still useless, then you can say “bottleneck by design” more confidently.

My recommendation is a strict bounded plan: spend one week on audit + temperature sweep + one DPO pilot + one discrete masked-LM baseline. If none of those gives clear matched-vs-shuffled separation, retire Dirichlet flow from Paper 1 and submit the falsification/scorer/benchmark paper.