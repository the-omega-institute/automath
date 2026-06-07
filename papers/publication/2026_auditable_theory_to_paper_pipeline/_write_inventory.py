import json, re
from pathlib import Path
lines=Path('main.tex').read_text(encoding='utf-8').splitlines()
pat=re.compile(r'\\begin\{(definition|theorem|lemma|proposition|corollary)\}(?:\[([^\]]*)\])?')
items=[]
for i,line in enumerate(lines,1):
    m=pat.search(line)
    if not m: continue
    lab=''
    for j in range(i,min(i+8,len(lines))+1):
        lm=re.search(r'\\label\{([^}]*)\}', lines[j-1])
        if lm: lab=lm.group(1); break
    items.append({'line':i,'env':m.group(1),'label':lab,'title':m.group(2) or ''})
def labels(a,b): return '; '.join(x['label'] for x in items[a-1:b])
def loc(a,b): return f"main.tex:{items[a-1]['line']}-main.tex:{items[b-1]['line']}"
def obj(label, location, reason, action, **kw):
    d={'label':label,'location':location,'reason':reason,'required_action':action}; d.update(kw); return d
present_specs=[
(1,2,'Package-shape and nested route-state conventions','Defines the primary article, supplement, theorem inventory, review bundle, human-promotion boundary, and daemon-visible active-paper boundary.','Keep as package-boundary spine; refresh support logs after final inventory generation.'),
(3,4,'Architecture axes and non-escalation','Defines the five evidence axes and proves no axis certifies stronger claims on another axis.','Keep as the core architecture theorem pair.'),
(5,13,'Bounded source-interface extraction and separation','Covers source_interface_record.json, pinned snapshot consistency, bounded maximality, public-source non-escalation, and semantic-completeness obstruction.','Keep as traceability machinery; add public fetch/compare logs only if public-source byte equality is claimed.'),
(14,18,'Operational finite-record vocabulary','Defines the operational acceptance interface, record-gate soundness, stronger-reading preorder, and certificate schema.','Keep definitions visible in the short presentation.'),
(19,27,'Executable verifier exactness and trust boundary','Establishes schema-relative verifier exactness, finite-coordinate determination, rigidity, and the obstruction from finite-record acceptance to implementation soundness.','Keep as the formal trust-boundary core.'),
(28,37,'Machine-readable records and finite obstruction mechanisms','Connects certificate JSON rows to TeX claims, dispatches claim kinds, and gives bad-subrecord and extension-budget obstructions.','Keep in supplement; rerun certificate scripts after inventory changes.'),
(38,43,'Publication-safety dependency and main theorem','Separates gate interfaces, human promotion, daemon active tracks, scheduler advice, command-run evidence, and proves the bounded publication-safety interface under record-gate soundness.','Keep as central theorem chain; do not hide the external soundness hypothesis.'),
(44,56,'Finite-record maximality and implementation-upgrade barriers','Proves rigidity, exact non-gluing, boundary normal forms, five-axis upgrade obstruction, maximality, and implementation-soundness extension criteria.','Keep as technical support, compressing only presentation prose.'),
(57,64,'Current-package certificate instantiation','Instantiates the abstract calculus on current_package_pass_records.json and the primary-claim inventory while preserving path-verified status.','Refresh if any ledger row or primary inventory row changes.'),
(65,68,'Case-study witness protocol','Provides gate/issue/lesson/path witness criteria and coverage for the four case studies.','Keep cases as bounded snapshots, not live rerun claims.'),
(69,75,'Venue and submission artifact boundary','Records venue freshness, historical non-escalation, upload-time compliance requirements, submission-pack gate, and artifact role separation.','Rerun live checks at submission time.'),
(76,83,'Formal-source, finite-witness, and primary-supplement boundary','Covers formal-source gate instantiation, promotion obstruction, evidence-level overclaiming, finite-witness manifests, artifact-semantic boundary, and primary/supplement interface map.','Keep every load-bearing claim tied to concrete rows and paths.'),
(84,98,'Support-surface and archive-equivalence calculus','Defines exact supplemental inclusion, public branch archive-equivalence, upload/archive instantiation, digest closure, and fallback without external support.','Update manifests/digests whenever support bytes change.'),
(99,112,'Theorem-inventory ledger and extractor boundary','Makes the theorem inventory part of the submitted obligation ledger while limiting the extractor to syntactic label coverage rather than proof checking.','Rerun extractor after writing the final inventory.'),
(113,131,'Review-bundle, command-run, and post-inventory support closure','Completes review-bundle availability, case evidence closure, command-run boundary, post-inventory fixed points, replay criteria, and four-coordinate support skeleton.','Treat current realization as conditional until post-inventory reruns and final digest regeneration are complete.')]
inv={
'valid': True,
'in_scope_present':[obj(labels(a,b),loc(a,b),r,act) for a,b,_,r,act in present_specs],
'missing_in_scope_results':[
obj('review_bundle/primary_claim_inventory_freshness_2026-06-08.log digest row','review_bundle/FINAL_DIGESTS_SHA256.md:1','The command-boundary chain names the 2026-06-08 primary-claim freshness log, but the inspected digest manifest does not list it.','Regenerate FINAL_DIGESTS_SHA256.md after the final post-inventory freshness run.'),
obj('review_bundle/VENUE_BIBLIOGRAPHY_LIVE_CHECK_2026-06-08.log digest row','main.tex:8158; review_bundle/FINAL_DIGESTS_SHA256.md:1','The manuscript names the 2026-06-08 venue/bibliography freshness log, but the current digest table does not list that log or report.','Add the 2026-06-08 venue freshness files to the regenerated digest table or downgrade to the newest digest-listed check.'),
obj('review_bundle/final_digest_generation_run.log digest row','main.tex:8157; review_bundle/FINAL_DIGESTS_SHA256.md:1','The final digest-generation log is treated as a command-result coordinate but is absent from the digest table.','Use an explicit two-pass digest convention or keep this log outside the digest surface.'),
obj('post-inventory theorem_inventory digest rows','review_bundle/FINAL_DIGESTS_SHA256.md:14','Digest rows for theorem_inventory.json/md existed while the files were absent before this run, so they cannot certify the files now being written.','Rerun extractor/verifiers after accepting this inventory and regenerate inventory digest rows.')],
'weak_in_scope_core_results':[
obj('thm:publication-safety-interface','main.tex:2786','Appropriate for scope but only as a conditional finite-record invariant under record-gate soundness.','In the short version, state the hypothesis and non-claim boundary explicitly.'),
obj('thm:current-command-result-closure; thm:current-inventory-artifact-realization; cor:current-post-inventory-support-tuple-instantiation','main.tex:8893; main.tex:8955; main.tex:9001','Current-realization claims require inventory files, post-inventory reruns, and regenerated digests; before that they are conditional.','Treat as conditional until the ordered rerun sequence is logged.'),
obj('venue freshness results','main.tex:5179-main.tex:5345','Venue facts are temporally unstable and June 2026 logs become historical unless checked at actual submission time.','Rerun live venue/bibliography verification before submission.'),
obj('case snapshot coverage results','main.tex:4977-main.tex:5036','Case results prove snapshot/path coverage, not current daemon or artifact behavior.','Keep snapshot/historical wording unless fresh rerun logs are added.')],
'proof_gaps':[
obj('digest/support fixed-point ordering','main.tex:8757; review_bundle/FINAL_DIGESTS_SHA256.md:14','The post-inventory fixed-point theorems require inventory files before reruns and digest regeneration; inspected logs/digests predate the inventory files.','After writing inventory, rerun extractor, certificate verifier, source-interface verifier, primary-claim freshness check, venue check if used, then regenerate digests.'),
obj('circular digest-generation coordinate','main.tex:8157; main.tex:8770','Hashing the digest-generation log into the digest table generated by that same log needs an explicit two-pass or historical-log convention.','Specify and execute a two-pass closure rule or exclude the generator log from the digest table.'),
obj('source_commit consistency in retained logs','review_bundle/*.log','Stage A did not confirm all retained post-inventory logs share the same final source state after this inventory is written.','Rerun from the final source state or mark old logs historical.'),
obj('public-source reachability boundary','main.tex:731; references.bib:1','The public repository and pinned commit are cited, but no public fetch/byte-equality log is currently supplied.','Add a fetch/compare log for public-byte claims or keep claims candidate/path-verified.'),
obj('background citation sufficiency','references.bib:25-references.bib:54','Lean, LeanDojo, Draft--Sketch--Prove, and AFP are background citations; the set may be thin for CICM reproducibility context.','Verify venue bibliography needs and add only directly relevant background citations.')],
'supporting_appendix_or_background':[
obj('automated-discovery snapshot definitions','review_bundle/source_snapshots/automated_theory_discovery_pipeline_calculus_3fb3d6a0641767388a401883062aa522ea0b397b.tex:18-224','Prior source definitions for certified theory state, automation records, pipeline states, discovery claims, and gates support the bounded interface.','Use only via source_interface_record.json and the pinned snapshot.'),
obj('automated-discovery gate and adequacy theorems','review_bundle/source_snapshots/automated_theory_discovery_pipeline_calculus_3fb3d6a0641767388a401883062aa522ea0b397b.tex:237-465','Prior-source theorems on discovery gates, lineage, and pipeline adequacy motivate the imported source-interface axis.','Classify as supporting background, not new results of this article.'),
obj('bedc-newmath-source; automath-publication-pipeline; auditable-pipeline-review-bundle','references.bib:1; references.bib:9; references.bib:17','Local/public support references identify source and package surfaces, with explicit no-DOI/no-upload/no-fresh-command boundaries.','Keep notes explicit and conditional.'),
obj('deMouraKADR2015Lean; YangEtAl2023LeanDojo; JiangEtAl2023DraftSketchProve; BlanchetteHMN2015AFP','references.bib:25; references.bib:37; references.bib:44; references.bib:54','Classical/external background for proof assistants, AI-assisted proving, and proof archives.','Use only as contextual citations.')],
'out_of_scope_strong_results':[
obj('prior L0/L1/L2 universality hierarchy ledger','Prompt prior research ledger; not present in main.tex','Interesting but belongs to a mathematical universality paper, not this workflow/software article.','Do not import into this manuscript.',candidate_title='Single-Primitive Universality Hierarchy and Finite-Fiber Certificate Universality',source_contribution='Earlier Stage A reasoning identified L0/L1/L2 universality, Zeckendorf protocol/certificate universality, Richardson/EML conditionality, and finite-state strictness.',scope_mismatch='Mathematical universality and arithmetic/certificate results are outside the auditable publication-pipeline scope.',independent_paper_rationale='They form a coherent independent theorem chain.',needed_to_split=['separate scope contract','full proof audit','independent bibliography','no reliance on this workflow paper']),
obj('full automated-discovery pipeline calculus','review_bundle/source_snapshots/automated_theory_discovery_pipeline_calculus_3fb3d6a0641767388a401883062aa522ea0b397b.tex:18-488','The snapshot is a complete discovery-gate calculus but the current article imports only a bounded interface.','Keep as review-bundle support.',candidate_title='A Gate Calculus for Automated Theory Discovery Pipelines',source_contribution='Definitions and theorems for discovery states, transitions, gates, lineage, and adequacy.',scope_mismatch='Standalone discovery calculus is broader than publication-package audit architecture.',independent_paper_rationale='Could support a focused automated-discovery gating paper.',needed_to_split=['promote snapshot to manuscript','add related work','audit proofs independently','provide standalone examples'])],
'split_candidates':[
obj('finite-record support-coordinate fixed-point calculus','main.tex:8587-9181','The post-inventory fixed-point/replay chain is reusable but heavy for a presentation paper.','Keep only local closure requirements here; consider splitting later.',candidate_title='Finite Support-Coordinate Fixed Points for Auditable Research Packages',source_contribution='Finite-coordinate dichotomy, fixed-point normal form, replay criterion, and external-support boundary.',scope_mismatch='Presentation route mostly needs the rerun protocol and boundary.',independent_paper_rationale='Could generalize to reproducible computational packages.',needed_to_split=['abstract filenames','resolve digest circularity','give algorithms','add examples']),
obj('support-surface archive-equivalence calculus','main.tex:6311-7167','Exact inclusion, public locator criteria, upload boundaries, and digest closure form reusable archive-equivalence machinery.','Keep local criterion here; split if length pressure requires.',candidate_title='Archive-Equivalent Support Surfaces for Research Software Submissions',source_contribution='Exact supplemental inclusion, byte-equality archive criteria, upload/archive records, and no-external-instantiation lemmas.',scope_mismatch='The present article needs this only to bound its review bundle.',independent_paper_rationale='Useful as general reproducibility packaging theory.',needed_to_split=['generalize path conventions','define archive equivalence independently','add archive examples','relate to artifact evaluation policies'])],
'irrelevant_or_remove':[
obj('root-level audit scratch files','_audit_*.tmp; _codex_*.json; _stage_a_*.json','Local diagnostics are outside the selected primary/supplement/review-bundle support surface.','Do not cite or rely on them unless promoted into the manifest.'),
obj('compile logs outside selected support rows','compile_*.log','Compilation logs are local history unless explicitly included in the selected support tuple.','Either leave as local history or add load-bearing logs to the manifest/digests.'),
obj('temporary environment indexes from this review','main.tex.env_index.json; automated_theory_discovery_pipeline_calculus_*.env_index.json','Generated during Stage A inspection and not part of requested deliverables.','Ignore or remove before final packaging unless intentionally manifested.')],
'naive_truncation_risks':[
obj('finite digest rows treated as stable after edits','main.tex:7066; main.tex:8757; review_bundle/FINAL_DIGESTS_SHA256.md:14','Digest rows are byte-state coordinates, not invariants under later inventory/log edits.','Regenerate digests after all final support files exist.'),
obj('row-frozen package invariance','main.tex:4410','Row-frozen invariance holds only for the frozen row set and byte state.','Rerun finite-record checks after row or support-file changes.'),
obj('case snapshot evidence generalized to current behavior','main.tex:8023; review_bundle/case_snapshots/','Snapshots do not prove current daemon, validator, or external repository behavior.','Keep snapshot/historical wording unless fresh rerun logs are supplied.'),
obj('public branch/path locator treated as archive-equivalent without byte equality','main.tex:6349; references.bib:17','A moving branch/path does not glue to local digest rows without pinned or same-state byte equality.','Require immutable archive, pinned commit, or same-state byte-equality log.'),
obj('theorem-environment extraction treated as proof checking','main.tex:7233; main.tex:7411; review_bundle/extract_theorem_environments.py:1','The extractor verifies syntactic label coverage only, not theorem semantics.','Keep the proof-checker obstruction explicit.')],
'journal_style_gaps':[
obj('presentation length and theorem density','main.tex:174-9181','The supplement has 131 theorem-like environments, far too dense for a compact CICM presentation artifact.','Use submission_abstract.tex as primary and main.tex as technical supplement/support.'),
obj('central contribution framing','research_directive.md:8; main.tex:63','The paper must foreground theory-compiler architecture, not local rejected-paper history or general AI safety.','Lead with axes, trust boundary, deterministic gates, and four safe case lessons.'),
obj('venue and bibliography live verification','review_bundle/VENUE_BIBLIOGRAPHY_LIVE_CHECK_2026-06-08.log','Venue rules and bibliography metadata are unstable.','Rerun live checks immediately before submission and update logs/digests.'),
obj('terminology load for CICM audience','main.tex:288; main.tex:963; main.tex:1144','Terms such as record-gate soundness and support-coordinate fixed point need concise operational explanation.','Preserve a short glossary/table in the presentation artifact.'),
obj('citation style for local support surfaces','references.bib:9; references.bib:17','Local support notes may not be acceptable as ordinary citations without a supplied supplement or stable archive.','Provide exact supplement/archive locator or convert them to support-package notes per venue style.')]
}
keys=['valid','in_scope_present','missing_in_scope_results','weak_in_scope_core_results','proof_gaps','supporting_appendix_or_background','out_of_scope_strong_results','split_candidates','irrelevant_or_remove','naive_truncation_risks','journal_style_gaps']
inv={k:inv[k] for k in keys}
Path('theorem_inventory.json').write_text(json.dumps(inv,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
md=['# Theorem Inventory','','Stage A scope-bound theorem inventory for `2026_auditable_theory_to_paper_pipeline`.','']
for k in keys:
    md += [f'## {k.replace("_"," ").title()}','']
    if k=='valid': md += [f'- `{inv[k]}`','']; continue
    for row in inv[k]:
        md.append(f'- **{row["label"]}** (`{row["location"]}`): {row["reason"]} Required action: {row["required_action"]}')
        for e in ['candidate_title','source_contribution','scope_mismatch','independent_paper_rationale','needed_to_split']:
            if e in row: md.append(f'  - {e}: {"; ".join(row[e]) if isinstance(row[e],list) else row[e]}')
    md.append('')
Path('theorem_inventory.md').write_text('\n'.join(md)+'\n',encoding='utf-8')
print(len(items),'theorem-like environments covered')
print('wrote theorem_inventory.json theorem_inventory.md')
