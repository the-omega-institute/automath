import json,re,pathlib
files=[pathlib.Path('main.tex')]+sorted(pathlib.Path('source').glob('*.tex'))
envs='theorem|lemma|proposition|corollary|definition|example|remark|conclusion'
rows=[]
for p in files:
    ls=p.read_text(encoding='utf-8').splitlines()
    for i,l in enumerate(ls,1):
        m=re.search(r'\\begin\{('+envs+r')\}(?:\[([^\]]*)\])?',l)
        if not m: continue
        end=i
        for j in range(i,len(ls)+1):
            if re.search(r'\\end\{'+m.group(1)+r'\}',ls[j-1]): end=j; break
        block='\n'.join(ls[i-1:end])
        lab=re.search(r'\\label\{([^}]*)\}',block)
        rows.append({'file':str(p).replace('\\','/'),'line':i,'env':m.group(1),'title':m.group(2) or m.group(1).title(),'ref':lab.group(1) if lab else ''})

def obj(label,loc,reason,action):
    return {'label':label,'location':loc,'reason':reason,'required_action':action}

def rowobj(r,reason,action):
    return obj(f"{r['env'].title()}: {r['title']}",f"{r['file']}:{r['line']}",reason,action)

support_refs={
 'prop:joukowsky-boundary-compatibility','prop:short-elliptic-speed-spectrum','def:coprime-squarefree-codebook',
 'prop:short-capacity-prime-register-dictionary','prop:short-primorial-capacity-minimization',
 'cor:elliptic-two-scale-mahler-multiplicative','rem:leyang-linear-log-response'
}
weak_refs={'thm:finite-degree-rational-image-capacity','prop:endpoint-input-synthesis','thm:boundary-scale-rigidity','cor:capacity-mahler-fiber-classification'}

in_scope=[]; support=[]
for r in rows:
    if r['ref'] in support_refs:
        support.append(rowobj(r,'Supporting/background or appendix material rather than the article spine.','Keep secondary with citations and clear dependency on the main Joukowsky package.'))
    else:
        reason='In-scope theorem-interface present in the manuscript and used by the capacity/equilibrium/Blaschke/Mahler/inverse chain.'
        action='Keep and ensure proof dependencies remain explicit.'
        if r['ref']=='thm:pullback-factorization': reason='Scope-contract must-prove algebraic pullback identity for Q_r(J_r).'; action='Keep as a central theorem.'
        if r['ref']=='thm:discriminant-factorization': reason='Scope-contract must-prove discriminant factorization for transported roots.'; action='Keep as a central theorem.'
        if r['ref']=='thm:sharp-joukowsky-equilibrium-stability': reason='Main analytic theorem: exact Fourier deficit, sharp constants, extremizers, equilibrium, and capacity.'; action='Keep as headline CVEE theorem.'
        if r['ref']=='thm:finite-blaschke-joukowsky-cover': reason='Required Blaschke-cover theorem: deficit factors through B_*mu and classifies equilibrium lifts.'; action='Keep as core theorem.'
        if r['ref']=='prop:canonical-blaschke-lift-source-energy': reason='Required canonical lift energy product formula with monomial equality case.'; action='Keep next to Blaschke-cover theorem.'
        if r['ref']=='thm:algebraic-mahler-transport-inverse-package': reason='Required inverse package: multiscale reconstruction, one-scale resonance fibers, and unit-circle injectivity.'; action='Keep as central inverse theorem.'
        if r['ref']=='thm:quantitative-annular-rouche-stability': reason='Required quantitative Rouché stability theorem for canonical annular recovery.'; action='Keep as final inverse-stability theorem.'
        if r['ref']=='thm:finite-degree-rational-image-capacity': action='Keep but add a formal proof; also recorded under proof_gaps.'
        in_scope.append(rowobj(r,reason,action))

manual_support=[
 obj('Classical logarithmic capacity/equilibrium/Jensen/Mahler/Fekete/Blaschke facts','main.tex:63, references.bib:1','Classical background separated from the claimed new transport package.','Cite as tools; do not present as new results.'),
]
support=manual_support+support

inv={
 'valid':True,
 'in_scope_present':in_scope,
 'missing_in_scope_results':[],
 'weak_in_scope_core_results':[
   obj('Finite-degree rational-image capacity formula is under-proved','source/thm__group-jg-rational-capacity-equilibrium-blaschke.tex:89','Statement is broad and central enough for CVEE support, but no proof environment follows it.','Add a proof using nonpolarity, Borel selection, lower-truncated pullback equality, and equilibrium uniqueness.'),
   obj('Endpoint quotient synthesis is less central than analytic spine','main.tex:313, main.tex:370, main.tex:474','Useful synthesis, but weaker for the journal target than capacity/Fourier/Blaschke/Mahler/Rouché results.','Keep after the core package and present as consequence, not headline.')
 ],
 'proof_gaps':[
   obj('No proof after finite-degree rational-image capacity theorem','source/thm__group-jg-rational-capacity-equilibrium-blaschke.tex:89','The theorem states supremum equality, maximizer existence, and lift characterization, then moves directly to a new lemma.','Insert a formal proof before Lemma lem:rational-local-collision-skeleton.'),
   obj('Classical exterior-capacity and harmonic-measure facts need exact citation','source/thm__group-jg-rational-capacity-equilibrium-blaschke.tex:361','cap(E_r)=r and equilibrium as harmonic measure are standard but should be tied to a precise source.','Add a citation or preliminary fact for Green-function normalization and harmonic-measure equilibrium.'),
   obj('Finite Blaschke boundary-covering interface needs citation','source/thm__group-jg-rational-capacity-equilibrium-blaschke.tex:471','The boundary covering formula is proved, but standard Blaschke boundary facts should be cited for journal style.','Add Duren or equivalent citation at the lemma/proof.'),
   obj('Exact inverse data versus perturbed reconstruction interface','source/cor__group-jg-leyang-one-scale-resultant-reconstruction.tex:54','Exact one-scale recognition can be mistaken for numerical stability before the Rouché theorem.','Cross-reference the quantitative annular Rouché theorem when exact inverse data are introduced.')
 ],
 'supporting_appendix_or_background':support,
 'out_of_scope_strong_results':[
   {**obj('Unused elliptic-gate prime-spectrum rigidity package','split_paper_workspace/source_unused/thm__group-jg-elliptic-gate-prime-spectrum-rigidity.tex:4','Strong p-adic/Fourier rigidity package externalized from this CVEE spine.','Do not reinsert into main.tex; preserve for split-paper pipeline.'),'candidate_title':'Fourier-Support and p-Adic Rigidity of Elliptic Joukowsky Coverings','source_contribution':'Stage A discovered calibrated speed spectra, gauge control, p-adic rigidity, outer-function rigidity, register sets, valuation classification, and finite-window obstruction.','scope_mismatch':'It studies arithmetic recovery from parametrized speed profiles, not the present rational-capacity/Mahler transport spine.','independent_paper_rationale':'It has independent definitions, rigidity theorems, classification, and obstruction results.','needed_to_split':['Define gauges independently','Separate parametrized from unparametrized invariants','Develop p-adic examples','Feature finite-window obstruction']},
   {**obj('Unused Godel-Lorentz/Cayley/primorial ellipsoid package','split_paper_workspace/source_unused/thm__group-jg-godel-lorentz-cayley-primorial-capacity-ellipsoid.tex:11','Full Lorentz/prime-register package is stronger than the short optional appendix needed here.','Keep out of the main body; preserve as split-paper material.'),'candidate_title':'Capacity-Scaled Lorentz Representations and Primorial Extremality for Prime Registers','source_contribution':'Stage A discovered Lorentz representation, rigidity, condition-number identities, Einstein addition, primorial bounds, capacity-modulus links, ellipsoid-volume characters, and extremality.','scope_mismatch':'Mainly arithmetic/hyperbolic-matrix/coding material; it distracts from CVEE complex-variable scope.','independent_paper_rationale':'It forms a coherent standalone chain around prime registers and SO^+(1,1) rigidity.','needed_to_split':['State prime-register monoid as primary','Prove Lorentz rigidity','Separate volume/capacity characters','Add coprimality examples']}
 ],
 'split_candidates':[
   {**obj('Endpoint boundary-scale quotient classification','main.tex:313, main.tex:370, main.tex:453, main.tex:474','Currently in-scope as synthesis, but could grow into a separate quotient/fiber classification paper.','Keep compact here; split only if expanded beyond existing inputs.'),'candidate_title':'Boundary-Scale Quotients and Exact Fibers for Joukowsky Capacity--Mahler Data','source_contribution':'Stage A assembled endpoint inputs, realizable data, two-gate obstruction, and quotient fiber classification.','scope_mismatch':'A large classification treatment would shift emphasis away from rational capacity and Mahler transport.','independent_paper_rationale':'The quotient data and obstruction alternatives can support examples and a moduli-style treatment.','needed_to_split':['Develop quotient-data category','Add examples/counterexamples','Prove functoriality','Separate Blaschke and Mahler ambiguities']},
   {**obj('General finite-degree rational-image capacity calculus','source/thm__group-jg-rational-capacity-equilibrium-blaschke.tex:89','General theorem is used here only to support degree-two Joukowsky capacity.','Keep only needed proof here; split if higher-degree branch geometry is developed.'),'candidate_title':'Finite-Degree Rational Images and Pullback Kernels for Logarithmic Capacity','source_contribution':'Stage A introduced divided-difference kernel, lift variational formula, maximizer classification, and collision skeleton.','scope_mismatch':'Full finite-degree theory exceeds the degree-two Joukowsky focus.','independent_paper_rationale':'Arbitrary rational maps and branch graphs could support a separate potential-theory paper.','needed_to_split':['Add complete proof','Develop non-Joukowsky examples','Systematize branch graphs','Compare literature']}
 ],
 'irrelevant_or_remove':[
   obj('Over-expanded arithmetic-register headline route','split_paper_workspace/source_unused:1','Reintroducing the unused p-adic/Lorentz material would recreate the rejected mixed-scope manuscript.','Keep out of the main body; retain only short optional appendices or remove.'),
   obj('Endpoint synthesis as replacement headline','main.tex:78, main.tex:474','Endpoint data are consequences and should not obscure the capacity/Fourier/Blaschke/Mahler/Rouché spine.','Do not promote endpoint quotient data in title or abstract.')
 ],
 'naive_truncation_risks':[
   obj('Lower-truncated energy across collision graphs','source/thm__group-jg-rational-capacity-equilibrium-blaschke.tex:11','Collision pullbacks can be -infinity unless finite-energy lift admissibility and lower-truncated descent are enforced.','Keep admissibility and prove the variational theorem through lower-truncated pushforward equality.'),
   obj('Fourier deficit for arbitrary measures','source/thm__group-jg-rational-capacity-equilibrium-blaschke.tex:305','Exact coefficient summation needs finite logarithmic energy; arbitrary measures only get extended-energy bounds.','Maintain finite-energy hypotheses and route arbitrary measures through the extended proposition.'),
   obj('Finite scale budgets as global invariants','source/cor__group-jg-leyang-one-scale-resultant-reconstruction.tex:317','n+1 scales are a uniform sufficient Laurent budget; one-scale injectivity needs Lee--Yang shell separation.','Keep coefficient-budget corollary and unit-circle hypotheses visible.'),
   obj('Exact one-scale recovery treated as stable without Rouché descent','source/cor__group-jg-leyang-one-scale-resultant-reconstruction.tex:330','Exact shell selection is not perturbatively stable without contour separation and explicit envelopes.','Cross-reference quantitative annular Rouché stability.'),
   obj('Parametrized speed spectrum as unparametrized invariant','main.tex:656','Fourier coefficients and p-adic slopes depend on calibrated parametrized-cover gauge.','Keep gauge language and appendix status; do not promote finite-window recovery as an ellipse invariant.')
 ],
 'journal_style_gaps':[
   obj('Missing visible MSC and keywords','main.tex:45','Front matter lacks standard classification/keyword metadata for journal submission.','Add MSC 2020 and keywords.'),
   obj('Dense theorem chain','main.tex:287, main.tex:294, main.tex:301','Many theorem-like statements appear in rapid succession.','Add dependency map and demote only genuinely supporting labels.'),
   obj('Citation granularity','references.bib:1','Classical facts are cited broadly but some proof points need exact citations.','Tighten citations at capacity, Blaschke, Mahler/Jensen, and resultant uses.'),
   obj('Overfull boxes in latest build','main.log:620','Build log reports several overfull hboxes in headings/formulas.','Break long headings/formulas after proof gaps are fixed.'),
   obj('Appendix arithmetic vocabulary may distract CVEE readers','main.tex:650, main.tex:703','p-adic and prime-register appendices are secondary but visibly off-spine.','Keep short, explicitly tied to Joukowsky capacity scale, and removable.')
 ]
}
pathlib.Path('theorem_inventory.json').write_text(json.dumps(inv,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
md=['# Theorem Inventory','','Stage A scope-bound inventory for the CVEE-routed Joukowsky capacity/Mahler manuscript.','']
for k,v in inv.items():
    if k=='valid': continue
    md += ['## '+k.replace('_',' ').title(),'']
    if not v: md += ['- None.','']; continue
    for it in v:
        md.append(f"- **{it['label']}** (`{it['location']}`): {it['reason']} Required action: {it['required_action']}")
        if k in ('out_of_scope_strong_results','split_candidates'):
            for e in ['candidate_title','source_contribution','scope_mismatch','independent_paper_rationale']:
                if e in it: md.append(f"  - {e.replace('_',' ').title()}: {it[e]}")
            if 'needed_to_split' in it: md.append('  - Needed to split: '+'; '.join(it['needed_to_split']))
    md.append('')
pathlib.Path('theorem_inventory.md').write_text('\n'.join(md)+'\n',encoding='utf-8')
print(json.dumps(inv,indent=2,ensure_ascii=False))
