import re, io, json, sys, time, unicodedata
import urllib.request, urllib.parse
p = r"D:\omega\automath\papers\publication\2026_single_primitive_universality_hierarchy\references.bib"
txt = io.open(p, encoding='utf-8').read()
entries = re.split(r'\n(?=@)', txt)
def field(e, name):
    m = re.search(name + r'\s*=\s*[{"](.*?)[}"]\s*,?\s*\n', e, re.S)
    if not m:
        m = re.search(name + r'\s*=\s*\{(.*?)\}\s*,?\s*\n', e, re.S)
    return re.sub(r'\s+', ' ', m.group(1)).strip() if m else None
def norm(s):
    s = unicodedata.normalize('NFKD', s or '')
    s = ''.join(c for c in s if not unicodedata.combining(c))
    return re.sub(r'[^a-z0-9 ]', ' ', s.lower())
print(f'{"key":38s} {"DOI":34s} verdict')
print('-'*110)
nchecked = nok = nbad = nnodoi = 0
rows = []
for e in entries:
    m = re.match(r'@\w+\{([^,]+),', e)
    if not m: continue
    key = m.group(1).strip()
    doi = field(e, 'doi')
    title = field(e, 'title')
    if not doi:
        nnodoi += 1
        rows.append((key, '-', 'NO DOI (title-only entry)', title))
        continue
    nchecked += 1
    url = 'https://api.crossref.org/works/' + urllib.parse.quote(doi)
    try:
        req = urllib.request.Request(url, headers={'User-Agent': 'omega-bib-check/1.0 (mailto:alyicabhz@gmail.com)'})
        with urllib.request.urlopen(req, timeout=30) as r:
            d = json.load(r)['message']
        ct = ' '.join(d.get('title') or [''])
        a = norm(title); b = norm(ct)
        aw = set(a.split()) - {'the','of','a','on','and','in','for','to'}
        bw = set(b.split()) - {'the','of','a','on','and','in','for','to'}
        ov = len(aw & bw) / max(1, len(aw))
        ok = ov >= 0.6
        nok += ok; nbad += (not ok)
        rows.append((key, doi, ('MATCH' if ok else 'MISMATCH') + f' (overlap {ov:.2f})', ct))
    except Exception as ex:
        nbad += 1
        rows.append((key, doi, 'CROSSREF ERROR: ' + str(ex)[:40], title))
    time.sleep(0.6)
for k, d, v, t in rows:
    print(f'{k:38s} {d:34s} {v}')
    print(f'{"":38s} crossref/bib title: {t[:90] if t else ""}')
print('-'*110)
print(f'RAW COUNTS  entries={len(rows)}  with DOI={nchecked}  matched={nok}  problem={nbad}  no DOI={nnodoi}')
