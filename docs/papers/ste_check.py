#!/usr/bin/env python3
"""ASD-STE100 (Simplified Technical English, Issue 8) review of a LaTeX paper.

Checks the writing rules that can be tested mechanically:
  R4/5  sentence length: procedural sentences <= 20 words, descriptive sentences <= 25 words
  R6    paragraph length: <= 6 sentences
  R3.4  no -ing forms (except technical names in the allowlist)
  R3.1  active voice (passive constructions are listed for review)
  R3.6  no contractions
  R9    no vague modal verbs (should, would, could, may, might, shall)
  R3.2  no phrasal verbs from a known list
  Dict  words that the STE dictionary does not approve, with the approved alternative.
The STE dictionary is not available here; the unapproved-word list covers commonly cited
entries only. Math, tables, Lean names, citations and references are removed before the check.
Usage: ste_check.py paper.tex
"""
import re, sys

UNAPPROVED = {
    'obtain': 'get', 'obtains': 'get', 'utilize': 'use', 'utilise': 'use', 'require': 'necessary',
    'requires': 'necessary', 'required': 'necessary', 'requirement': 'necessary',
    'need': 'necessary', 'needs': 'necessary', 'needed': 'necessary',
    'provide': 'give / supply', 'provides': 'give / supply', 'ensure': 'make sure',
    'determine': 'find', 'determines': 'find', 'indicate': 'show', 'indicates': 'show',
    'achieve': 'get', 'achieves': 'get', 'maintain': 'keep', 'maintains': 'keep',
    'exceed': 'more than', 'exceeds': 'more than', 'via': 'through / with', 'e.g.': 'for example',
    'i.e.': 'that is', 'accomplish': 'do', 'adequate': 'sufficient', 'additional': 'more',
    'adjacent': 'near', 'assist': 'help', 'attempt': 'try', 'commence': 'start',
    'demonstrate': 'show', 'demonstrates': 'show', 'eliminate': 'remove', 'employ': 'use',
    'facilitate': 'help', 'implement': 'do', 'initial': 'first', 'initiate': 'start',
    'locate': 'find', 'modify': 'change', 'perform': 'do', 'performs': 'do', 'possess': 'have',
    'proceed': 'go', 'regarding': 'about', 'remain': 'stay', 'remains': 'stay', 'retain': 'keep',
    'reveal': 'show', 'terminate': 'stop', 'therefore': 'thus', 'numerous': 'many',
    'various': 'different', 'whether': 'if', 'very': '(delete)', 'really': '(delete)',
    'significant': 'large', 'significantly': '(rewrite)', 'essentially': '(delete)',
    'basically': '(delete)', 'simply': '(delete)', 'just': '(delete)', 'quite': '(delete)',
    'rather': '(rewrite)', 'whereas': 'but', 'whilst': 'while', 'hence': 'thus',
    'allow': 'let', 'allows': 'let', 'permit': 'let', 'permits': 'let', 'absorb': 'compensate',
    'verify': 'make sure', 'verified': 'tested', 'yield': 'give', 'yields': 'give',
    'compute': 'calculate', 'computed': 'calculated', 'examine': 'do a check of',
    'feasible': 'possible', 'infeasible': 'not possible', 'leverage': 'use', 'robust': '(rewrite)',
    'crucial': 'important', 'key': 'important', 'enable': 'let', 'enables': 'let',
}
PHRASAL = ['set up', 'carry out', 'find out', 'turn on', 'turn off', 'look up', 'figure out',
           'come up', 'end up', 'point out', 'make up', 'take off', 'go on', 'build up',
           'give up', 'look into', 'put in', 'run out', 'pick up', 'slow down', 'speed up']
ING_OK = {'during', 'thing', 'things', 'wing', 'wings', 'bring', 'string', 'spring', 'ring',
          'nothing', 'something', 'anything', 'everything', 'ceiling', 'king', 'sing', 'thing',
          'bearing', 'housing', 'fixed-wing', 'coating', 'reading', 'setting', 'sling'}
MODALS = ['should', 'would', 'could', 'may', 'might', 'shall']
IRREG = ('done made given taken seen shown known found set put kept held built sent left lost '
         'got gotten told thrown driven proven proved written forced locked tilted '
         'applied measured changed tested installed attached removed used limited filtered '
         'planned recorded included checked bounded supplied caused locked fixed').split()

def table_text(tex):
    """Captions and table cells, each as its own paragraph."""
    out = []
    for tab in re.findall(r'\\begin\{table\}.*?\\end\{table\}', tex, flags=re.S):
        for cap in re.findall(r'\\caption\{((?:[^{}]|\{[^{}]*\})*)\}', tab):
            out.append(cap)
        inner = re.sub(r'\\caption\{((?:[^{}]|\{[^{}]*\})*)\}|\\label\{[^}]*\}', '', tab)
        inner = re.sub(r'\\(toprule|midrule|bottomrule|centering|small)|\\begin\{[^}]*\}(\{[^}]*\})*|\\end\{[^}]*\}', '', inner)
        for row in inner.split('\\\\'):
            for cell in row.split('&'):
                if len(re.findall(r'[A-Za-z]{3,}', cell)) >= 4:
                    out.append(cell)
    return '\n\n'.join(out)

def strip(tex):
    body = tex.split('\\begin{document}', 1)[1].split('\\end{document}', 1)[0]
    body = body + '\n\n' + table_text(body)
    body = re.sub(r'(?s)(.*)\n\n(' + re.escape(table_text(body)) + ')$', r'\1', body) if False else body
    body = re.sub(r'\\begin\{thebibliography\}.*?\\end\{thebibliography\}', '', body, flags=re.S)
    body = re.sub(r'\\begin\{(table|tabular|tabularx|equation\*?|align\*?)\}.*?\\end\{\1\}', '\n\n', body, flags=re.S)
    body = re.sub(r'\\maketitle|\\section\*?\{[^}]*\}|\\subsection\*?\{[^}]*\}|\\label\{[^}]*\}', '\n\n', body)
    body = re.sub(r'(?<!\\)%.*', '', body)
    body = re.sub(r'\\cite\{[^}]*\}', '', body)
    body = re.sub(r'\\[cC]ref\{[^}]*\}', 'Section 1', body)
    body = re.sub(r'\\eqref\{[^}]*\}', 'Equation 1', body)
    body = re.sub(r'\\lean\{[^}]*\}', 'NAME', body)
    body = re.sub(r'\\texttt\{[^}]*\}', 'NAME', body)
    body = re.sub(r'\\url\{[^}]*\}', 'URL', body)
    body = re.sub(r'\$[^$]*\$', 'X', body)
    body = re.sub(r'\\(emph|textbf|textit)\{([^}]*)\}', r'\2', body)
    body = re.sub(r'\\begin\{(abstract|itemize|enumerate|theorem|definition|proof|remark|lemma)\}(\[[^]]*\])?', '\n\n', body)
    body = re.sub(r'\\end\{[a-z]+\}', '\n\n', body)
    body = re.sub(r'\\item\s*', '\n\n', body)
    body = re.sub(r'\\[a-zA-Z]+\*?(\[[^]]*\])?', ' ', body)
    body = body.replace('~', ' ').replace('\\,', ' ').replace('{', '').replace('}', '').replace('\\', '')
    return body

def sentences(par):
    par = re.sub(r'\s+', ' ', par).strip()
    if not par: return []
    parts = re.split(r'(?<=[.!?])\s+(?=[A-Z0-9])', par)
    return [p for p in parts if re.search(r'[A-Za-z]', p)]

def words(s):
    return re.findall(r"[A-Za-z][A-Za-z'\-]*|\d+(?:\.\d+)?", s)

def is_procedural(s):
    w = words(s)
    if not w: return False
    first = w[0].lower()
    return first in {'use', 'install', 'attach', 'put', 'increase', 'decrease', 'keep', 'do',
                     'get', 'fly', 'expect', 'know', 'treat', 'measure', 'make', 'always', 'then',
                     'test', 'add', 'remove', 'set', 'read', 'see', 'apply'}

def check(path):
    text = strip(open(path).read())
    pars = [p for p in re.split(r'\n\s*\n', text) if p.strip()]
    issues = []; nsent = 0; nwords = 0
    for par in pars:
        ss = sentences(par)
        if len(ss) > 6:
            issues.append(('R6 paragraph > 6 sentences', ss[0][:70] + ' ...'))
        for s in ss:
            nsent += 1
            w = words(s); nwords += len(w)
            lim = 20 if is_procedural(s) else 25
            if len(w) > lim:
                issues.append((f'R4/5 sentence {len(w)} words > {lim}', s))
            for t in w:
                tl = t.lower()
                if tl.endswith('ing') and len(tl) > 4 and tl not in ING_OK:
                    issues.append(('R3.4 -ing form', f'"{t}" in: {s}'))
                if tl in UNAPPROVED:
                    issues.append(('Dict unapproved word', f'"{t}" -> {UNAPPROVED[tl]} in: {s}'))
                if tl in MODALS:
                    issues.append(('R9 modal verb', f'"{t}" in: {s}'))
                if re.search(r"n't|'re|'ll|'ve|'d\b", tl):
                    issues.append(('R3.6 contraction', f'"{t}" in: {s}'))
            low = ' ' + s.lower() + ' '
            for ph in PHRASAL:
                if f' {ph} ' in low:
                    issues.append(('R3.2 phrasal verb', f'"{ph}" in: {s}'))
            m = re.search(r'\b(is|are|was|were|be|been|being)\s+(\w+ly\s+)?(\w+ed|' + '|'.join(IRREG) + r')\b', s, re.I)
            if m:
                issues.append(('R3.1 passive (review)', f'"{m.group(0)}" in: {s}'))
    return issues, nsent, nwords, len(pars)

if __name__ == '__main__':
    for path in sys.argv[1:]:
        issues, ns, nw, npar = check(path)
        hard = [i for i in issues if not i[0].startswith('R3.1')]
        print(f'== {path}: {npar} paragraphs, {ns} sentences, mean {nw / max(ns, 1):.1f} words/sentence')
        print(f'   {len(hard)} rule violations, {len(issues) - len(hard)} passive constructions to review')
        for k, v in issues:
            print(f'   [{k}] {v[:220]}')
