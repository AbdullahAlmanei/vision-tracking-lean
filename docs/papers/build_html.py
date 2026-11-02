#!/usr/bin/env python3
"""Render the paper drafts (Markdown, the source of truth) to standalone HTML pages."""
import re, sys, markdown, pathlib

TEMPLATE = """<title>{title}</title>
<meta name="claude:viewport-fit-sides" content="cover">
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Archivo:wght@500;700;800&family=Source+Serif+4:ital,opsz,wght@0,8..60,400;0,8..60,600;1,8..60,400&family=JetBrains+Mono:wght@400;600&display=swap">
<style>
/* Layout: a single technical-report column, tables and code break out wider on desktop. */
:root {{
  --paper: #f5f6f3; --ink: #1a2126; --muted: #5a656c; --rule: #d5d9d4;
  --accent: #b4461b; --panel: #eaece7; --code: #e6e9e3;
  --display: "Archivo", "Helvetica Neue", Arial, sans-serif;
  --body: "Source Serif 4", Georgia, "Times New Roman", serif;
  --mono: "JetBrains Mono", ui-monospace, Menlo, Consolas, monospace;
}}
@media (prefers-color-scheme: dark) {{ :root:not([data-theme="light"]) {{
  --paper: #121619; --ink: #e3e7e4; --muted: #9aa5a9; --rule: #2c3438;
  --accent: #f0875a; --panel: #1b2125; --code: #1f272b; color-scheme: dark }} }}
:root[data-theme="dark"] {{
  --paper: #121619; --ink: #e3e7e4; --muted: #9aa5a9; --rule: #2c3438;
  --accent: #f0875a; --panel: #1b2125; --code: #1f272b; color-scheme: dark }}
body {{ background: var(--paper); color: var(--ink); font: 17px/1.62 var(--body);
  padding-left: max(16px, env(safe-area-inset-left, 0px));
  padding-right: max(16px, env(safe-area-inset-right, 0px)); padding-block: 40px 80px; }}
main {{ max-width: 46rem; margin: 0 auto; }}
.kicker {{ font: 700 0.72rem/1 var(--display); letter-spacing: 0.14em; text-transform: uppercase;
  color: var(--accent); margin: 0 0 14px; }}
h1 {{ font: 800 clamp(2rem, 6vw, 3.1rem)/1.05 var(--display); letter-spacing: -0.02em;
  text-wrap: balance; margin: 0 0 12px; }}
h1 + p {{ font: 500 1.15rem/1.4 var(--display); color: var(--muted); margin-top: 0; }}
h2 {{ font: 700 1.45rem/1.2 var(--display); margin: 2.6em 0 0.6em; padding-top: 0.8em;
  border-top: 2px solid var(--ink); text-wrap: balance; }}
h3 {{ font: 700 1.08rem/1.3 var(--display); margin: 1.8em 0 0.4em; }}
p, li {{ max-width: 68ch; }}
a {{ color: var(--accent); }}
strong {{ font-weight: 600; }}
hr {{ border: 0; border-top: 1px solid var(--rule); margin: 2.4em 0; }}
code {{ font: 0.84em var(--mono); background: var(--code); padding: 0.08em 0.32em; border-radius: 3px; }}
blockquote {{ margin: 1.4em 0; padding: 0.2em 1.1em; border-left: 3px solid var(--accent);
  background: var(--panel); }}
.tbl {{ overflow-x: auto; margin: 1.2em 0 1.6em; }}
table {{ border-collapse: collapse; font: 0.86rem/1.4 var(--display); font-variant-numeric: tabular-nums;
  min-width: 100%; }}
th {{ text-align: left; font-weight: 700; border-bottom: 2px solid var(--ink); padding: 7px 10px 6px 0; }}
td {{ border-bottom: 1px solid var(--rule); padding: 7px 10px 7px 0; vertical-align: top; }}
td code {{ font-size: 0.8rem; }}
em:first-child:last-child {{ color: var(--muted); }}
@media (min-width: 900px) {{ .tbl {{ margin-left: -3rem; margin-right: -3rem; }} }}
</style>
<main>
<p class="kicker">{kicker}</p>
{body}
</main>
"""

def build(src, kicker):
    text = pathlib.Path(src).read_text()
    title = re.search(r"^# (.+)$", text, re.M).group(1).strip()
    html = markdown.markdown(text, extensions=["tables", "sane_lists"])
    html = html.replace("<table>", '<div class="tbl"><table>').replace("</table>", "</table></div>")
    out = pathlib.Path(src).with_suffix(".html")
    out.write_text(TEMPLATE.format(title=title, kicker=kicker, body=html))
    return out

if __name__ == "__main__":
    d = pathlib.Path(__file__).parent
    print(build(d / "paper1-engineering-guide.md", "Engineering guide · Vision tracking"))
    print(build(d / "paper2-certified-pursuit.md", "Formal methods · Vision tracking"))
