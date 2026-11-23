#!/usr/bin/env bash
# Build the PDF with pandoc and XeLaTeX, retaining the bibliographic fields in the PDF.
# Ghostscript is not used: it drops the text mapping, so words and symbols could not be copied out of the PDF.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/.." && pwd)"
cd "$root"
md=paper/crossley-criteria-riemann-hypothesis.md
# Convert GitHub math delimiters to pandoc syntax in the temporary input.
pandoc_md="$(mktemp)".md
python3 -I - "$md" "$pandoc_md" <<'PY'
import re, sys
src, out = sys.argv[1:3]
lines = open(src, encoding="utf-8").read().split("\n")
res, fence, i = [], None, 0
while i < len(lines):
    line = lines[i]
    s = line.strip()
    if fence is None and s == "```math":
        indent = line[: len(line) - len(line.lstrip())]
        j = i + 1
        while j < len(lines) and lines[j].strip() != "```":
            j += 1
        assert j < len(lines), f"unclosed math block at line {i + 1}"
        body = lines[i + 1 : j]
        if len(body) == 1:
            res.append(f"{indent}$$ {body[0].strip()} $$")
        else:
            res += [indent + "$$"] + body + [indent + "$$"]
        i = j + 1
        continue
    if s.startswith("```"):
        fence = None if fence else s
    elif fence is None:
        line = re.sub(r"\$`(.*?)`\$", lambda m: "$" + m.group(1) + "$", line)
        if " ... " in line:
            line = line.replace(" ... ", r" \.\.\. ")
    res.append(line)
    i += 1
open(out, "w", encoding="utf-8").write("\n".join(res))
PY
md="$pandoc_md"
out=paper/crossley-criteria-riemann-hypothesis.pdf
tmp="$(mktemp)".pdf
trap 'rm -f "$tmp" "$pandoc_md"' EXIT
SOURCE_DATE_EPOCH=0 pandoc "$md" --pdf-engine=xelatex --lua-filter=paper/layout.lua -H paper/header.tex \
  -V colorlinks=true -V linkcolor=black -V urlcolor=blue \
  --resource-path=.:paper --pdf-engine-opt='-output-driver=xdvipdfmx -V 4' -o "$tmp"
cp "$tmp" "$out"
python3 -I - "$out" <<'SCRUB'
import re, sys
path = sys.argv[1]
data = open(path, "rb").read()
# Same-length replacements keep every cross-reference offset valid.
blank = lambda m: b" " * len(m.group(0))  # drop the key and its value
data = re.sub(rb"(/(?:Producer|Creator|CreationDate|ModDate)\s*)\((?:[^()\\]|\\.)*\)", blank, data)
data = re.sub(rb"/ID\s*\[\s*<[0-9A-Fa-f]*>\s*<[0-9A-Fa-f]*>\s*\]", lambda m: re.sub(rb"[0-9A-Fa-f]", b"0", m.group(0)), data)
if b"/ObjStm" in data:
    sys.exit("object streams present: metadata may be compressed")
for bad in (b"xdvipdfmx", b"XeTeX", b"xmpmeta", b"/Metadata", b"D:19", b"D:20"):
    if bad in data:
        sys.exit(f"metadata left in {path}: {bad.decode()}")
open(path, "wb").write(data)
SCRUB
left="$(exiftool -s -s -s -Creator -Producer -CreateDate -ModifyDate -XMP:all "$out" | tr -d '[:space:]')"
[[ -z "$left" ]] || { echo "metadata left in $out: $left" >&2; exit 1; }
for field in Title Author Subject Keywords; do
  [[ -n "$(exiftool -s3 "-$field" "$out")" ]] || { echo "missing PDF $field" >&2; exit 1; }
done
echo "built $out ($(pdfinfo "$out" 2>/dev/null | awk '/Pages/{print $2}') pp)"
