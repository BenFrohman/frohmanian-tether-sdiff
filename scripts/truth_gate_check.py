#!/usr/bin/env python3
# Author: Benjamin Stanley Frohman
# Truth Gate static checks (see TRUTH_GATE.md). Exit code 0 only if every check passes.
#  0. A lock marked `"certifying": false` (re-audit) fails.
#  1. TRUTH_GATE.lock parses and names existing files.
#  2. Semantics.lean declares formal_claim, paper_claim, intended_correspondence (inside the lock region).
#  3. The paper file hash equals the recorded hash, and the quoted paper text occurs verbatim
#     (whitespace-normalised) in the paper file.
#  4. The sha256 of the lock region of Semantics.lean equals the recorded hash (the claim is fixed).
#  5. No sorry / admit / native_decide / `axiom` declaration in ANY tracked .lean file
#     (`git ls-files '*.lean'`, only .lake/ left out; comments and string literals are not code).
#  6. The same checks for every entry of "additional_locks" (one semantics file, several
#     formal_claim_X / paper_claim_X / intended_correspondence_X triples).
import hashlib, json, os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FAIL = []

def fail(msg):
    FAIL.append(msg)
    print("TRUTH GATE FAIL: " + msg)

def sha256_file(p):
    with open(p, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()

def norm(s):
    return re.sub(r"\s+", " ", s).strip()

def strip_comments_strings(src):
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
        if depth > 0:
            if src.startswith("/-", i): depth += 1; i += 2; continue
            if src.startswith("-/", i): depth -= 1; i += 2; continue
            i += 1; continue
        if src.startswith("/-", i): depth = 1; i += 2; continue
        if src.startswith("--", i):
            j = src.find("\n", i); i = n if j < 0 else j; continue
        if src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            out.append('""'); i = j + 1; continue
        out.append(src[i]); i += 1
    return "".join(out)

lock_path = os.path.join(ROOT, "TRUTH_GATE.lock")
if not os.path.isfile(lock_path):
    fail("TRUTH_GATE.lock missing"); sys.exit(1)
lock = json.load(open(lock_path))
for k in ["semantics_file", "semantics_module", "paper_path", "paper_sha256",
          "main_theorems", "lock_region_sha256"]:
    if k not in lock: fail(f"TRUTH_GATE.lock lacks key {k}")
for _k in ["draft" + "_dirs", "lean" + "_roots"]:
    if _k in lock:
        fail(f"TRUTH_GATE.lock carries {_k}: no directory may be exempted or left out of the scan")
if FAIL: sys.exit(1)

# 0. Re-audit status: a lock marked non-certifying keeps the gate red (see TRUTH_GATE.md).
if lock.get("certifying", True) is not True:
    fail("this lock is NOT certifying (reopened by the re-audit of 2026-11-16): "
         + str(lock.get("reopened_reason", "see TRUTH_GATE.md")))

sem = os.path.join(ROOT, lock["semantics_file"])
if not os.path.isfile(sem):
    fail(f"{lock['semantics_file']} missing"); sys.exit(1)
src = open(sem, encoding="utf-8").read()

# 2. lock region and required declarations
m = re.search(r"^-- TRUTH-GATE LOCK BEGIN\n(.*?)^-- TRUTH-GATE LOCK END\n", src, re.S | re.M)
if not m:
    fail("lock region markers missing in Semantics.lean")
else:
    region = m.group(1)
    for decl in [r"def\s+formal_claim\s*:\s*Prop", r"def\s+paper_claim\s*:\s*Prop",
                 r"theorem\s+intended_correspondence\s*:\s*formal_claim\s*↔\s*paper_claim"]:
        if not re.search(decl, strip_comments_strings(region)):
            fail(f"lock region lacks `{decl}`")
    code_region = strip_comments_strings(region)
    # 2b. paper_claim must not mention formal_claim (no aliasing).
    pm = re.search(r"def\s+paper_claim\s*:\s*Prop\s*:=(.*?)(?=^\s*(?:/--|theorem|def|lemma)\b|\Z)", code_region, re.S | re.M)
    if not pm:
        fail("cannot parse the body of paper_claim")
    elif re.search(r"(?<![\w.'])(TruthGate\.)?formal_claim(?![\w'])", pm.group(1)):
        fail("paper_claim's definition mentions formal_claim (vacuous alias)")
    # 2c. intended_correspondence must have a substantive proof, not rfl / Iff.rfl.
    cm = re.search(r"theorem\s+intended_correspondence\s*:\s*formal_claim\s*↔\s*paper_claim\s*:=(.*)", code_region, re.S)
    if cm:
        body = re.sub(r"\s+", " ", cm.group(1)).strip()
        trivial = {"Iff.rfl", "rfl", "by rfl", "by exact Iff.rfl", "by exact rfl", "by apply Iff.rfl",
                   "by constructor <;> exact id", "⟨id, id⟩", "Iff.intro id id", "by exact ⟨id, id⟩",
                   "by simp", "by simp only [formal_claim, paper_claim]", "by unfold formal_claim paper_claim; rfl",
                   "by unfold formal_claim paper_claim; exact Iff.rfl", "by decide", "by trivial", "by tauto"}
        if body in trivial or re.fullmatch(r"(by\s+)?(exact\s+)?(Iff\.)?rfl", body):
            fail(f"intended_correspondence is proved trivially (`{body}`); a substantive proof is required")
        if re.search(r"(?<![\w.'])(Iff\.rfl|rfl)(?![\w'])", body) and len(body) < 40:
            fail(f"intended_correspondence proof `{body}` is (essentially) rfl")
    got = hashlib.sha256(region.encode("utf-8")).hexdigest()
    if got != lock["lock_region_sha256"]:
        fail(f"lock region sha256 {got} != locked {lock['lock_region_sha256']} "
             "(the locked claim was edited; changing it needs the owner's explicit sign-off and a new lock)")

# 3. paper hash and verbatim quote
pp = os.path.join(ROOT, lock["paper_path"])
if not os.path.isfile(pp):
    fail(f"paper file {lock['paper_path']} missing")
else:
    h = sha256_file(pp)
    if h != lock["paper_sha256"]:
        fail(f"paper sha256 {h} != locked {lock['paper_sha256']}")
    if f"PAPER_SHA256: {lock['paper_sha256']}" not in src:
        fail("Semantics.lean docstring does not record the locked PAPER_SHA256")
    if f"PAPER_PATH: {lock['paper_path']}" not in src:
        fail("Semantics.lean docstring does not record PAPER_PATH")
    if not re.search(r"^PAPER_SECTION: \S", src, re.M):
        fail("Semantics.lean docstring lacks a PAPER_SECTION: field")
    tg = open(os.path.join(ROOT, "TRUTH_GATE.md"), encoding="utf-8").read() if os.path.isfile(os.path.join(ROOT, "TRUTH_GATE.md")) else ""
    if not tg:
        fail("TRUTH_GATE.md missing")
    elif lock["paper_sha256"] not in tg or lock["paper_path"] not in tg:
        fail("TRUTH_GATE.md does not record the locked paper path and sha256")
    quotes = re.findall(r"PAPER_QUOTE_BEGIN\n(.*?)\nPAPER_QUOTE_END", src, re.S)
    if not quotes:
        fail("no PAPER_QUOTE_BEGIN/END block in Semantics.lean")
    paper = norm(open(pp, encoding="utf-8", errors="replace").read())
    for q in quotes:
        if norm(q) not in paper:
            fail("quoted paper text not found verbatim in the paper file: " + norm(q)[:120])
        if tg and norm(q) not in norm(tg):
            fail("TRUTH_GATE.md does not carry the verbatim paper quote")

# 6. Additional locks (TRUTH_GATE.lock "additional_locks"): the same rules for every
#    (formal_claim_X, paper_claim_X, intended_correspondence_X) triple of another semantics file.
TRIVIAL = {"Iff.rfl", "rfl", "by rfl", "by exact Iff.rfl", "by exact rfl", "by apply Iff.rfl",
           "by constructor <;> exact id", "⟨id, id⟩", "Iff.intro id id", "by exact ⟨id, id⟩",
           "by simp", "by decide", "by trivial", "by tauto"}
extra_roots = []
for ex in lock.get("additional_locks", []):
    tag = ex.get("name", ex.get("semantics_file", "?"))
    for k in ["semantics_file", "semantics_module", "paper_path", "paper_sha256", "claims",
              "main_theorems", "lock_region_sha256", "audit_file"]:
        if k not in ex: fail(f"additional lock {tag} lacks key {k}")
    if any(k not in ex for k in ["semantics_file", "paper_path", "paper_sha256", "claims", "lock_region_sha256"]):
        continue
    if ex.get("certifying", True) is not True:
        fail(f"additional lock {tag} is NOT certifying: " + str(ex.get("reopened_reason", "")))
    xsem = os.path.join(ROOT, ex["semantics_file"])
    if not os.path.isfile(xsem):
        fail(f"{ex['semantics_file']} missing"); continue
    extra_roots.append(ex["semantics_file"])
    xsrc = open(xsem, encoding="utf-8").read()
    xm = re.search(r"^-- TRUTH-GATE LOCK BEGIN\n(.*?)^-- TRUTH-GATE LOCK END\n", xsrc, re.S | re.M)
    if not xm:
        fail(f"lock region markers missing in {ex['semantics_file']}"); continue
    xregion = xm.group(1)
    xcode = strip_comments_strings(xregion)
    for cid in ex["claims"]:
        for decl in [rf"def\s+formal_claim_{cid}\s*:\s*Prop", rf"def\s+paper_claim_{cid}\s*:\s*Prop",
                     rf"theorem\s+intended_correspondence_{cid}\s*:\s*formal_claim_{cid}\s*↔\s*paper_claim_{cid}\s*:="]:
            if not re.search(decl, xcode):
                fail(f"{tag}: lock region lacks `{decl}`")
        cm = re.search(rf"theorem\s+intended_correspondence_{cid}\s*:\s*formal_claim_{cid}\s*↔\s*paper_claim_{cid}\s*:=(.*?)(?=^(?:theorem|def|lemma)\b|\Z)", xcode, re.S | re.M)
        if cm:
            body = re.sub(r"\s+", " ", cm.group(1)).strip()
            if body in TRIVIAL or re.fullmatch(r"(by\s+)?(exact\s+)?(Iff\.)?rfl", body) or \
               (re.search(r"(?<![\w.'])(Iff\.rfl|rfl)(?![\w'])", body) and len(body) < 40):
                fail(f"{tag}: intended_correspondence_{cid} is proved trivially (`{body}`)")
    # every paper-side definition (paper_*) must not mention any formal_claim or a forbidden repository Prop
    forbidden = ex.get("paper_forbidden_names", [])
    for pm in re.finditer(r"^def\s+(paper_\w+)\b(.*?)(?=^(?:theorem|def|lemma|abbrev)\b|\Z)", xcode, re.S | re.M):
        pbody = pm.group(2)
        if re.search(r"(?<![\w.'])([\w.]*\.)?formal_claim\w*(?![\w'])", pbody):
            fail(f"{tag}: {pm.group(1)} mentions a formal_claim (vacuous alias)")
        for fn in forbidden:
            if re.search(rf"(?<![\w'])([\w]+\.)*{re.escape(fn)}(?![\w'])", pbody):
                fail(f"{tag}: {pm.group(1)} names the repository Prop {fn} instead of transcribing the paper")
    got = hashlib.sha256(xregion.encode("utf-8")).hexdigest()
    if got != ex["lock_region_sha256"]:
        fail(f"{tag}: lock region sha256 {got} != locked {ex['lock_region_sha256']} "
             "(the locked claims were edited; a new lock needs the owner's explicit sign-off)")
    xpp = os.path.join(ROOT, ex["paper_path"])
    if not os.path.isfile(xpp):
        fail(f"{tag}: paper file {ex['paper_path']} missing"); continue
    xh = sha256_file(xpp)
    if xh != ex["paper_sha256"]:
        fail(f"{tag}: paper sha256 {xh} != locked {ex['paper_sha256']}")
    if f"PAPER_SHA256: {ex['paper_sha256']}" not in xsrc:
        fail(f"{tag}: {ex['semantics_file']} does not record the locked PAPER_SHA256")
    if f"PAPER_PATH: {ex['paper_path']}" not in xsrc:
        fail(f"{tag}: {ex['semantics_file']} does not record PAPER_PATH")
    if not re.search(r"^PAPER_SECTION: \S", xsrc, re.M):
        fail(f"{tag}: {ex['semantics_file']} lacks a PAPER_SECTION: field")
    tg = open(os.path.join(ROOT, "TRUTH_GATE.md"), encoding="utf-8").read() if os.path.isfile(os.path.join(ROOT, "TRUTH_GATE.md")) else ""
    if ex["paper_sha256"] not in tg or ex["paper_path"] not in tg:
        fail(f"{tag}: TRUTH_GATE.md does not record the locked paper path and sha256")
    xquotes = re.findall(r"PAPER_QUOTE_BEGIN\n(.*?)\nPAPER_QUOTE_END", xsrc, re.S)
    if not xquotes:
        fail(f"{tag}: no PAPER_QUOTE_BEGIN/END block")
    xpaper = norm(open(xpp, encoding="utf-8", errors="replace").read())
    for q in xquotes:
        if norm(q) not in xpaper:
            fail(f"{tag}: quoted paper text not found verbatim in the paper file: " + norm(q)[:120])
        if tg and norm(q) not in norm(tg):
            fail(f"{tag}: TRUTH_GATE.md does not carry the verbatim paper quote: " + norm(q)[:80])
    print(f"TRUTH GATE STATIC: additional lock {tag}: claims {ex['claims']} checked")

# 5. forbidden tokens in every tracked .lean file (no directory is exempt)
import subprocess
tok = re.compile(r"(?<![\w.'])(sorry|admit|native_decide)(?![\w'])|^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|public\s+|noncomputable\s+)*axiom\s", re.M)
files = [f for f in subprocess.check_output(["git", "ls-files", "*.lean"], cwd=ROOT).decode().splitlines()
         if f and not f.startswith(".lake/") and "/.lake/" not in f]
if not files:
    fail("git ls-files '*.lean' returned no files")
bad = 0
for rel in files:
    code = strip_comments_strings(open(os.path.join(ROOT, rel), encoding="utf-8").read())
    for mm in tok.finditer(code):
        line = code.count("\n", 0, mm.start()) + 1
        fail(f"forbidden token `{(mm.group(1) or 'axiom')}` at {rel}:{line}"); bad += 1
print(f"TRUTH GATE STATIC: scanned all {len(files)} tracked .lean files (git ls-files); {bad} forbidden tokens")

if FAIL:
    print(f"TRUTH GATE STATIC FAIL ({len(FAIL)} problems)"); sys.exit(1)
print("TRUTH GATE STATIC PASS")
