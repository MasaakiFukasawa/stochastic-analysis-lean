#!/usr/bin/env python3
"""Validate the release sources, build with Lake, then audit theorem axioms.
Run from any directory. --check-only checks packaging, not Lean proofs.
"""
from pathlib import Path
import argparse, hashlib, json, os, re, subprocess, sys, time

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def code_only(source):
    out = []; i = 0; depth = 0
    while i < len(source):
        if source[i:i+2] == '/-': depth += 1; i += 2
        elif depth and source[i:i+2] == '-/': depth -= 1; i += 2
        elif depth:
            if source[i] == '\n': out.append('\n')
            i += 1
        elif source[i:i+2] == '--':
            end = source.find('\n', i); i = len(source) if end < 0 else end
        else: out.append(source[i]); i += 1
    return ''.join(out)


def check_sources(snapshot):
    errors = []; names = set(snapshot['modules']); external = set()
    # Public metadata must identify proofs without redistributing manuscript text.
    def check_metadata(value, filename):
        if isinstance(value, dict):
            for key, item in value.items():
                if key in {'statement', 'following_prose', 'proof', 'source_text', 'manuscript_text', 'tex_source'} and isinstance(item, str):
                    errors.append('Manuscript text field in public metadata: ' + str(filename) + ':' + key)
                check_metadata(item, filename)
        elif isinstance(value, list):
            for item in value: check_metadata(item, filename)
        elif isinstance(value, str) and '\\begin{' in value:
            errors.append('TeX manuscript environment in public metadata: ' + str(filename))
    for filename in (ROOT/'audit').rglob('*.json'):
        check_metadata(json.loads(filename.read_text()), filename.relative_to(ROOT))

    roots = set((ROOT/'audit/module-roots.txt').read_text().splitlines())
    if roots != names | {'Book'}: errors.append('Lake module roots differ from the release inventory')
    actual = {p.stem for p in (ROOT/'src').glob('*.lean')} - {'Book'}
    if actual != names: errors.append('Source directory differs from the release inventory')
    for name, record in snapshot['modules'].items():
        p = ROOT / 'src' / (name.replace('.', '/') + '.lean')
        if not p.is_file(): errors.append('Missing module: ' + name); continue
        if hashlib.sha256(p.read_bytes()).hexdigest() != record['source_sha256']:
            errors.append('Source differs from audited snapshot: ' + name)
        source = code_only(p.read_text())
        if re.search(r'\b(sorry|admit|axiom|native_decide)\b', source):
            errors.append('Forbidden proof token: ' + name)
        for dep in re.findall(r'^\s*(?:(?:public|private)\s+)?import\s+([\w.]+)', source, re.M):
            if dep not in names: external.add(dep)
    unknown = [n for n in external if n.split('.')[0] not in
               {'Mathlib','Lean','Init','Std','Batteries','Aesop','Qq','Plausible','ImportGraph','ProofWidgets','LeanSearchClient'}]
    errors += ['Unknown external import: ' + n for n in sorted(unknown)]
    if errors: raise RuntimeError('\n'.join(errors))
    return sorted(external)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check-only', action='store_true', help='only source hashes / imports / forbidden tokens')
    parser.add_argument('--skip-build', action='store_true', help='audit after a separately completed lake build')
    args = parser.parse_args()
    snapshot = json.loads((ROOT/'audit/verified-snapshot.json').read_text())
    check_sources(snapshot)
    print(f"Source/package checks passed: {len(snapshot['modules'])} modules", flush=True)
    if args.check_only: return
    lake = os.environ.get('LAKE', 'lake')
    if not args.skip_build:
        subprocess.run([lake, 'build'], cwd=ROOT, check=True)
    declarations = sorted({d for r in snapshot['modules'].values() for d in r['declarations']})
    work = ROOT/'.lake/audit'; work.mkdir(parents=True, exist_ok=True)
    audit = work/'Axioms.lean'
    audit.write_text('import Book\n' + ''.join('#print axioms '+d+'\n' for d in declarations))
    result = subprocess.run([lake,'env','lean',str(audit)],cwd=ROOT,text=True,
                            stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (work/'axioms.log').write_text(result.stdout)
    blocks = dict(re.findall(r"'(.+?)' depends on axioms: \[([^]]*)\]", result.stdout))
    empty = set(re.findall(r"'(.+?)' does not depend on any axioms", result.stdout))
    missing = sorted(set(declarations) - blocks.keys() - empty)
    unexpected = {n: sorted(set(a.strip() for a in b.split(',') if a.strip()) - ALLOWED)
                  for n,b in blocks.items() if set(a.strip() for a in b.split(',') if a.strip()) - ALLOWED}
    passed = result.returncode == 0 and not missing and not unexpected
    report = {'passed':passed,'date_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),
              'modules':len(snapshot['modules']),'declarations':len(declarations),
              'missing_declarations':missing,'unexpected_axioms':unexpected,
              'scope':'Lean statements and transitive axioms; not automatic verification of TeX prose.'}
    (ROOT/'audit/latest-run.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    if not passed: raise RuntimeError('Lean axiom audit failed; see .lake/audit/axioms.log and audit/latest-run.json')
    print(f"PASS: {len(declarations)} declarations; allowed axioms only")

if __name__ == '__main__':
    try: main()
    except (RuntimeError, subprocess.CalledProcessError) as e:
        print(e, file=sys.stderr); sys.exit(1)
