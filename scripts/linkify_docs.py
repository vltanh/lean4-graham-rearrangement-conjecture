#!/usr/bin/env python3
"""Link the Lean names in the Markdown documentation to the code.

Every inline code span that names a declaration, a module, a file or a directory of this
repository becomes a relative link; the link of a declaration points at the line of its
name. Existing links are kept, except links to a line of a Lean file, which are
recomputed: running the script after editing the code brings them up to date.

Run from the repository root, after `lake build`:

    python3 scripts/linkify_docs.py           # update the links
    python3 scripts/linkify_docs.py --check   # list the files whose links are out of date

The declaration locations come from the `.ilean` files that `lake build` writes.
"""

import argparse
import json
import os
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DOCS = ['README.md', 'REPORT.md', 'GrahamRearrangement/External/README.md']
BUILD = ROOT / '.lake' / 'build' / 'lib' / 'lean'
DOCS_URL = 'https://leanprover-community.github.io/mathlib4_docs/'

# Lean's standard axioms, and the core modules that declare them.
CORE = {'propext': 'Init.Core', 'Classical.choice': 'Init.Prelude', 'Quot.sound': 'Init.Prelude'}

# Namespaces in which the documentation names declarations without their prefix.
NAMESPACES = ['GrahamRearrangement', 'PhamSauermann'] + ['GrahamRearrangement.' + ns for ns in [
    'External', 'External.Hypergeometric', 'Auxiliary', 'Section3', 'Section4', 'Section5']]

# Directories, besides the repository root, against which the paths in the documents of a
# given directory are resolved.
PATH_BASES = {'': ['.github/workflows'], 'GrahamRearrangement/External': ['GrahamRearrangement/External']}

IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_'!?.₀-₉]*$")
TOKEN = re.compile(r'\[`([^`\n]+)`\]\(([^)\s]+)\)'  # a link whose text is a code span
                   r'|\[[^\]\n]*\]\([^)\s]*\)'       # any other link
                   r'|`([^`\n]+)`')                  # a code span
LINE_LINK = re.compile(r'^[^:#]+\.lean#L\d+$')
TABLE_RULE = re.compile(r'^\|\s*:?-{3}')


def warn(message):
    print('warning: ' + message, file=sys.stderr)


def module_file(module):
    return '/'.join(module.split('.')) + '.lean'


def load_locations():
    """Each declaration's module and the line of its name, read from the `.ilean` files."""
    locations, challenge = {}, {}
    for ilean in sorted(BUILD.rglob('*.ilean')):
        data = json.loads(ilean.read_text(encoding='utf-8'))
        # `Solution` restates the theorems of `Challenge`; those link to the challenge.
        target = challenge if data['module'] == 'Challenge' else locations
        for name, ranges in data.get('decls', {}).items():
            # `ranges` holds the declaration's range, then its name's; lines count from 0.
            target[name] = (data['module'], ranges[4] + 1)
    locations.update(challenge)
    if not locations:
        sys.exit('no .ilean files under %s; run `lake build` first' % BUILD)
    return locations


class Linker:
    def __init__(self, locations):
        self.locations = locations

    def declaration(self, name):
        candidates = [name]
        # Short names such as `U` or `h` are variables, not declarations.
        if len(name) >= 4:
            candidates += [ns + '.' + name for ns in NAMESPACES]
        hits = [c for c in candidates if c in self.locations]
        if not hits:
            return None
        if hits[0] != name and len(hits) > 1:
            warn('`%s` is ambiguous: %s' % (name, ', '.join(hits)))
            return None
        module, line = self.locations[hits[0]]
        return '%s#L%d' % (module_file(module), line)

    def target(self, text, doc_dir):
        """The repository path or URL that `text` names, or None."""
        path = text.rstrip('/')
        if path and not path.startswith(('/', '.')) and ' ' not in path:
            for base in [''] + PATH_BASES.get(doc_dir, []):
                candidate = os.path.normpath(os.path.join(base, path))
                if (ROOT / candidate).exists():
                    return candidate
        if not IDENT.match(text):
            return None
        if text.split('.')[0] in ('GrahamRearrangement', 'Challenge', 'Solution'):
            if (ROOT / module_file(text)).is_file():
                return module_file(text)
        if text.startswith('Mathlib.'):
            return DOCS_URL + text.replace('.', '/') + '.html'
        if text in CORE:
            return DOCS_URL + CORE[text].replace('.', '/') + '.html#' + text
        return self.declaration(text)

    def link(self, text, doc_dir):
        """The link target for `text` in a document of `doc_dir`, or None."""
        target = self.target(text, doc_dir)
        if target is None or target.startswith('https:'):
            return target
        path, _, anchor = target.partition('#')
        relative = os.path.relpath(ROOT / path, ROOT / doc_dir)
        if relative == '.':
            return None
        return relative + ('#' + anchor if anchor else '')

    def token(self, match, doc, doc_dir):
        text, old, span = match.groups()
        if text is not None:
            recompute = LINE_LINK.match(old) or (
                not old.startswith(('http:', 'https:', 'mailto:', '#'))
                and not (ROOT / doc_dir / old.partition('#')[0]).exists())
            if not recompute:
                return match.group(0)
            new = self.link(text, doc_dir)
            if new is None:
                warn('%s: `%s` names nothing any more; its link is removed' % (doc, text))
                return '`%s`' % text
            return '[`%s`](%s)' % (text, new)
        if span is not None:
            new = self.link(span, doc_dir)
            if new is not None:
                return '[`%s`](%s)' % (span, new)
        return match.group(0)

    def rewrite(self, doc):
        doc_dir = os.path.dirname(doc)
        lines = (ROOT / doc).read_text(encoding='utf-8').split('\n')
        fenced = False
        for i, line in enumerate(lines):
            if line.startswith('```'):
                fenced = not fenced
                continue
            header = line.startswith('|') and i + 1 < len(lines) and TABLE_RULE.match(lines[i + 1])
            if fenced or line.startswith('#') or header:
                continue
            lines[i] = TOKEN.sub(lambda m: self.token(m, doc, doc_dir), line)
        return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('--check', action='store_true',
                        help='list the files whose links are out of date, and change nothing')
    parser.add_argument('docs', nargs='*', help='Markdown files (default: %s)' % ', '.join(DOCS))
    args = parser.parse_args()
    docs = [os.path.relpath(os.path.abspath(d), ROOT) for d in args.docs] or DOCS
    linker = Linker(load_locations())
    changed = []
    for doc in docs:
        new = linker.rewrite(doc)
        if new != (ROOT / doc).read_text(encoding='utf-8'):
            changed.append(doc)
            if not args.check:
                (ROOT / doc).write_text(new, encoding='utf-8')
    for doc in changed:
        print(('out of date: ' if args.check else 'updated: ') + doc)
    return 1 if args.check and changed else 0


if __name__ == '__main__':
    sys.exit(main())
