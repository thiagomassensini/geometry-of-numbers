#!/usr/bin/env python3
"""Inventory actual Lean declarations, excluding nested comments and strings."""
from pathlib import Path
import re


def lean_code(source):
    out = []
    pos, depth = 0, 0
    while pos < len(source):
        if source.startswith('/-', pos):
            depth += 1
            out.extend('  ')
            pos += 2
        elif depth and source.startswith('-/', pos):
            depth -= 1
            out.extend('  ')
            pos += 2
        elif depth:
            out.append('\n' if source[pos] == '\n' else ' ')
            pos += 1
        elif source.startswith('--', pos):
            end = source.find('\n', pos)
            end = len(source) if end < 0 else end
            out.extend(' ' * (end-pos))
            pos = end
        elif source[pos] == '"':
            out.append(' ')
            pos += 1
            while pos < len(source):
                if source[pos] == '\\' and pos+1 < len(source):
                    out.extend('  ')
                    pos += 2
                elif source[pos] == '"':
                    out.append(' ')
                    pos += 1
                    break
                else:
                    out.append('\n' if source[pos] == '\n' else ' ')
                    pos += 1
        else:
            out.append(source[pos])
            pos += 1
    assert depth == 0, 'Unclosed Lean comment'
    return ''.join(out)


def public_names(root):
    names = []
    for path in sorted(root.glob('*.lean')):
        if path.stem == 'Audit':
            continue
        names += re.findall(
            r'^(?:(?:noncomputable|protected) )?'
            r'(?:def|theorem|lemma|inductive|structure|abbrev) '
            r'([A-Za-z_][A-Za-z_0-9.\u0080-\uffff]*)',
            lean_code(path.read_text()), re.M)
    assert len(names) == len(set(names)), 'Duplicate public root'
    return names


def main():
    root = Path(__file__).resolve().parent
    names = public_names(root)
    expected = ''.join('CarryCriticalSource.' + n + '\n' for n in names)
    assert (root/'public-roots.txt').read_text() == expected, 'Stale public root inventory'
    audit = (root/'Audit.lean').read_text()
    for name in names:
        assert '\n#assert_central_comparison_axioms ' + name + '\n' in audit, name
        assert '\n#print axioms ' + name + '\n' in audit, name
    assert len(re.findall(r'^#assert_central_comparison_axioms ', audit, re.M)) == len(names)
    print(f'PASS: {len(names)} public roots have explicit transitive type-and-body guards')


if __name__ == '__main__':
    main()
