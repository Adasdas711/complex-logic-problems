#!/usr/bin/env python3
"""merge_cards.py BASE AGENT PREFIX[,PREFIX...] — взять из AGENT карточки, чей id начинается с одного из префиксов (например 01.01,01.02), и вставить на место тех же id в BASE. Порядок и прочие карточки BASE сохраняются."""
import re, sys
base, agent, prefs = sys.argv[1], sys.argv[2], sys.argv[3].split(',')
def split(p):
    t = open(p, encoding='utf-8').read()
    return t, re.split(r'\n=====\n', t)
def cid(ch):
    m = re.search(r'^id: "?([^"\n]+)"?', ch, re.M); return m.group(1) if m else None
_, bch = split(base); _, ach = split(agent)
amap = {cid(c): c for c in ach if cid(c)}
out, n, miss = [], 0, []
for c in bch:
    i = cid(c)
    if i and any(i.startswith(p + '-') or i == p for p in prefs):
        if i in amap:
            new = amap[i]
            # сохранить хвостовой перевод строки последнего блока как в базе
            if c.endswith('\n') and not new.endswith('\n'): new += '\n'
            if not c.endswith('\n') and new.endswith('\n'): new = new.rstrip('\n')
            n += new != c; out.append(new)
        else:
            miss.append(i); out.append(c)
    else:
        out.append(c)
open(base, 'w', encoding='utf-8').write('\n=====\n'.join(out))
print(f'заменено {n}; нет в источнике: {miss}')
