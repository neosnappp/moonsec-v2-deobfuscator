import sys
import os
import re
import math
import unicodedata as ud
import encodings.aliases as ca
import shutil as sh
import subprocess as sub
import tempfile as tf
import heapq as hq
from collections import deque as dq
from pathlib import Path as P

sys.setrecursionlimit(2000)


class Err(Exception):
    pass


class N:
    def __init__(self, k, a=(), s=0, e=0, ln=1, tag=0):
        self.k = k
        self.a = list(a)
        self.s = s
        self.e = e
        self.ln = ln
        self.tag = tag


class T:
    def __init__(self, k, v, s, e, ln):
        self.k = k
        self.v = v
        self.s = s
        self.e = e
        self.ln = ln


def bad(msg):
    raise Err(msg)


def lex(src):
    out = []
    i = 0
    ln = 1
    n = len(src)
    num = re.compile(r'(?:0[xX][0-9a-fA-F_]+(?:\.[0-9a-fA-F_]+)?(?:[pP][+-]?[0-9_]+)?|0[bB][01_]+|(?:[0-9][0-9_]*(?:\.(?!\.)[0-9_]*)?|\.[0-9][0-9_]*)(?:[eE][+-]?[0-9_]+)?)')
    nam = re.compile(r'[A-Za-z_][A-Za-z_0-9]*')
    ops = ('...', '..=', '//=', '==', '~=', '<=', '>=', '+=', '-=', '*=', '/=', '%=', '^=', '..', '::', '->', '//')
    while i < n:
        s = i
        l = ln
        c = src[i]
        if c.isspace():
            ln += c == '\n'
            i += 1
            continue
        cm = src.startswith('--', i)
        j = i + 2 if cm else i
        m = re.match(r'\[(=*)\[', src[j: j + 128])
        if m:
            dl = ']' + m[1] + ']'
            b = j + len(m[0])
            z = src.find(dl, b)
            if z < 0:
                bad('unterminated long token at line ' + str(l))
            i = z + len(dl)
            ln += src[s:i].count('\n')
            if not cm:
                out.append(T('str', src[s:i], s, i, l))
            continue
        if cm:
            z = src.find('\n', i)
            i = n if z < 0 else z
            continue
        if c in ('"', "'", '`'):
            i += 1
            dep = 0
            while i < n:
                x = src[i]
                if x == '\\':
                    if i + 1 >= n:
                        bad('unterminated string at line ' + str(l))
                    esc = src[i + 1]
                    if esc == 'z' and c != '`':
                        i += 2
                        while i < n and src[i] in ' \t\v\f\r\n':
                            ln += src[i] == '\n'
                            i += 1
                    elif esc in '\r\n':
                        ln += 1
                        i += 2
                        if i < n and src[i] in '\r\n' and src[i] != esc:
                            i += 1
                    else:
                        i += 2
                    continue
                if x == c and dep == 0:
                    i += 1
                    break
                if c == '`':
                    if x == '{':
                        dep += 1
                    elif x == '}':
                        dep -= 1
                        if dep < 0:
                            bad('invalid interpolation at line ' + str(l))
                    elif x in ('"', "'") and dep:
                        q = x
                        i += 1
                        while i < n and src[i] != q:
                            if src[i] == '\\':
                                i += 1
                            if i < n:
                                ln += src[i] == '\n'
                            i += 1
                        if i == n:
                            bad('unterminated interpolation at line ' + str(l))
                elif x in '\n\r':
                    bad('unterminated string at line ' + str(l))
                ln += x == '\n'
                i += 1
            else:
                bad('unterminated string at line ' + str(l))
            if c != '`':
                try:
                    lit(src[s:i])
                except (ValueError, IndexError, OverflowError, UnicodeError):
                    bad('invalid string escape at line ' + str(l))
            out.append(T('str', src[s:i], s, i, l))
            continue
        m = num.match(src, i)
        if m:
            i = m.end()
            out.append(T('num', m[0], s, i, l))
            continue
        m = nam.match(src, i)
        if m:
            i = m.end()
            out.append(T('id', m[0], s, i, l))
            continue
        op = next((x for x in ops if src.startswith(x, i)), None)
        if op:
            i += len(op)
            out.append(T('op', op, s, i, l))
            continue
        if c in '+-*/%^#=<>;:,().{}[]~&|?':
            i += 1
            out.append(T('op', c, s, i, l))
            continue
        bad('invalid token at line ' + str(l))
    out.append(T('eof', '', n, n, ln))
    return out


def itp(tok):
    s = tok.v
    out = []
    beg = 0
    i = 1
    while i < len(s) - 1:
        if s[i] == '\\':
            i += 2
            continue
        if s[i] != '{':
            i += 1
            continue
        out.append(s[beg:i + 1])
        beg = i + 1
        i += 1
        dep = 1
        while i < len(s) - 1 and dep:
            c = s[i]
            if c in ('"', "'", '`'):
                q = c
                i += 1
                while i < len(s) - 1:
                    if s[i] == '\\':
                        i += 2
                    elif s[i] == q:
                        i += 1
                        break
                    else:
                        i += 1
                else:
                    bad('unterminated interpolation at line ' + str(tok.ln))
                continue
            m = re.match(r'\[(=*)\[', s[i:i + 128])
            if m:
                dl = ']' + m[1] + ']'
                end = s.find(dl, i + len(m[0]))
                if end < 0:
                    bad('unterminated interpolation long string at line ' + str(tok.ln))
                i = end + len(dl)
                continue
            if c == '{':
                dep += 1
            elif c == '}':
                dep -= 1
                if not dep:
                    break
            i += 1
        if dep:
            bad('unterminated interpolation at line ' + str(tok.ln))
        p = Prs(lex(s[beg:i]))
        x = p.exp()
        if p.cur().k != 'eof':
            bad('malformed interpolation at line ' + str(tok.ln))
        out.append(x)
        beg = i
        i += 1
    out.append(s[beg:])
    return out


class Prs:
    def __init__(self, tok):
        self.tok = tok
        self.i = 0
        self.dep = 0
        self.stp = 0
        self.varg = True
        self.lim = max(10000, len(tok) * 40)
        self.kw = set('and break do else elseif end false for function if in local nil not or repeat return then true until while continue'.split())
        self.bp = {'or': (1, 2), 'and': (2, 3), '<': (3, 4), '>': (3, 4), '<=': (3, 4), '>=': (3, 4), '~=': (3, 4), '==': (3, 4), '..': (4, 4), '+': (5, 6), '-': (5, 6), '*': (6, 7), '/': (6, 7), '//': (6, 7), '%': (6, 7), '^': (8, 8)}

    def cur(self):
        return self.tok[self.i]

    def at(self, v):
        return self.cur().v == v

    def pop(self):
        self.stp += 1
        if self.stp > self.lim:
            bad('parser step limit exceeded')
        t = self.cur()
        if t.k != 'eof':
            self.i += 1
        return t

    def eat(self, v):
        if self.at(v):
            self.pop()
            return True
        return False

    def req(self, v):
        if not self.eat(v):
            bad('parse error at line ' + str(self.cur().ln))

    def nam(self):
        t = self.pop()
        if t.k != 'id' or t.v in self.kw:
            bad('invalid name at line ' + str(t.ln))
        return N('id', [t.v], t.s, t.e, t.ln)

    def mk(self, k, a, t):
        return N(k, a, t.s, self.tok[max(0, self.i - 1)].e, t.ln)

    def blk(self, end=(), loop=0):
        self.dep += 1
        if self.dep > 160:
            bad('parse depth exceeded')
        out = []
        while self.cur().k != 'eof' and self.cur().v not in end:
            old = self.i
            x = self.stmt(loop)
            if x is not None:
                out.append(x)
            if self.i <= old:
                bad('parser progress failure at line ' + str(self.cur().ln))
        self.dep -= 1
        return out

    def typ(self, stop):
        if stop == {'>'}:
            d = []
            st = self.i
            while self.cur().k != 'eof':
                v = self.cur().v
                if not d and v in stop:
                    break
                if v in ('(', '{', '[', '<'):
                    d.append({'(': ')', '{': '}', '[': ']', '<': '>'}[v])
                elif d and v == d[-1]:
                    d.pop()
                self.pop()
            if st == self.i or d:
                bad('malformed type at line ' + str(self.cur().ln))
            return
        self.ty()

    def ty(self, bp=0):
        self.dep += 1
        if self.dep > 160:
            bad('type depth exceeded')
        t = self.cur()
        if self.eat('...'):
            self.ty(3)
        elif self.eat('<'):
            self.typ({'>'})
            self.req('>')
            self.ty(3)
        elif self.eat('('):
            if not self.at(')'):
                while True:
                    if self.cur().k == 'id' and self.tok[self.i + 1].v == ':':
                        self.pop()
                        self.pop()
                    self.ty()
                    if not self.eat(','):
                        break
            self.req(')')
        elif self.eat('{'):
            while not self.at('}'):
                if self.eat('['):
                    self.ty()
                    self.req(']')
                    self.req(':')
                    self.ty()
                elif self.cur().k == 'id' and self.tok[self.i + 1].v == ':':
                    self.pop()
                    self.pop()
                    self.ty()
                else:
                    self.ty()
                if not self.eat(',') and not self.eat(';'):
                    break
            self.req('}')
        elif t.k == 'id' or t.k == 'str':
            self.pop()
            if t.v == 'typeof' and self.eat('('):
                self.exp()
                self.req(')')
            else:
                while self.eat('.'):
                    self.nam()
                if self.eat('<'):
                    if not self.at('>'):
                        while True:
                            self.ty()
                            if not self.eat(','):
                                break
                    self.req('>')
        else:
            bad('malformed type at line ' + str(t.ln))
        while self.eat('?') or self.eat('...'):
            pass
        while self.cur().v in ('|', '&') and (1 if self.cur().v == '|' else 2) >= bp:
            op = self.pop().v
            self.ty(2 if op == '|' else 3)
        if bp == 0 and self.eat('->'):
            self.ty()
        self.dep -= 1

    def fn(self, t):
        if self.eat('<'):
            self.typ({'>'})
            self.req('>')
        self.req('(')
        ps = []
        if not self.at(')'):
            while True:
                if self.at('...'):
                    x = self.pop()
                    ps.append(N('id', ['...'], x.s, x.e, x.ln))
                else:
                    ps.append(self.nam())
                if self.eat(':'):
                    self.typ({',', ')'})
                if not self.eat(','):
                    break
                if ps[-1].a[0] == '...':
                    bad('variadic parameter must be last at line ' + str(self.cur().ln))
        self.req(')')
        if self.eat(':'):
            self.typ({'local', 'return', 'if', 'for', 'while', 'repeat', 'do', 'end'})
        prev = self.varg
        self.varg = bool(ps) and ps[-1].a[0] == '...'
        b = self.blk({'end'}, 0)
        self.varg = prev
        self.req('end')
        return self.mk('fn', [ps, b], t)

    def lst(self):
        out = [self.exp()]
        while self.eat(','):
            out.append(self.exp())
        return out

    def stmt(self, loop):
        t = self.cur()
        v = t.v
        if self.eat(';'):
            return None
        if self.eat('local'):
            if self.eat('function'):
                n = self.nam()
                f = self.fn(t)
                return self.mk('lfn', [n, f], t)
            ns = [self.nam()]
            if self.eat(':'):
                self.typ({',', '='})
            while self.eat(','):
                ns.append(self.nam())
                if self.eat(':'):
                    self.typ({',', '='})
            es = self.lst() if self.eat('=') else []
            return self.mk('loc', [ns, es], t)
        if self.eat('function'):
            n = self.nam()
            while self.eat('.'):
                n = self.mk('dot', [n, self.nam()], t)
            if self.eat(':'):
                n = self.mk('met', [n, self.nam()], t)
            f = self.fn(t)
            return self.mk('def', [n, f], t)
        if self.eat('if'):
            bs = []
            c = self.exp()
            self.req('then')
            bs.append([c, self.blk({'elseif', 'else', 'end'}, loop)])
            while self.eat('elseif'):
                c = self.exp()
                self.req('then')
                bs.append([c, self.blk({'elseif', 'else', 'end'}, loop)])
            e = self.blk({'end'}, loop) if self.eat('else') else []
            self.req('end')
            return self.mk('if', [bs, e], t)
        if self.eat('while'):
            c = self.exp()
            self.req('do')
            b = self.blk({'end'}, loop + 1)
            self.req('end')
            return self.mk('wh', [c, b], t)
        if self.eat('repeat'):
            b = self.blk({'until'}, loop + 1)
            self.req('until')
            c = self.exp()
            return self.mk('rep', [b, c], t)
        if self.eat('do'):
            b = self.blk({'end'}, loop)
            self.req('end')
            return self.mk('do', [b], t)
        if self.eat('for'):
            ns = [self.nam()]
            if self.eat('='):
                es = self.lst()
                if len(es) not in (2, 3):
                    bad('malformed for header at line ' + str(t.ln))
                k = 'for'
            else:
                while self.eat(','):
                    ns.append(self.nam())
                self.req('in')
                es = self.lst()
                k = 'iter'
            self.req('do')
            b = self.blk({'end'}, loop + 1)
            self.req('end')
            return self.mk(k, [ns, es, b], t)
        if self.eat('return'):
            es = [] if self.cur().k == 'eof' or self.cur().v in (';', 'end', 'else', 'elseif', 'until') else self.lst()
            return self.mk('ret', [es], t)
        if v in ('break', 'continue'):
            if not loop:
                bad('invalid ' + v + ' at line ' + str(t.ln))
            self.pop()
            return self.mk(v, [], t)
        if self.at('export') or self.at('type') and self.tok[self.i + 1].k == 'id':
            self.eat('export')
            self.req('type')
            n = self.nam()
            if self.eat('<'):
                self.typ({'>'})
                self.req('>')
            self.req('=')
            self.typ({';', 'local', 'return', 'function', 'export', 'type'})
            return self.mk('type', [n], t)
        x = self.exp()
        if self.cur().v in ('=', ',', '+=', '-=', '*=', '/=', '//=', '%=', '^=', '..='):
            ns = [x]
            while self.eat(','):
                ns.append(self.exp())
            op = self.pop().v
            if op not in ('=', '+=', '-=', '*=', '/=', '//=', '%=', '^=', '..='):
                bad('malformed assignment at line ' + str(t.ln))
            if any(n.k not in ('id', 'idx', 'dot') for n in ns):
                bad('invalid assignment target at line ' + str(t.ln))
            es = self.lst()
            if op != '=' and (len(ns) != 1 or len(es) != 1):
                bad('malformed compound assignment at line ' + str(t.ln))
            return self.mk('set', [ns, es, op], t)
        if x.k not in ('call', 'mcall'):
            bad('invalid statement at line ' + str(t.ln))
        return self.mk('stmt', [x], t)

    def exp(self, bp=0):
        self.dep += 1
        if self.dep > 160:
            bad('expression depth exceeded')
        t = self.pop()
        v = t.v
        if v in ('-', '#', 'not', '~'):
            x = self.mk('un', [v, self.exp(7)], t)
        elif t.k == 'num':
            x = self.mk('num', [v], t)
        elif t.k == 'str':
            x = self.mk('interp', [itp(t)], t) if v.startswith('`') else self.mk('str', [v], t)
        elif v in ('nil', 'true', 'false', '...'):
            if v == '...' and not self.varg:
                bad('vararg outside variadic function at line ' + str(t.ln))
            x = self.mk(v, [], t)
        elif v == 'function':
            x = self.fn(t)
        elif v == '(':
            a = self.exp()
            self.req(')')
            x = self.mk('grp', [a], t)
        elif v == '{':
            fs = []
            while not self.at('}'):
                if self.cur().k == 'eof':
                    bad('unterminated table at line ' + str(t.ln))
                if self.eat('['):
                    k = self.exp()
                    self.req(']')
                    self.req('=')
                    a = self.exp()
                elif self.cur().k == 'id' and self.tok[self.i + 1].v == '=':
                    k = self.nam()
                    k = N('key', k.a, k.s, k.e, k.ln)
                    self.req('=')
                    a = self.exp()
                else:
                    k = None
                    a = self.exp()
                fs.append([k, a])
                if not self.eat(',') and not self.eat(';'):
                    break
            self.req('}')
            x = self.mk('tab', [fs], t)
        elif v == 'if':
            arms = []
            head = t
            while True:
                c = self.exp()
                self.req('then')
                a = self.exp()
                arms.append((head, c, a))
                if not self.at('elseif'):
                    break
                head = self.pop()
            self.req('else')
            x = self.exp()
            for head, c, a in reversed(arms):
                x = self.mk('iex', [c, a, x], head)
        elif t.k == 'id' and v not in self.kw:
            x = self.mk('id', [v], t)
        else:
            bad('parse error at line ' + str(t.ln))
        while True:
            if self.eat('['):
                k = self.exp()
                self.req(']')
                x = self.mk('idx', [x, k], t)
            elif self.eat('.'):
                x = self.mk('dot', [x, self.nam()], t)
            elif self.eat(':'):
                n = self.nam()
                a = self.args()
                x = self.mk('mcall', [x, n, a], t)
            elif self.at('(') or self.at('{') or self.cur().k == 'str':
                a = self.args()
                x = self.mk('call', [x, a], t)
            elif self.eat('::'):
                st = self.i
                self.typ({',', ')', ']', '}', ';', '=', '+', '-', '*', '/', 'and', 'or'})
                x = self.mk('cast', [x, st, self.i], t)
            else:
                break
        while self.cur().v in self.bp and self.bp[self.cur().v][0] >= bp:
            op = self.pop().v
            y = self.exp(self.bp[op][1])
            x = self.mk('bin', [op, x, y], t)
        self.dep -= 1
        return x

    def args(self):
        if self.eat('('):
            a = [] if self.at(')') else self.lst()
            self.req(')')
            return a
        if self.at('{') or self.cur().k == 'str':
            return [self.exp(9)]
        bad('malformed call at line ' + str(self.cur().ln))


def walk(ast):
    st = [ast]
    n = 0
    while st:
        n += 1
        if n > 8000000:
            bad('ast step limit exceeded')
        x = st.pop()
        if isinstance(x, N):
            yield x
            st.extend(reversed(x.a))
        elif isinstance(x, (list, tuple)):
            st.extend(reversed(x))


def ung(x):
    while x.k in ('grp', 'cast'):
        x = x.a[0]
    return x


def lit(s):
    if s.startswith('`'):
        raise ValueError()
    if s.startswith('['):
        m = re.match(r'\[(=*)\[', s)
        s = s[len(m[0]): -len(m[0])]
        s = re.sub(r'\r\n|\n\r|\r', '\n', s)
        if s.startswith('\n'):
            s = s[1:]
        return s.encode('utf-8')
    s = s[1:-1]
    out = bytearray()
    i = 0
    esc = {'a': 7, 'b': 8, 'f': 12, 'n': 10, 'r': 13, 't': 9, 'v': 11, '\\': 92, "'": 39, '"': 34}
    while i < len(s):
        c = s[i]
        if c != '\\':
            out.extend(c.encode('utf-8'))
            i += 1
            continue
        i += 1
        c = s[i]
        if c in esc:
            out.append(esc[c])
            i += 1
        elif c.isdigit() and c.isascii():
            m = re.match(r'[0-9]{1,3}', s[i: i + 3])
            v = int(m[0])
            if v > 255:
                raise ValueError()
            out.append(v)
            i += len(m[0])
        elif c == 'x':
            if not re.fullmatch(r'[0-9a-fA-F]{2}', s[i + 1:i + 3]):
                raise ValueError()
            out.append(int(s[i + 1:i + 3], 16))
            i += 3
        elif c == 'u' and s[i + 1:i + 2] == '{':
            j = s.index('}', i + 2)
            if not re.fullmatch(r'[0-9a-fA-F]+', s[i + 2:j]):
                raise ValueError()
            out.extend(chr(int(s[i + 2:j], 16)).encode('utf-8'))
            i = j + 1
        elif c == 'z':
            i += 1
            while i < len(s) and s[i] in ' \t\v\f\r\n':
                i += 1
        elif c in '\r\n':
            out.append(10)
            if s[i + 1:i + 2] in ('\r', '\n') and s[i + 1] != c:
                i += 1
            i += 1
        else:
            raise ValueError()
    return bytes(out)


def tru(x):
    return x is not None and x is not False


def cv(x, env, mem, many=False):
    key = (id(x), many)
    if key in mem:
        return mem[key]
    k = x.k
    a = x.a
    if k == 'num':
        s = a[0].replace('_', '')
        if s.lower().startswith('0x'):
            v = float.fromhex(s)
        elif s.lower().startswith('0b'):
            v = int(s, 2)
        else:
            v = float(s)
    elif k == 'str':
        v = lit(a[0])
    elif k == 'fn':
        v = x
    elif k == 'true':
        v = True
    elif k == 'false':
        v = False
    elif k == 'nil':
        v = None
    elif k in ('grp', 'cast'):
        v = cv(a[0], env, mem)
    elif k == 'id':
        if a[0] not in env:
            raise ValueError()
        v = env[a[0]]
    elif k == 'un':
        v = cv(a[1], env, mem)
        if a[0] == '-':
            if type(v) not in (int, float):
                raise ValueError()
            v = -v
        elif a[0] == 'not':
            v = not tru(v)
        elif a[0] == '#':
            if not isinstance(v, (bytes, tuple)):
                raise ValueError()
            if isinstance(v, tuple):
                size = len(v)
                while size and v[size - 1] is None:
                    size -= 1
                if any(q is None for q in v[:size]):
                    raise ValueError()
                v = size
            else:
                v = len(v)
        else:
            raise ValueError()
    elif k == 'tab':
        if any(q[0] is not None for q in a[0]):
            raise ValueError()
        vals = []
        for i, q in enumerate(a[0]):
            item = cv(q[1], env, mem, i == len(a[0]) - 1)
            if isinstance(item, V) and item.k == 'vals':
                vals.extend(item.a)
            else:
                vals.append(item)
        v = tuple(vals)
        end = False
        for q in v:
            if q is None:
                end = True
            elif end:
                raise ValueError()
    elif k == 'bin':
        op = a[0]
        l = cv(a[1], env, mem)
        if op == 'and':
            v = cv(a[2], env, mem) if tru(l) else l
        elif op == 'or':
            v = l if tru(l) else cv(a[2], env, mem)
        else:
            r = cv(a[2], env, mem)
            if op in ('==', '~='):
                if isinstance(l, tuple) or isinstance(r, tuple):
                    raise ValueError()
                eq = (type(l) == type(r) or type(l) in (int, float) and type(r) in (int, float)) and l == r
                v = eq if op == '==' else not eq
            elif op == '..':
                if not isinstance(l, bytes) or not isinstance(r, bytes):
                    raise ValueError()
                if len(l) + len(r) > 32000000:
                    bad('constant size limit exceeded')
                v = l + r
            elif op in ('<', '>', '<=', '>='):
                if type(l) not in (int, float) or type(r) not in (int, float):
                    raise ValueError()
                v = {'<': l < r, '>': l > r, '<=': l <= r, '>=': l >= r}[op]
            else:
                if type(l) not in (int, float) or type(r) not in (int, float):
                    raise ValueError()
                if op == '+':
                    v = l + r
                elif op == '-':
                    v = l - r
                elif op == '*':
                    v = l * r
                elif op == '/':
                    v = l / r
                elif op == '//':
                    v = math.floor(l / r)
                elif op == '%':
                    v = l % r
                elif op == '^':
                    if abs(r) > 4096 or abs(l) > 1e100:
                        raise ValueError()
                    v = l ** r
                else:
                    raise ValueError()
    elif k == 'iex':
        v = cv(a[1] if tru(cv(a[0], env, mem)) else a[2], env, mem)
    elif k == 'mcall':
        if a[1].a[0] != 'find' or not 1 <= len(a[2]) <= 3:
            raise ValueError()
        obj = cv(a[0], env, mem)
        args = [cv(q, env, mem) for q in a[2]]
        if not isinstance(obj, bytes) or not isinstance(args[0], bytes):
            raise ValueError()
        pat = args[0]
        plai = len(args) == 3 and tru(args[2])
        if not plai and any(c in pat for c in b'^$()%.[]*+-?'):
            raise ValueError()
        pos = args[1] if len(args) > 1 else 1
        if type(pos) not in (int, float) or not math.isfinite(pos) or pos != int(pos):
            raise ValueError()
        pos = max(1, int(pos) if pos >= 0 else len(obj) + int(pos) + 1)
        idx = obj.find(pat, pos - 1) if pos <= len(obj) + 1 else -1
        if idx < 0:
            v = None
        else:
            vals = [idx + 1, idx + len(pat)]
            v = V('vals', vals) if many else vals[0]
    elif k == 'call':
        f = ung(a[0])
        if f.k != 'fn' or len(f.a[1]) != 1 or f.a[1][0].k != 'ret' or len(f.a[1][0].a[0]) != 1:
            raise ValueError()
        ps = f.a[0]
        if any(p.a[0] == '...' for p in ps):
            raise ValueError()
        vals = []
        for i, q in enumerate(a[1]):
            item = cv(q, env, mem, i == len(a[1]) - 1)
            if isinstance(item, V) and item.k == 'vals':
                vals.extend(item.a)
            else:
                vals.append(item)
        loc = dict(env)
        for i, p in enumerate(ps):
            loc[p.a[0]] = vals[i] if i < len(vals) else None
        v = cv(f.a[1][0].a[0][0], loc, {}, many)
    else:
        raise ValueError()
    if isinstance(v, (float, int)) and not isinstance(v, bool):
        if not math.isfinite(v):
            raise ValueError()
    mem[key] = v
    return v


def val(x, env=None):
    try:
        return True, cv(x, {} if env is None else env, {})
    except (ValueError, TypeError, ZeroDivisionError, OverflowError, IndexError, KeyError):
        return False, None


def txt(x, src):
    return src[x.s:x.e]


def num(v):
    if v == int(v) and abs(v) < 2 ** 53:
        return str(int(v))
    return repr(float(v))


def scan(ast):
    fs = []
    vms = []
    for x in walk(ast):
        if x.k == 'lfn':
            fs.append((x.a[0].a[0], x.a[1], x.ln))
        if x.k != 'wh':
            continue
        b = x.a[1]
        if len(b) < 2 or b[0].k != 'set' or b[1].k != 'set':
            continue
        q = b[0].a
        r = b[1].a
        if len(q[0]) != 1 or len(q[1]) != 1 or len(r[0]) != 1 or len(r[1]) != 1:
            continue
        a = ung(q[1][0])
        c = ung(r[1][0])
        if a.k != 'idx' or c.k != 'idx' or q[0][0].k != 'id':
            continue
        if c.a[0].k == 'id' and c.a[0].a[0] == q[0][0].a[0]:
            vms.append((x, q[0][0], a, r[0][0], c))
    return fs, vms


def dec(ast):
    out = []
    for x in walk(ast):
        if x.k != 'call' or len(x.a[1]) != 1:
            continue
        f = ung(x.a[0])
        a = x.a[1][0]
        if f.k != 'fn' or a.k != 'str':
            continue
        bs = f.a[1]
        if not bs or bs[0].k != 'loc' or len(bs[0].a[0]) != 2 or len(bs[0].a[1]) != 2:
            continue
        ok, w = val(bs[0].a[1][0])
        if not ok or type(w) not in (float, int) or w <= 0 or w != int(w):
            continue
        if not any(z.k == 'mcall' and z.a[1].a[0] == 'sub' for z in walk(f)):
            continue
        if not any(z.k == 'wh' for z in walk(f)):
            continue
        out.append((x, f, int(w), a))
    return out


def enc(x, f, w, a, env):
    loc = dict(env)
    for z in f.a[1]:
        if z.k == 'wh':
            break
        if z.k != 'loc':
            continue
        for n, q in zip(z.a[0], z.a[1]):
            ok, v = val(q, loc)
            if ok:
                loc[n.a[0]] = v
    wh = next((z for z in f.a[1] if z.k == 'wh'), None)
    if wh is None:
        return None
    cmp = []
    for z in walk(wh):
        if z.k == 'bin' and z.a[0] == '==':
            for q in z.a[1:]:
                ok, v = val(q, loc)
                if ok and type(v) in (float, int) and v > 0:
                    cmp.append(v)
    if len(cmp) != 1:
        return None
    cnt = cmp[0] + 1
    if cnt != int(cnt) or cnt > 256:
        return None
    begs = []
    for z in f.a[1]:
        if z is wh:
            break
        if z.k == 'loc':
            for n, q in zip(z.a[0], z.a[1]):
                if q.k == 'bin' and q.a[0] == '+':
                    ok, v = val(q, loc)
                    if ok and v >= 1 and v == int(v):
                        begs.append(int(v))
    if len(begs) != 1:
        return None
    buf = lit(a.a[0])
    st = begs[0] - 1
    cnt = int(cnt)
    lps = [z for z in f.a[1] if z.k == 'wh' and z is not wh]
    if len(lps) != 1:
        bad('encoded symbol loop plan unresolved')
    tsts = [z for z in lps[0].a[1] if z.k == 'if']
    if len(tsts) != 1 or len(tsts[0].a[0]) != 1 or tsts[0].a[1]:
        bad('encoded pair condition plan unresolved')
    test, body = tsts[0].a[0][0]
    test = ung(test)
    if test.k != 'bin' or test.a[0] != '==':
        bad('encoded pair condition operation unresolved')
    mod, zero = ung(test.a[1]), test.a[2]
    if mod.k != 'bin' or mod.a[0] != '%':
        mod, zero = ung(test.a[2]), test.a[1]
    if mod.k != 'bin' or mod.a[0] != '%' or ung(mod.a[1]).k != 'id':
        bad('encoded pair modulus plan unresolved')
    name = ung(mod.a[1]).a[0]
    size, off = val(mod.a[2], loc), val(zero, loc)
    if not size[0] or not off[0]:
        miss = sorted({q.a[0].lower() for q in walk([mod.a[2], zero]) if q.k == 'id' and q.a[0] not in loc})
        bad('encoded pair counter condition unresolved' + (' for ' + ','.join(miss) if miss else '') + ' at line ' + str(test.ln))
    if type(size[1]) not in (int, float) or type(off[1]) not in (int, float) or size[1] != 2 or off[1] != 0:
        bad('encoded pair counter does not select two symbols')
    init = [z for z in walk(wh) if z.k == 'set' and len(z.a[0]) == len(z.a[1]) == 1 and z.a[0][0].k == 'id' and z.a[0][0].a[0] == name]
    rest = [z for z in body if z.k == 'set' and len(z.a[0]) == len(z.a[1]) == 1 and z.a[0][0].k == 'id' and z.a[0][0].a[0] == name]
    step = [z for z in lps[0].a[1] if z.k == 'set' and len(z.a[0]) == len(z.a[1]) == 1 and z.a[0][0].k == 'id' and z.a[0][0].a[0] == name]
    if len(init) != 1 or len(rest) != 1 or len(step) != 1:
        bad('encoded pair counter state plan unresolved')
    for z in init + rest:
        ok, v = val(z.a[1][0], loc)
        if not ok:
            bad('encoded pair counter state unresolved at line ' + str(z.ln))
        if z.a[2] != '=' or type(v) not in (int, float) or v != 0:
            bad('encoded pair counter initial state is not zero')
    z = step[0]
    inc = ung(z.a[1][0]) if z.a[2] == '=' else N('bin', [z.a[2][:-1], z.a[0][0], z.a[1][0]])
    if inc.k != 'bin' or inc.a[0] != '+':
        bad('encoded pair counter increment operation unresolved')
    left, rite = ung(inc.a[1]), inc.a[2]
    if left.k != 'id' or left.a[0] != name:
        left, rite = ung(inc.a[2]), inc.a[1]
    ok, v = val(rite, loc)
    if left.k != 'id' or left.a[0] != name or not ok or type(v) not in (int, float) or v != 1:
        bad('encoded pair counter increment is not one')
    end = st + cnt * w
    if end > len(buf):
        bad('encoded alphabet exceeds string at line ' + str(a.ln))
    tab = {buf[j:j + w]: i for i, j in enumerate(range(st, end, w))}
    pad = (len(buf) - end) % (w * 2)
    if pad:
        loop = lps[0].a[1]
        tail = f.a[1][-1]
        head = loop[0]
        good = pad <= w and len(loop) == 3 and loop[1] is step[0] and loop[2] is tsts[0]
        good = good and head.k == 'set' and head.a[2] == '=' and len(head.a[0]) == len(head.a[1]) == 1
        if good:
            dst = ung(head.a[0][0])
            src = ung(head.a[1][0])
            good = dst.k == 'idx' and ung(dst.a[0]).k == 'dot' and ung(dst.a[1]).k == 'id' and ung(dst.a[1]).a[0] == name
            good = good and src.k == 'mcall' and src.a[1].a[0] == 'sub'
        if good:
            good = tail.k == 'ret' and len(tail.a[0]) == 1 and ung(tail.a[0][0]).k == 'call'
        if good:
            ret = ung(tail.a[0][0])
            good = len(ret.a[1]) == 1 and ung(ret.a[1][0]).k == 'dot'
        if good:
            acc = ung(ret.a[1][0])
            box = ung(dst.a[0])
            good = box.a[0].k == acc.a[0].k == 'id' and box.a[0].a[0] == acc.a[0].a[0] and box.a[1].a[0] != acc.a[1].a[0]
            good = good and len(body) == 2 and body[0] is rest[0] and body[1].k == 'stmt'
        if good:
            app = ung(body[1].a[0])
            good = app.k == 'call' and len(app.a[1]) == 2 and Em().ex(app.a[1][0]) == Em().ex(acc)
        if not good:
            bad('encoded byte pair truncated at line ' + str(a.ln))
    out = bytearray()
    for j in range(end, len(buf) - pad, w * 2):
        hi = tab.get(buf[j:j + w])
        lo = tab.get(buf[j + w:j + w * 2])
        if hi is None or lo is None:
            if len(tab) != cnt:
                bad('encoded alphabet has ' + str(len(tab)) + ' distinct symbols for ' + str(cnt) + ' slots and an absent payload symbol at byte ' + str(j))
            bad('encoded symbol absent from alphabet at byte ' + str(j))
        v = hi * cnt + lo
        if v > 255:
            bad('encoded byte exceeds range at byte ' + str(j))
        out.append(v)
    return bytes(out)


def envs(ast):
    out = {}
    for x in walk(ast):
        if x.k != 'fn':
            continue
        env = {}
        for z in x.a[1]:
            if z.k not in ('loc', 'lfn'):
                break
            if z.k == 'lfn':
                continue
            for n, q in zip(z.a[0], z.a[1]):
                ok, v = val(q, env)
                if ok:
                    env[n.a[0]] = v
            for q in z.a[1]:
                for y in walk(q):
                    if y.k == 'call' and ung(y.a[0]).k == 'fn':
                        out[id(y)] = dict(env)
    return out


class Rd:
    def __init__(self, buf, env, tab):
        self.buf = buf
        self.env = dict(env)
        self.tab = {}
        self.fun = {}
        self.pos = None
        self.stp = 0
        for key, fn in tab.a[0]:
            ok, kv = val(key, env)
            if not ok or type(kv) not in (int, float):
                continue
            self.fun[int(kv)] = fn
            bs = fn.a[1]
            if len(bs) < 2 or bs[0].k != 'loc' or bs[-1].k != 'ret':
                continue
            ns, es = bs[0].a
            if len(es) != 1:
                continue
            call = ung(es[0])
            if call.k != 'call' or len(call.a[1]) != 3:
                continue
            arg = call.a[1]
            pos = ung(arg[1])
            if pos.k != 'id':
                continue
            pn = pos.a[0]
            loc = dict(env)
            loc[pn] = 0
            ok, end = val(arg[2], loc)
            if not ok or type(end) not in (float, int) or end != int(end):
                continue
            span = int(end) + 1
            size = len(ns)
            if span < size or size < 1 or size > len(buf):
                continue
            if any(z.k != 'set' or any(n.k != 'id' for n in z.a[0]) or z.a[2] != '=' for z in bs[1:-1]):
                continue
            if len(bs[-1].a[0]) != 1:
                continue
            if self.pos is None:
                self.pos = pn
            if self.pos != pn:
                continue
            self.tab[int(kv)] = (ns, size, bs[1:-1], bs[-1].a[0][0])
        if self.pos is None or self.pos not in env:
            bad('reader cursor initial value absent')
        if type(env[self.pos]) not in (int, float):
            bad('reader cursor initial value is not numeric')

    def get(self, key):
        self.stp += 1
        if self.stp > len(self.buf) + 1:
            bad('reader step limit exceeded')
        if key not in self.tab:
            bad('reader arithmetic plan absent for key ' + str(key))
        ns, size, sets, ret = self.tab[key]
        pos = self.env[self.pos] - 1
        if pos != int(pos) or pos < 0 or pos + size > len(self.buf):
            bad('reader truncated at offset ' + str(int(pos)))
        pos = int(pos)
        loc = dict(self.env)
        for n, b in zip(ns, self.buf[pos:pos + size]):
            loc[n.a[0]] = b
        upd = {}
        for z in sets:
            vals = []
            for q in z.a[1]:
                ok, v = val(q, loc)
                if not ok:
                    bad('reader update expression unresolved at offset ' + str(pos))
                vals.append(v)
            for n, v in zip(z.a[0], vals):
                loc[n.a[0]] = v
                upd[n.a[0]] = v
        ok, v = val(ret, loc)
        if not ok:
            bad('reader return expression unresolved at offset ' + str(pos))
        if upd.get(self.pos) != self.env[self.pos] + size:
            bad('reader cursor increment differs from read width at offset ' + str(pos))
        self.env.update(upd)
        return v


def rdr(ast, buf):
    for f in walk(ast):
        if f.k != 'fn':
            continue
        env = {}
        for z in f.a[1]:
            if z.k not in ('loc', 'set'):
                continue
            ns, es = z.a[:2]
            if len(es) == 1 and es[0].k == 'tab':
                tab = es[0]
                if tab.a[0] and all(k is not None and v.k == 'fn' for k, v in tab.a[0]):
                    rd = Rd(buf, env, tab)
                    if rd.tab:
                        rd.own = f
                        return rd, ns[0].a[0]
            vals = [val(q, env) for q in es]
            for i, n in enumerate(ns):
                if n.k != 'id':
                    continue
                if i < len(vals) and vals[i][0]:
                    env[n.a[0]] = vals[i][1]
                else:
                    env.pop(n.a[0], None)
    return None


def rkey(x, name):
    x = ung(x)
    if x.k != 'call' or x.a[1]:
        return None
    f = ung(x.a[0])
    if f.k != 'idx' or f.a[0].k != 'id' or f.a[0].a[0] != name:
        return None
    return f.a[1]


def head(ast, rd, name):
    for f in walk(ast):
        if f.k != 'lfn':
            continue
        fn = f.a[1]
        if fn.a[0] or not any(z.k == 'for' for z in fn.a[1]):
            continue
        env = dict(rd.env)
        out = []
        for z in fn.a[1]:
            if z.k == 'for':
                break
            if z.k not in ('loc', 'set'):
                continue
            for n, q in zip(z.a[0], z.a[1]):
                k = rkey(q, name)
                if k is not None:
                    ok, kv = val(k, env)
                    if not ok or kv not in rd.tab:
                        return None
                    out.append((n, int(kv)))
                elif n.k == 'id':
                    ok, v = val(q, env)
                    if ok:
                        env[n.a[0]] = v
                    else:
                        env.pop(n.a[0], None)
        if out:
            return f.a[0].a[0], [(n, rd.get(k)) for n, k in out]
    return None


def atom(v):
    if v is None:
        return N('nil')
    if type(v) is bool:
        return N('true' if v else 'false')
    if isinstance(v, bytes):
        try:
            s = v.decode('utf-8')
            esc = {'\\': '\\\\', '"': '\\"', '\n': '\\n', '\r': '\\r', '\t': '\\t'}
            s = '"' + ''.join(esc.get(c, '\\' + str(ord(c)).zfill(3) if ord(c) < 32 or ord(c) == 127 else c) for c in s) + '"'
        except UnicodeDecodeError:
            s = '"' + ''.join('\\' + str(b).zfill(3) for b in v) + '"'
        return N('str', [s])
    if isinstance(v, float) and not math.isfinite(v):
        return N('bin', ['/', atom(0 if math.isnan(v) else -1 if v < 0 else 1), atom(0)])
    return N('num', [num(v)])


class Dc:
    def __init__(self, rd, name):
        self.rd = rd
        self.name = name
        self.lim = max(10000, len(rd.buf) * 100)
        self.stp = 0
        self.dep = 0
        self.sps = {}
        self.fps = {}
        self.bps = {}
        for key, fn in rd.fun.items():
            if key in rd.tab:
                continue
            bs = fn.a[1]
            if len(bs) == 1 and bs[0].k == 'if' and fn.a[0]:
                self.bps[key] = fn
            elif any(z.k == 'for' for z in bs):
                self.sps[key] = self.strp(fn)
            elif any(z.k == 'ret' for z in bs) and not fn.a[0]:
                self.fps[key] = fn

    def tick(self):
        self.stp += 1
        if self.stp > self.lim:
            bad('decoder step limit exceeded')

    def ex(self, x, env, byte=None, ld=None):
        self.tick()
        self.dep += 1
        if self.dep > 120:
            bad('decoder expression depth exceeded')
        try:
            a = x.a
            if x.k in ('grp', 'cast'):
                return self.ex(a[0], env, byte, ld)
            if x.k == 'call':
                f = ung(a[0])
                if f.k == 'idx' and f.a[0].k == 'id' and f.a[0].a[0] == self.name:
                    ok, key = val(f.a[1], env)
                    if not ok:
                        bad('reader key expression unresolved')
                    args = [self.ex(q, env, byte, ld) for q in a[1]]
                    if key not in self.rd.fun:
                        bad('reader key ' + num(key) + ' absent at stream offset ' + str(int(self.rd.env[self.rd.pos] - 1)))
                    return self.get(int(key), args)
                if ld is not None and f.k == 'id' and f.a[0] == ld and len(a[1]) == 2:
                    v = [self.ex(q, env, byte, ld) for q in a[1]]
                    return math.ldexp(v[0], int(v[1]))
                if byte is not None:
                    return byte
                bad('decoder call target unresolved at line ' + str(x.ln))
            if x.k == 'id':
                if a[0] not in env:
                    bad('decoder variable ' + a[0].lower() + ' has no constant binding at stream offset ' + str(int(self.rd.env[self.rd.pos] - 1)))
                return env[a[0]]
            if x.k == 'bin':
                op = a[0]
                l = self.ex(a[1], env, byte, ld)
                if op == 'and' and not tru(l) or op == 'or' and tru(l):
                    return l
                r = self.ex(a[2], env, byte, ld)
                if op in ('and', 'or'):
                    return r
                return cv(N('bin', [op, atom(l), atom(r)]), {}, {})
            if x.k == 'un':
                if a[0] == '#' and ung(a[1]).k == 'id':
                    v = env.get(ung(a[1]).a[0])
                    if isinstance(v, (bytes, tuple, list, dict)):
                        return len(v)
                v = self.ex(a[1], env, byte, ld)
                return cv(N('un', [a[0], atom(v)]), {}, {})
            ok, v = val(x, env)
            if ok:
                return v
            bad('decoder arithmetic expression unresolved at line ' + str(x.ln))
        finally:
            self.dep -= 1

    def get(self, key, args=()):
        self.tick()
        if key in self.rd.tab:
            return self.rd.get(key)
        if key in self.bps:
            fn = self.bps[key]
            env = dict(self.rd.env)
            for i, p in enumerate(fn.a[0]):
                env[p.a[0]] = args[i] if i < len(args) else None
            br = fn.a[1][0]
            body = br.a[1]
            for cond, bs in br.a[0]:
                if tru(self.ex(cond, env)):
                    body = bs
                    break
            for z in body:
                if z.k == 'loc':
                    vals = [self.ex(q, env) for q in z.a[1]]
                    for n, v in zip(z.a[0], vals):
                        env[n.a[0]] = v
                elif z.k == 'ret':
                    return self.ex(z.a[0][0], env)
                else:
                    bad('bit reader expression record unresolved')
            bad('bit reader return expression absent')
        if key in self.sps:
            return self.strg(self.sps[key], args)
        if key in self.fps:
            return self.flt(self.fps[key])
        bad('reader plan absent for key ' + str(key))

    def strp(self, fn):
        bs = fn.a[1]
        lps = [z for z in bs if z.k == 'for']
        if len(lps) != 1:
            bad('string reader byte loop absent')
        loop = lps[0]
        mods = []
        sets = []
        for z in loop.a[2]:
            if z.k == 'set' and z.a[0][0].k == 'id':
                q = z.a[1][0]
                if any(y.k == 'call' for y in walk(q)):
                    mods.extend(y for y in walk(q) if y.k == 'bin' and y.a[0] == '%' and any(v.k == 'call' for v in walk(y)))
                else:
                    sets.append(z)
        if len(mods) != 1 or len(sets) != 1:
            bad('string reader byte arithmetic unresolved')
        lens = []
        for z in bs:
            if z is loop:
                break
            for q in walk(z):
                if q.k == 'call' and rkey(q, self.name) is not None:
                    lens.append(q)
        if len(lens) != 1:
            bad('string reader length field unresolved')
        return lens[0], mods[0], sets[0]

    def strg(self, plan, args):
        lenc, expr, upd = plan
        size = args[0] if args and args[0] is not None else self.ex(lenc, self.rd.env)
        pos = self.rd.env[self.rd.pos] - 1
        if size != int(size) or size < 0 or pos != int(pos):
            bad('string length or cursor is not integral')
        size, pos = int(size), int(pos)
        if size > len(self.rd.buf) - pos:
            bad('string field length ' + str(size) + ' exceeds ' + str(len(self.rd.buf) - pos) + ' remaining bytes at offset ' + str(pos))
        env = dict(self.rd.env)
        out = bytearray(size)
        for i in range(size):
            v = self.ex(expr, env, self.rd.buf[pos + i])
            if v != int(v) or not 0 <= v <= 255:
                bad('decoded string byte exceeds range at offset ' + str(pos + i))
            out[i] = int(v)
            v = self.ex(upd.a[1][0], env)
            env[upd.a[0][0].a[0]] = v
        self.rd.env[upd.a[0][0].a[0]] = env[upd.a[0][0].a[0]]
        self.rd.env[self.rd.pos] += size
        return bytes(out)

    def flt(self, fn):
        env = dict(self.rd.env)
        cond = None
        ret = None
        for z in fn.a[1]:
            if z.k == 'loc':
                vals = [self.ex(q, env) for q in z.a[1]]
                for n, v in zip(z.a[0], vals):
                    env[n.a[0]] = v
            elif z.k == 'if':
                cond = z
                break
        if cond is None:
            bad('float reader boundary conditions absent')
        for z in reversed(fn.a[1]):
            if z.k == 'ret':
                ret = z.a[0][0]
                break
        if ret is None:
            bad('float reader final expression absent')
        zero = cond.a[0][0]
        if tru(self.ex(zero[0], env)):
            body = zero[1]
            if len(body) != 1 or body[0].k != 'if':
                bad('float subnormal branch shape unresolved')
            inn = body[0]
            if tru(self.ex(inn.a[0][0][0], env)):
                r = inn.a[0][0][1][-1]
                return self.ex(r.a[0][0], env)
            for z in inn.a[1]:
                if z.k != 'set':
                    bad('float subnormal expression unresolved')
                for n, q in zip(z.a[0], z.a[1]):
                    env[n.a[0]] = self.ex(q, env)
        for c, bs in cond.a[0][1:]:
            if tru(self.ex(c, env)):
                r = bs[-1].a[0][0]
                x = ung(r)
                if x.k != 'bin' or x.a[0] != 'or':
                    bad('float infinity expression unresolved')
                left = ung(x.a[1])
                if left.k != 'bin' or left.a[0] != 'and':
                    bad('float infinity predicate unresolved')
                if tru(self.ex(left.a[1], env)):
                    prod = ung(left.a[2])
                    return math.copysign(math.inf, self.ex(prod.a[1], env))
                return math.nan
        cls = [q for q in walk(ret) if q.k == 'call']
        if len(cls) != 1 or ung(cls[0].a[0]).k != 'id':
            bad('float scale operation unresolved')
        return self.ex(ret, env, ld=ung(cls[0].a[0]).a[0])


class Sch:
    def __init__(self, ast, dc, ae=None):
        self.ae = Ae(ast) if ae is None else ae
        self.dc = dc
        self.fn = None
        self.name = None
        self.env = dict(dc.rd.env)
        self.ctab = None
        self.tags = {}
        self.acts = []
        for z in walk(ast):
            if z.k != 'lfn' or z.a[1].a[0]:
                continue
            name = z.a[0].a[0]
            cap = self.ae.out.get(id(z.a[1]), {}).get(dc.name)
            tab = cap.a[0] if isinstance(cap, V) and cap.k == 'bind' else None
            if not isinstance(tab, dict) or id(tab) in self.ae.bad or set(tab) != set(dc.rd.fun):
                continue
            if not all(isinstance(tab[k], V) and tab[k].k == 'afn' and tab[k].a[0] is fn for k, fn in dc.rd.fun.items()):
                continue
            if any(q.k == 'call' and ung(q.a[0]).k == 'id' and ung(q.a[0]).a[0] == name for q in walk(z.a[1])):
                if self.fn is not None:
                    bad('recursive prototype constructor binding ambiguous')
                self.fn = z.a[1]
                self.name = name
        if self.fn is None:
            bad('recursive prototype constructor absent')
        for name, cell in self.ae.out[id(self.fn)].items():
            v = cell.a[0]
            if name not in self.env and (v is None or type(v) in (bool, int, float, bytes)):
                self.env[name] = v
        for z in self.fn.a[1]:
            if z.k == 'loc':
                for n, q in zip(z.a[0], z.a[1]):
                    if q.k == 'tab' and q.a[0] and all(k is not None and ung(v).k == 'fn' for k, v in q.a[0]):
                        self.ctab = n.a[0]
                        for k, v in q.a[0]:
                            self.tags[int(self.dc.ex(k, self.env))] = ung(v)
                    elif rkey(q, dc.name) is not None:
                        self.acts.append(('count', n.a[0], q))
                    else:
                        ok, v = val(q, self.env)
                        if ok:
                            self.env[n.a[0]] = v
            elif z.k == 'set':
                n, q = z.a[0][0], z.a[1][0]
                if n.k == 'idx' and rkey(q, dc.name) is not None:
                    self.acts.append(('field', n.a[1], q))
            elif z.k == 'for':
                rec = any(q.k == 'call' and ung(q.a[0]).k == 'id' and ung(q.a[0]).a[0] == self.name for q in walk(z.a[2]))
                ins = any(q.k == 'tab' and any(k is not None and ung(v).k == 'fn' for k, v in q.a[0]) for q in walk(z.a[2]))
                self.acts.append(('child' if rec else 'ins' if ins else 'const', z, None))
        if not self.tags or not all(any(z[0] == k for z in self.acts) for k in ('child', 'ins', 'const')):
            bad('prototype record sections absent')

    def ext(self, fn):
        env = dict(self.env)
        src = None
        loop = None
        for z in fn.a[1]:
            if z.k == 'loc':
                for n, q in zip(z.a[0], z.a[1]):
                    if rkey(q, self.dc.name) is not None:
                        src = self.dc.ex(q, env)
                        env[n.a[0]] = src
                    else:
                        ok, v = val(q, env)
                        if ok:
                            env[n.a[0]] = v
            elif z.k == 'for':
                loop = z
        if src is None or loop is None:
            bad('constant string transform plan absent')
        mods = []
        upd = []
        ordr = []
        for z in loop.a[2]:
            if z.k != 'set':
                bad('constant string transform statement unresolved')
            q = z.a[1][0]
            if any(y.k == 'call' for y in walk(q)):
                mods = [y for y in walk(q) if y.k == 'bin' and y.a[0] == '%' and any(v.k == 'call' for v in walk(y))]
                ordr.append('byte')
            else:
                upd.append(z)
                ordr.append('upd')
        if len(mods) != 1 or len(upd) != 1:
            bad('constant string transform arithmetic unresolved')
        out = bytearray()
        for b in src:
            for k in ordr:
                if k == 'upd':
                    env[upd[0].a[0][0].a[0]] = self.dc.ex(upd[0].a[1][0], env)
                else:
                    v = self.dc.ex(mods[0], env, b)
                    out.append(int(v))
        return bytes(out)

    def con(self, loop, cnt, env):
        bs = loop.a[2]
        tag = None
        mod = None
        for z in bs:
            if z.k == 'loc':
                for q in z.a[1]:
                    if rkey(q, self.dc.name) is not None:
                        tag = q
                    if q.k == 'idx' and q.a[0].k == 'id' and q.a[0].a[0] == self.ctab:
                        if q.a[1].k == 'bin' and q.a[1].a[0] == '%':
                            mod = q.a[1].a[2]
        if tag is None or mod is None:
            bad('constant tag selector absent')
        mod = self.dc.ex(mod, env)
        out = {}
        for i in range(1, cnt + 1):
            key = int(self.dc.ex(tag, env) % mod)
            fn = self.tags.get(key)
            if fn is None:
                out[i] = None
                continue
            body = fn.a[1]
            if len(body) == 1 and body[0].k == 'ret':
                loc = dict(env)
                for p in fn.a[0]:
                    loc[p.a[0]] = ()
                out[i] = self.dc.ex(body[0].a[0][0], loc)
            else:
                out[i] = self.ext(fn)
        return out

    def ins(self, loop, cnt, env, con):
        bs = loop.a[2]
        if len(bs) != 2 or bs[0].k != 'loc' or bs[1].k != 'if':
            bad('instruction record selector shape unresolved')
        flag = bs[0].a[0][0].a[0]
        read = bs[0].a[1][0]
        br = bs[1].a[0][0]
        body = br[1]
        tab = None
        fmt = None
        rec = None
        out = {}
        for i in range(1, cnt + 1):
            loc = dict(env)
            loc[flag] = self.dc.ex(read, loc)
            if not tru(self.dc.ex(br[0], loc)):
                continue
            vals = {}
            for z in body:
                if z.k == 'loc':
                    for n, q in zip(z.a[0], z.a[1]):
                        if q.k == 'tab':
                            if q.a[0] and all(k is not None and ung(v).k == 'fn' for k, v in q.a[0]):
                                tab = {int(self.dc.ex(k, loc)): ung(v) for k, v in q.a[0]}
                            elif q.a[0] and all(k is None for k, v in q.a[0]):
                                rec = n.a[0]
                                vals = {j: self.dc.ex(v, loc) for j, (k, v) in enumerate(q.a[0], 1)}
                        else:
                            loc[n.a[0]] = self.dc.ex(q, loc)
                elif z.k == 'stmt':
                    call = ung(z.a[0])
                    if call.k != 'call' or ung(call.a[0]).k != 'idx' or tab is None:
                        bad('instruction operand dispatch absent')
                    idx = ung(call.a[0]).a[1]
                    fmt = int(self.dc.ex(idx, loc))
                    fn = tab.get(fmt)
                    if fn is None:
                        bad('instruction format key absent at offset ' + str(int(self.dc.rd.env[self.dc.rd.pos] - 1)))
                    for setn in fn.a[1]:
                        if setn.k != 'set':
                            bad('instruction operand assignment absent')
                        for n, q in zip(setn.a[0], setn.a[1]):
                            vals[self.dc.ex(n.a[1], loc)] = self.dc.ex(q, loc)
                elif z.k == 'if':
                    c, sets = z.a[0][0]
                    if tru(self.dc.ex(c, loc)):
                        for setn in sets:
                            n, q = setn.a[0][0], setn.a[1][0]
                            if n.k != 'idx' or q.k != 'idx' or q.a[1].k != 'idx':
                                bad('instruction constant substitution shape unresolved')
                            dest = self.dc.ex(n.a[1], loc)
                            src = self.dc.ex(q.a[1].a[1], loc)
                            if src not in vals:
                                bad('instruction constant source field absent')
                            key = vals[src]
                            vals[dest] = con.get(key)
                elif z.k == 'set':
                    pass
                else:
                    bad('instruction record statement unresolved')
            out[i] = vals
        return out

    def prs(self):
        root = {'h': {}, 'k': {}, 'i': {}, 'p': []}
        stk = [(root, dict(self.env), 0)]
        nump = 1
        while stk:
            self.dc.tick()
            pro, env, idx = stk.pop()
            if idx >= len(self.acts):
                continue
            k, n, q = self.acts[idx]
            stk.append((pro, env, idx + 1))
            if k == 'count':
                env[n] = self.dc.ex(q, env)
            elif k == 'field':
                pro['h'][int(self.dc.ex(n, env))] = self.dc.ex(q, env)
            else:
                beg = self.dc.ex(n.a[1][0], env)
                end = self.dc.ex(n.a[1][1], env)
                step = self.dc.ex(n.a[1][2], env) if len(n.a[1]) == 3 else 1
                if beg != int(beg) or end != int(end) or step != 1:
                    bad('prototype section count is not integral')
                cnt = max(0, int(end - beg + 1))
                if cnt > len(self.dc.rd.buf):
                    bad('prototype section count exceeds stream size at offset ' + str(int(self.dc.rd.env[self.dc.rd.pos] - 1)))
                if k == 'const':
                    pro['k'] = self.con(n, cnt, env)
                elif k == 'ins':
                    pro['i'] = self.ins(n, cnt, env, pro['k'])
                else:
                    nump += cnt
                    if nump > len(self.dc.rd.buf):
                        bad('prototype count exceeds stream size')
                    for j in range(cnt):
                        chd = {'h': {}, 'k': {}, 'i': {}, 'p': []}
                        pro['p'].append(chd)
                    for chd in reversed(pro['p']):
                        stk.append((chd, dict(self.env), 0))
        return root


class Hp:
    def __init__(self, ast, vm, env):
        self.vm = vm
        self.env = dict(env)
        self.base = dict(env)
        self.memo = {}
        self.stp = 0
        self.lim = max(10000, sum(1 for _ in walk(ast)) * 500)
        loop, ins, fet, op, fld = vm
        self.op = op.a[0]
        self.ins = ins.a[0]
        self.pc = ung(fet.a[1]).a[0]
        self.code = ung(fet.a[0]).a[0]
        self.fld = val(fld.a[1], env)[1]
        self.fn = None
        for fn in walk(ast):
            if fn.k == 'fn' and any(z is loop for z in fn.a[1]):
                self.fn = fn
                break
        if self.fn is None:
            bad('interpreter closure absent')
        for z in self.fn.a[1]:
            if z is loop:
                break
            if z.k == 'loc':
                for n in z.a[0]:
                    self.env.pop(n.a[0], None)
        self.env.pop(self.ins, None)
        self.env.pop(self.pc, None)
        self.env.pop(self.code, None)
        self.body = loop.a[1][2:]
        self.ctrl = {self.op}
        wr = {n.a[0] for z in walk(self.body) if z.k == 'set' for n in z.a[0] if n.k == 'id'}
        for z in walk(self.body):
            if z.k == 'wh':
                self.ctrl.update(n.a[0] for n in walk(z.a[0]) if n.k == 'id' and n.a[0] in wr)
        self.ctrl.discard(self.pc)
        self.ctrl.discard(self.ins)
        self.ctrl.discard(self.code)
        self.leaf = set()
        self.pick = False
        for q in walk(self.body):
            rows = []
            if q.k == 'wh' and self.test(q.a[0]):
                rows.append(q.a[1])
            elif q.k == 'if' and any(self.test(c) for c, b in q.a[0]):
                rows.extend(b for c, b in q.a[0])
                rows.append(q.a[1])
            for bs in rows:
                if bs and not any(z.k == 'wh' and self.test(z.a[0]) or z.k == 'if' and any(self.test(c) for c, b in z.a[0]) for z in bs):
                    self.leaf.add(id(bs))

    def test(self, cond):
        return any(q.k == 'id' and q.a[0] in self.ctrl for q in walk(cond))

    def blk(self, bs, env, scp=True, loc=None):
        if id(bs) in self.leaf:
            self.pick = True
        out = []
        loc = set() if loc is None else set(loc)
        sav = {}
        brk = False
        for z in bs:
            self.stp += 1
            if self.stp > self.lim:
                bad('handler specialization step limit exceeded')
            if z.k == 'break':
                brk = True
                break
            if z.k == 'loc':
                ns, es = z.a
                vals = [val(q, env) for q in es]
                for i, n in enumerate(ns):
                    key = n.a[0]
                    loc.add(key)
                    if key not in sav:
                        sav[key] = (key in env, env.get(key))
                    if i < len(vals) and vals[i][0]:
                        env[key] = vals[i][1]
                    else:
                        env.pop(key, None)
                out.append(z)
            elif z.k == 'set':
                ns, es, op = z.a
                knw = len(ns) == len(es) and all(n.k == 'id' and n.a[0] in self.ctrl and n.a[0] not in loc for n in ns)
                vals = []
                if knw:
                    for n, q in zip(ns, es):
                        if op != '=':
                            q = N('bin', [op[:-1], n, q])
                        vals.append(val(q, env))
                    knw = all(ok for ok, v in vals)
                if knw:
                    for n, (ok, v) in zip(ns, vals):
                        env[n.a[0]] = v
                else:
                    if any(n.k != 'id' or n.a[0] not in self.ctrl | {self.pc, self.ins, self.code} for n in ns):
                        self.pick = True
                    out.append(z)
                    for n in ns:
                        if n.k == 'id':
                            env.pop(n.a[0], None)
            elif z.k == 'wh':
                ok, v = val(z.a[0], env)
                if ok:
                    if tru(v):
                        body, stop = self.blk(z.a[1], env, loc=loc)
                        if not stop:
                            bad('constant dispatch branch has no static exit at line ' + str(z.ln))
                        if body:
                            out.append(N('do', [body], z.s, z.e, z.ln))
                else:
                    out.append(z)
            elif z.k == 'if':
                sel = None
                knw = True
                for c, body in z.a[0]:
                    ok, v = val(c, env)
                    if not ok:
                        knw = False
                        break
                    if tru(v):
                        sel = body
                        break
                if knw:
                    body, stop = self.blk(sel if sel is not None else z.a[1], env, loc=loc)
                    if body:
                        out.append(N('do', [body], z.s, z.e, z.ln))
                    if stop:
                        brk = True
                        break
                else:
                    out.append(z)
                    for q in walk(z):
                        if q.k == 'set':
                            for n in q.a[0]:
                                if n.k != 'id' or n.a[0] not in self.ctrl | {self.pc, self.ins, self.code}:
                                    self.pick = True
                                if n.k == 'id':
                                    env.pop(n.a[0], None)
                        elif q.k in ('stmt', 'ret', 'for'):
                            self.pick = True
            else:
                if z.k in ('stmt', 'ret', 'for'):
                    self.pick = True
                out.append(z)
        if scp:
            for key, (had, vv) in sav.items():
                if had:
                    env[key] = vv
                else:
                    env.pop(key, None)
        return out, brk

    def get(self, op):
        if op not in self.memo:
            env = dict(self.env)
            env[self.op] = op
            self.pick = False
            body, brk = self.blk(self.body, env)
            if self.leaf and not self.pick:
                bad('opcode dispatch has no reachable handler for opcode ' + num(op))
            self.memo[op] = body
        return self.memo[op]


class V:
    def __init__(self, k, a=()):
        self.k = k
        self.a = list(a)


class Ae:
    def __init__(self, ast):
        self.unk = V('unknown')
        self.out = {}
        self.cal = {}
        self.glob = {}
        self.act = set()
        self.bad = {}
        self.kact = set()
        self.stp = 0
        self.lim = max(10000, sum(1 for q in walk(ast)) * 256)
        z1 = {id(q[0]) for q in scan(ast)[1]}
        self.vms = {id(q) for q in walk(ast) if q.k == 'fn' and any(id(z) in z1 for z in q.a[1])}
        self.blk(ast, {})

    def tick(self):
        self.stp += 1
        if self.stp > self.lim:
            bad('lexical alias analysis budget exceeded')

    def one(self, v):
        return (v.a[0][0] if v.a[0] else None) if isinstance(v, V) and v.k == 'many' else v

    def tkey(self, v):
        if type(v) is bool:
            return ('bool', v)
        if isinstance(v, (V, dict)) or type(v) is float and math.isnan(v):
            return self.unk
        return v

    def genv(self, v):
        if not isinstance(v, V):
            return False
        if v.k == 'native':
            q = ung(v.a[0])
            return len(v.a) > 1 and v.a[1] == 'genv' or q.k == 'id' and q.a[0] == 'getfenv'
        if v.k != 'afn':
            return False
        fn, cap = v.a
        if fn.a[0] or len(fn.a[1]) != 1 or fn.a[1][0].k != 'ret' or len(fn.a[1][0].a[0]) != 1:
            return False
        q = ung(fn.a[1][0].a[0][0])
        if q.k != 'id' or q.a[0] != '_ENV':
            return False
        cell = cap.get('_ENV', self.glob.get('_ENV'))
        return cell is None or isinstance(cell.a[0], V) and cell.a[0].k == 'global'

    def yes(self, v):
        if isinstance(v, V) and v.k not in ('afn', 'global'):
            return None
        return tru(v)

    def args(self, qs, env):
        out = []
        for i, q in enumerate(qs):
            v = self.ex(q, env)
            if isinstance(v, V) and v.k == 'many' and i == len(qs) - 1:
                out.extend(v.a[0])
            else:
                out.append(self.one(v))
        return out

    def ex(self, x, env):
        self.tick()
        k, a = x.k, x.a
        if k in ('num', 'str', 'nil', 'true', 'false'):
            return cv(x, {}, {})
        if k == 'id':
            cell = env.get(a[0], self.glob.get(a[0]))
            if cell is None and a[0] == '_ENV':
                return V('global')
            return cell.a[0] if cell is not None else V('native', [x])
        if k in ('grp', 'cast'):
            return self.one(self.ex(a[0], env))
        if k == 'fn':
            cap = dict(env)
            self.out[id(x)] = cap
            return V('afn', [x, cap])
        if k == 'tab':
            tab, idx = {}, 1
            for i, (key, q) in enumerate(a[0]):
                v = self.ex(q, env)
                if key is None:
                    vs = v.a[0] if isinstance(v, V) and v.k == 'many' and i == len(a[0]) - 1 else [self.one(v)]
                    for item in vs:
                        if item is not None:
                            tab[idx] = item
                        idx += 1
                else:
                    key = key.a[0].encode() if key.k == 'key' else self.tkey(self.one(self.ex(key, env)))
                    if isinstance(key, V) or key is None:
                        return self.unk
                    v = self.one(v)
                    if v is not None:
                        tab[key] = v
                    else:
                        tab.pop(key, None)
            return tab
        if k in ('idx', 'dot'):
            obj = self.one(self.ex(a[0], env))
            key = a[1].a[0].encode() if k == 'dot' else self.one(self.ex(a[1], env))
            if isinstance(key, (V, dict)) or key is None:
                return self.unk
            if isinstance(obj, dict):
                key = self.tkey(key)
                return obj.get(key, self.unk) if not isinstance(key, V) and id(obj) not in self.bad else self.unk
            if isinstance(obj, V) and obj.k in ('native', 'global'):
                name = key.decode('ascii', errors='ignore') if isinstance(key, bytes) else ''
                if isinstance(key, bytes) and re.fullmatch('[A-Za-z_][A-Za-z_0-9]*', name) and name.encode() == key:
                    node = N('id', [name]) if obj.k == 'global' else N('dot', [obj.a[0], N('id', [name])])
                elif obj.k == 'native':
                    node = N('idx', [obj.a[0], atom(key)])
                else:
                    return self.unk
                return V('native', [node])
            return self.unk
        if k == 'un':
            v = self.one(self.ex(a[1], env))
            if a[0] == 'not':
                yes = self.yes(v)
                return self.unk if yes is None else not yes
            if a[0] == '#' and isinstance(v, dict):
                if id(v) in self.bad or set(v) != set(range(1, len(v) + 1)) or any(self.yes(q) is None for q in v.values()):
                    return self.unk
                return len(v)
            if isinstance(v, V):
                return self.unk
            ok, v = val(N('un', [a[0], atom(v)]))
            return v if ok else self.unk
        if k == 'bin':
            l = self.one(self.ex(a[1], env))
            if a[0] in ('and', 'or'):
                yes = self.yes(l)
                if yes is not None:
                    return self.ex(a[2], env) if (yes and a[0] == 'and') or (not yes and a[0] == 'or') else l
                r = self.one(self.ex(a[2], env))
                if a[0] == 'or' and self.genv(l) and self.genv(r):
                    z16 = r.a[0]
                    return V('native', [N('bin', [a[0], l.a[0], z16]), 'genv'])
                if isinstance(l, V) and l.k == 'native' and isinstance(r, V) and r.k == 'native':
                    return V('native', [N('bin', [a[0], l.a[0], r.a[0]])])
                return self.unk
            r = self.one(self.ex(a[2], env))
            if isinstance(l, (V, dict)) or isinstance(r, (V, dict)):
                return self.unk
            ok, v = val(N('bin', [a[0], atom(l), atom(r)]))
            return v if ok else self.unk
        if k in ('call', 'mcall'):
            if k == 'mcall':
                obj = self.one(self.ex(a[0], env))
                args = [obj] + self.args(a[2], env)
                f = V('native', [N('dot', [N('id', ['string']), a[1]])]) if isinstance(obj, bytes) else self.unk
            else:
                f = self.one(self.ex(a[0], env))
                args = self.args(a[1], env)
            if isinstance(f, V) and f.k == 'afn':
                fn, cap = f.a
                self.cal[id(x)] = fn
                loc = dict(cap)
                for i, p in enumerate(fn.a[0]):
                    if p.k == 'id':
                        loc[p.a[0]] = V('bind', [args[i] if i < len(args) else None])
                if id(fn) in self.vms:
                    return self.unk
                if id(fn) in self.act:
                    if id(fn) not in self.kact:
                        self.kact.add(id(fn))
                        try:
                            self.kill(fn.a[1], loc)
                        finally:
                            self.kact.remove(id(fn))
                    return self.unk
                self.act.add(id(fn))
                try:
                    if len(fn.a[1]) == 1 and fn.a[1][0].k == 'ret' and len(fn.a[1][0].a[0]) == 1:
                        return self.ex(fn.a[1][0].a[0][0], loc)
                    self.blk(fn.a[1], loc)
                finally:
                    self.act.remove(id(fn))
                return self.unk
            if isinstance(f, V) and f.k == 'native':
                node = f.a[0]
                name = Em().ex(node)
                if self.genv(f) and not args:
                    return V('global')
                if name == 'type' and len(args) == 1:
                    v = args[0]
                    typ = 'string' if isinstance(v, bytes) else 'boolean' if type(v) is bool else 'number' if type(v) in (int, float) else 'nil' if v is None else 'table' if isinstance(v, dict) or isinstance(v, V) and v.k == 'global' else 'function' if isinstance(v, V) and v.k == 'afn' else None
                    return typ.encode() if typ else self.unk
                if name in ('string.sub', 'string.find') and args and isinstance(args[0], bytes):
                    buf = args[0]
                    if name == 'string.sub' and len(args) in (2, 3) and all(type(v) in (int, float) and int(v) == v for v in args[1:]):
                        beg = int(args[1]); end = int(args[2]) if len(args) == 3 else len(buf)
                        beg = len(buf) + beg + 1 if beg < 0 else beg
                        end = len(buf) + end + 1 if end < 0 else end
                        return buf[max(1, beg) - 1:max(0, end)]
                    if name == 'string.find' and len(args) == 2 and isinstance(args[1], bytes) and not re.search(rb'[\^$()%\[\]*+?.-]', args[1]):
                        pos = buf.find(args[1])
                        return V('many', [[] if pos < 0 else [pos + 1, pos + len(args[1])]])
            for v in args:
                if isinstance(v, dict):
                    self.bad[id(v)] = v
            return self.unk
        return self.unk

    def eff(self, x, env):
        todo = [x]
        while todo:
            self.tick()
            q = todo.pop()
            if isinstance(q, (list, tuple)):
                todo.extend(q)
                continue
            if not isinstance(q, N) or q.k == 'fn':
                continue
            if q.k in ('call', 'mcall'):
                args = q.a[1] if q.k == 'call' else [q.a[0]] + q.a[2]
                for arg in args:
                    arg = ung(arg)
                    if arg.k == 'id':
                        v = self.one(self.ex(arg, env))
                        if isinstance(v, dict):
                            self.bad[id(v)] = v
                cal = ung(q.a[0])
                if q.k == 'call' and cal.k == 'id':
                    f = self.one(self.ex(cal, env))
                    if isinstance(f, V) and f.k == 'afn' and id(f.a[0]) not in self.kact:
                        fn, cap = f.a
                        loc = dict(cap)
                        for p in fn.a[0]:
                            loc[p.a[0]] = V('bind', [self.unk])
                        self.kact.add(id(fn))
                        try:
                            self.kill(fn.a[1], loc)
                        finally:
                            self.kact.remove(id(fn))
            todo.extend(q.a)

    def kill(self, bs, env):
        todo = [(bs if isinstance(bs, list) else [bs], dict(env))]
        while todo:
            body, loc = todo.pop()
            for q in body:
                self.tick()
                a = q.a
                if q.k in ('loc', 'set'):
                    self.eff(a[1], loc)
                    if q.k == 'set':
                        self.eff([n for n in a[0] if n.k != 'id'], loc)
                elif q.k in ('stmt', 'ret'):
                    self.eff(a[0], loc)
                elif q.k == 'if':
                    self.eff([cond for cond, part in a[0]], loc)
                elif q.k in ('for', 'iter'):
                    self.eff(a[1], loc)
                elif q.k == 'wh':
                    self.eff(a[0], loc)
                elif q.k == 'rep':
                    self.eff(a[1], loc)
                if q.k == 'loc':
                    vals = [self.one(self.ex(v, loc)) if ung(v).k in ('id', 'num', 'str', 'nil', 'true', 'false') else self.unk for v in a[1]]
                    for i, n in enumerate(a[0]):
                        loc[n.a[0]] = V('bind', [vals[i] if i < len(vals) else None])
                elif q.k == 'lfn':
                    loc[a[0].a[0]] = V('bind', [self.unk])
                elif q.k == 'set':
                    for n in a[0]:
                        if n.k == 'id':
                            cell = loc.get(n.a[0], self.glob.get(n.a[0]))
                            if cell is not None:
                                cell.a[0] = self.unk
                        elif n.k in ('idx', 'dot'):
                            obj = self.one(self.ex(n.a[0], loc))
                            if isinstance(obj, dict):
                                self.bad[id(obj)] = obj
                elif q.k == 'if':
                    todo.extend((part, dict(loc)) for cond, part in a[0])
                    todo.append((a[1], dict(loc)))
                elif q.k in ('for', 'iter'):
                    sub = dict(loc)
                    for n in a[0]:
                        sub[n.a[0]] = V('bind', [self.unk])
                    todo.append((a[2], sub))
                elif q.k == 'wh':
                    todo.append((a[1], dict(loc)))
                elif q.k == 'rep':
                    todo.append((a[0], dict(loc)))
                elif q.k == 'do':
                    todo.append((a[0], dict(loc)))

    def blk(self, bs, env):
        for q in bs:
            self.tick()
            a = q.a
            if q.k in ('loc', 'set'):
                dest = []
                for n in a[0]:
                    if n.k in ('idx', 'dot'):
                        obj = self.one(self.ex(n.a[0], env))
                        key = n.a[1].a[0].encode() if n.k == 'dot' else self.one(self.ex(n.a[1], env))
                        dest.append((obj, self.tkey(key)))
                    else:
                        dest.append(None)
                vals = self.args(a[1], env)
                for i, n in enumerate(a[0]):
                    v = vals[i] if i < len(vals) else None
                    if n.k == 'id':
                        if q.k == 'loc':
                            env[n.a[0]] = V('bind', [v])
                        elif n.a[0] in env:
                            env[n.a[0]].a[0] = v
                        else:
                            self.glob[n.a[0]] = V('bind', [v])
                            env[n.a[0]] = self.glob[n.a[0]]
                    elif dest[i] is not None:
                        obj, key = dest[i]
                        if isinstance(obj, dict):
                            if isinstance(key, (V, dict)) or key is None:
                                self.bad[id(obj)] = obj
                            elif v is None:
                                obj.pop(key, None)
                            else:
                                obj[key] = v
            elif q.k == 'lfn':
                cell = V('bind', [self.unk])
                env[a[0].a[0]] = cell
                cell.a[0] = self.ex(a[1], env)
            elif q.k == 'stmt':
                self.ex(a[0], env)
            elif q.k == 'ret':
                self.args(a[0], env)
                break
            elif q.k == 'do':
                self.blk(a[0], dict(env))
            elif q.k == 'if':
                z0 = True
                for c, body in a[0]:
                    yes = self.yes(self.one(self.ex(c, env)))
                    if yes is None:
                        z0 = False
                        break
                    if yes:
                        self.blk(body, dict(env))
                        break
                else:
                    self.blk(a[1], dict(env))
                if not z0:
                    self.kill(q, env)
            elif q.k in ('for', 'iter', 'wh', 'rep'):
                self.kill(q, env)


class Fx:
    def __init__(self, ast, hp, sc, pro, fid=0, ups=None, ctx=None, pool=None, link=None, rsv=None):
        self.hp = hp
        self.kw = Prs([]).kw
        self.sc = sc
        self.pro = pro
        self.fid = fid
        self.ups = {} if ups is None else ups
        self.ast = ast
        self.regs = set()
        self.tem0 = 0
        self.hois = []
        self.pac0 = {}
        self.pers = set()
        self.curp = 0
        self.stp = 0
        self.lim = max(10000, len(pro['i']) * 5000)
        self.env = dict(hp.base)
        self.pool = {} if pool is None else pool
        self.rsv = set() if rsv is None else rsv
        if ctx is not None:
            for name, cell in ctx.items():
                v = cell.a[0]
                if isinstance(v, V) and v.k == 'native':
                    self.env[name] = v
                elif name not in self.env:
                    self.env[name] = V('pending', [name])
        self.reg = None
        self.ctor = None
        self.rol0 = {}
        self.npar = None
        self.gph = {}
        self.clos = []
        self.cfld = set()
        self.cels = []
        self.vpre = []
        self.raw = None
        self.varg = None
        self.mgmt = set()
        if hasattr(hp, 'meta'):
            self.reg, mgmt, self.ctor, paks, args = hp.meta
            self.mgmt = set(mgmt)
            self.layo()
            for name in paks:
                self.env[name] = V('pack')
            self.env[self.ctor.a[0].a[0]] = V('interp')
        else:
            freq = {}
            paks = []
            for body in hp.memo.values():
                for z in walk(body):
                    if z.k != 'set':
                        continue
                    for n in z.a[0]:
                        if n.k == 'idx' and n.a[0].k == 'id' and any(q.k == 'id' and q.a[0] == hp.ins for q in walk(n.a[1])):
                            name = n.a[0].a[0]
                            freq[name] = freq.get(name, 0) + 1
                        if n.k == 'idx' and n.a[0].k == 'id':
                            idx = ung(n.a[1])
                            if idx.k == 'bin' and idx.a[0] == '+':
                                lhs = ung(idx.a[1])
                                if lhs.k == 'un' and lhs.a[0] == '#' and ung(lhs.a[1]).k == 'id' and ung(lhs.a[1]).a[0] == n.a[0].a[0]:
                                    self.mgmt.add(n.a[0].a[0])
            if not freq:
                bad('register file store shape absent')
            self.reg = max(freq, key=freq.get)
            self.layo()
            for z in walk(ast):
                if z.k == 'lfn':
                    fn = z.a[1]
                    if any(q.k == 'ret' and any(ung(v) is hp.fn for v in q.a[0]) for q in fn.a[1]):
                        self.ctor = z
                    if len(fn.a[1]) == 1 and fn.a[1][0].k == 'ret':
                        es = fn.a[1][0].a[0]
                        if len(es) == 2 and es[0].k == 'tab' and any(v.k == '...' for k, v in es[0].a[0]):
                            self.env[z.a[0].a[0]] = V('pack')
                            paks.append(z.a[0].a[0])
            if self.ctor is None:
                bad('interpreter constructor binding absent')
            name = self.ctor.a[0].a[0]
            self.env[name] = V('interp')
            cal0 = [q for q in walk(ast) if q.k == 'call' and ung(q.a[0]).k == 'id' and ung(q.a[0]).a[0] == name and any(v.k == 'call' and ung(v.a[0]).k == 'id' and ung(v.a[0]).a[0] == sc.name for v in q.a[1])]
            if link is not None:
                cal0 = [q for q in cal0 if link.get(id(q)) is self.ctor.a[1]]
            if not cal0:
                bad('prototype invocation binding absent')
            args = cal0[0].a[1]
            hp.meta = (self.reg, frozenset(self.mgmt), self.ctor, tuple(paks), args)
        ps = self.ctor.a[1].a[0]
        for p, q in zip(ps, args):
            if q.k == 'call' and ung(q.a[0]).k == 'id' and ung(q.a[0]).a[0] == sc.name:
                v = V('proto')
            elif q.k == 'tab':
                v = V('up', [self.ups])
            else:
                v = V('global')
            self.rol0[p.a[0]] = v.k
            self.env[p.a[0]] = v
        for z in self.ctor.a[1].a[1]:
            if z.k == 'ret':
                break
            if z.k == 'loc':
                vals = [self.ex(q, self.env) for q in z.a[1]]
                for n, v in zip(z.a[0], vals):
                    self.env[n.a[0]] = v
        for z in hp.fn.a[1]:
            if z is hp.vm[0]:
                break
            if z.k == 'for':
                for q in walk(z.a[2]):
                    if q.k == 'if':
                        for c, body in q.a[0]:
                            c = ung(c)
                            if c.k == 'bin' and c.a[0] == '>=':
                                v = self.ex(c.a[2], self.env)
                                if type(v) in (int, float):
                                    self.npar = int(v)
                if self.npar is not None and len(z.a[0]) == 1:
                    loc = dict(self.env)
                    loc[z.a[0][0].a[0]] = self.npar
                    for q in walk(z.a[2]):
                        if q.k != 'set' or len(q.a[0]) != 1 or len(q.a[1]) != 1:
                            continue
                        lhs, rhs = q.a[0][0], ung(q.a[1][0])
                        if lhs.k != 'idx' or lhs.a[0].k != 'id' or lhs.a[0].a[0] == self.reg or rhs.k != 'idx':
                            continue
                        obj = self.ex(rhs.a[0], loc)
                        if not isinstance(obj, V) or obj.k != 'raw':
                            continue
                        beg = self.ex(lhs.a[1], loc)
                        src = self.ex(rhs.a[1], loc)
                        if type(beg) in (int, float) and int(beg) == beg and src == self.npar + 1:
                            self.env[lhs.a[0].a[0]] = V('vargs', [int(beg)])
                continue
            if z.k == 'loc':
                for n, q in zip(z.a[0], z.a[1]):
                    if n.a[0] == self.reg:
                        self.env[n.a[0]] = V('regs')
                    elif n.a[0] in self.mgmt:
                        self.env[n.a[0]] = V('upctx')
                    else:
                        try:
                            self.env[n.a[0]] = self.ex(q, self.env)
                        except Err:
                            self.env[n.a[0]] = V('pending', [n.a[0]])
            elif z.k == 'set':
                for n, q in zip(z.a[0], z.a[1]):
                    if n.k == 'id':
                        if z.a[2] != '=':
                            q = N('bin', [z.a[2][:-1], n, q])
                        try:
                            self.env[n.a[0]] = self.ex(q, self.env)
                        except Err:
                            self.env[n.a[0]] = V('pending', [n.a[0]])
        for body in hp.memo.values():
            for z in walk(body):
                if z.k == 'call' and len(z.a[1]) == 3 and z.a[1][0].k == 'id' and z.a[1][0].a[0] == self.reg and z.a[1][2].k == 'id':
                    name = z.a[1][2].a[0]
                    if name in self.env:
                        self.pers.add(name)
        self.env[hp.code] = V('code')
        self.env[hp.pc] = 1
        self.env[hp.ins] = pro['i'].get(1)
        if self.npar is None:
            bad('prototype parameter count binding absent')

    def tick(self):
        self.stp += 1
        if self.stp > self.lim:
            bad('instruction lifting step limit exceeded')

    def layo(self):
        self.lay = {}
        self.kbas = 0
        rol0 = {}
        for k, loop, q in self.sc.acts:
            if k not in ('child', 'ins'):
                continue
            sets = [z for z in walk(loop.a[2]) if z.k == 'set' and z.a[0][0].k == 'idx']
            if not sets:
                continue
            dst = sets[-1].a[0][0]
            if dst.a[0].k == 'id':
                rol0[dst.a[0].a[0]] = k
            if k == 'child':
                env = dict(self.sc.env)
                env[loop.a[0][0].a[0]] = cv(loop.a[1][0], env, {})
                self.kbas = int(cv(dst.a[1], env, {}))
        ret = self.sc.fn.a[1][-1]
        if ret.k != 'ret' or len(ret.a[0]) != 1 or ret.a[0][0].k != 'id':
            bad('prototype layout return table absent')
        name = ret.a[0][0].a[0]
        tab = None
        for z in self.sc.fn.a[1]:
            if z.k == 'loc':
                for n, q in zip(z.a[0], z.a[1]):
                    if n.a[0] == name and q.k == 'tab':
                        tab = q
        if tab is None:
            bad('prototype layout constructor absent')
        for i, (key, v) in enumerate(tab.a[0], 1):
            if v.k == 'id' and v.a[0] in rol0:
                self.lay[i] = V('code' if rol0[v.a[0]] == 'ins' else 'kids')
            else:
                self.lay[i] = None
        self.lay.update(self.pro['h'])

    def slot(self, idx):
        if type(idx) not in (int, float) or idx != int(idx) or idx < 0:
            bad('register index lifting pending')
        idx = int(idx)
        self.regs.add(idx)
        return N('id', ['l_' + str(self.fid) + '_' + str(idx)])

    def temp(self):
        self.tem0 += 1
        return N('id', ['var_' + str(self.fid) + '_' + str(self.tem0)])

    def upfn(self, q):
        q = ung(q)
        if q.k == 'id':
            return q.a[0] == 'unpack'
        if q.k == 'dot':
            return q.a[0].k == 'id' and q.a[0].a[0] == 'table' and q.a[1].a[0] == 'unpack'
        return q.k == 'bin' and q.a[0] == 'or' and self.upfn(q.a[1]) and self.upfn(q.a[2])

    def lin(self, q, name):
        self.tick()
        q = ung(q)
        if q.k == 'id' and q.a[0] == name:
            return 1, 0
        ok, v = val(q)
        if ok and type(v) in (int, float):
            return 0, v
        if q.k == 'bin' and q.a[0] in ('+', '-'):
            a, b = self.lin(q.a[1], name)
            c, d = self.lin(q.a[2], name)
            sign = 1 if q.a[0] == '+' else -1
            return a + sign * c, b + sign * d
        bad('dynamic range index expression unresolved')

    def vpak(self):
        if self.varg is None:
            if self.npar is None:
                bad('variadic parameter boundary unresolved')
            self.raw, self.varg = self.temp(), self.temp()
            pack = self.nx(V('native', [N('dot', [N('id', ['table']), N('id', ['pack'])])]))
            opts = [v for v in self.env.values() if isinstance(v, V) and v.k == 'native' and self.upfn(v.a[0])]
            if not opts:
                bad('variadic unpack helper unresolved')
            unpk = self.nx(opts[0])
            cnt = N('dot', [self.raw, N('id', ['n'])])
            vals = N('call', [unpk, [self.raw, atom(self.npar + 1), cnt]])
            self.vpre = [N('loc', [[self.raw], [N('call', [pack, [N('...')]])]]), N('loc', [[self.varg], [N('call', [pack, [vals]])]]), N('set', [[N('dot', [self.varg, N('id', ['n'])])], [N('bin', ['-', cnt, atom(self.npar)])], '='])]
        return self.varg

    def nx(self, v):
        if isinstance(v, N):
            return v
        if isinstance(v, V):
            if v.k == 'native':
                key = Em().ex(v.a[0])
                if key not in self.pool:
                    name = 'var_0_' + str(len(self.pool) + 1)
                    while name in self.rsv:
                        name += '_'
                    self.rsv.add(name)
                    self.pool[key] = (N('id', [name]), v.a[0])
                return self.pool[key][0]
            if v.k == 'array':
                return v.a[0]
            if v.k == 'count':
                base = N('dot', [v.a[0], N('id', ['n'])])
                return base if v.a[1] == 0 else N('bin', ['+', base, atom(v.a[1])])
            if v.k == 'table':
                fs = []
                for k, q in v.a[0].items():
                    fs.append([atom(k), self.nx(q)])
                return N('tab', [fs])
            bad('runtime expression lifting pending for ' + v.k)
        if isinstance(v, dict):
            bad('instruction record escaped into runtime expression')
        return atom(v)

    def ex(self, x, env):
        self.tick()
        k, a = x.k, x.a
        if k in ('grp', 'cast'):
            v = self.ex(a[0], env)
            return N('grp', [v]) if k == 'grp' and isinstance(v, N) and v.k == 'call' else v
        if k == 'id':
            if a[0] in self.pers and a[0] not in env.get('$shadow', ()) and a[0] not in env.get('$def', ()):
                env['$use'] = env.get('$use', frozenset()) | {a[0]}
            v = env.get(a[0], N('id', [a[0]]))
            if isinstance(v, V) and v.k == 'argc' and self.curp:
                return V('count', [self.vpak(), v.a[0] + self.npar])
            return v
        if k in ('num', 'str', 'true', 'false', 'nil'):
            return cv(x, {}, {})
        if k == '...':
            return V('varargs')
        if k == 'fn':
            return V('fn', [x, dict(env)])
        if k == 'tab':
            if len(a[0]) == 1 and a[0][0][0] is None and a[0][0][1].k == '...':
                return V('raw')
            tab = {}
            rows = []
            idx = 1
            for key, q in a[0]:
                seq = key is None
                if seq:
                    key = idx
                    idx += 1
                elif key.k == 'key':
                    key = key.a[0].encode()
                else:
                    key = self.ex(key, env)
                v = self.ex(q, env)
                tab[key] = v
                rows.append((seq, key, v))
            if any(isinstance(key, N) or isinstance(q, N) or isinstance(q, V) and q.k == 'array' for seq, key, q in rows):
                fs = [[None if seq else self.nx(key), self.nx(q)] for seq, key, q in rows]
                return V('array', [N('tab', [fs])])
            return V('table', [tab])
        if k in ('idx', 'dot'):
            obj = self.ex(a[0], env)
            key = self.ex(a[1], env) if k == 'idx' else a[1].a[0].encode()
            if isinstance(obj, dict):
                if isinstance(key, (N, V)):
                    bad('instruction field index unresolved')
                return obj.get(key)
            if isinstance(obj, V):
                if obj.k == 'regs':
                    if isinstance(key, N) and '$range' in env:
                        temp, idx, base = env['$range']
                        z9, off = self.lin(key, idx.a[0])
                        if z9 != 1 or off != base - 1:
                            bad('dynamic register range access unresolved')
                        return N('idx', [temp, idx])
                    return self.slot(key)
                if obj.k == 'proto':
                    return self.lay.get(key)
                if obj.k == 'code':
                    if key not in self.pro['i']:
                        bad('instruction fetch absent at index ' + str(key))
                    return self.pro['i'][key]
                if obj.k == 'kids':
                    if type(key) not in (int, float) or not math.isfinite(key) or key != int(key):
                        bad('child prototype index is not integral')
                    idx = int(key) - self.kbas
                    if idx < 0 or idx >= len(self.pro['p']):
                        bad('child prototype index exceeds table')
                    return V('child', [idx])
                if obj.k == 'global':
                    if isinstance(key, bytes):
                        try:
                            name = key.decode('ascii')
                        except UnicodeDecodeError:
                            name = ''
                        if re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', name) and name not in self.kw:
                            return N('id', [name])
                        return N('id', ['\0' + key.decode('utf-8', 'surrogateescape')])
                    return N('idx', [N('call', [N('id', ['getfenv']), []]), self.nx(key)])
                if obj.k == 'up':
                    if key not in obj.a[0]:
                        bad('upvalue binding lifting pending for index ' + str(key))
                    return obj.a[0][key]
                if obj.k == 'table':
                    return obj.a[0].get(key)
                if obj.k == 'vargs':
                    idx = key - obj.a[0] + 1 if type(key) in (int, float) else N('bin', ['+', N('bin', ['-', self.nx(key), atom(obj.a[0])]), atom(1)])
                    return N('idx', [self.vpak(), self.nx(idx)])
                if obj.k in ('results', 'array'):
                    return N('idx', [obj.a[0], self.nx(key)])
                bad('table index lifting pending for ' + obj.k)
            return N('idx', [self.nx(obj), self.nx(key)])
        if k == 'un':
            v = self.ex(a[1], env)
            if isinstance(v, V) and v.k == 'table' and a[0] == '#':
                return len(v.a[0])
            if not isinstance(v, (N, V, dict)):
                ok, res = val(N('un', [a[0], atom(v)]))
                if ok:
                    return res
            return N('un', [a[0], self.nx(v)])
        if k == 'bin':
            l = self.ex(a[1], env)
            if not isinstance(l, (N, V, dict)) and a[0] in ('and', 'or'):
                if a[0] == 'and' and not tru(l) or a[0] == 'or' and tru(l):
                    return l
                return self.ex(a[2], env)
            r = self.ex(a[2], env)
            if isinstance(l, V) and l.k == 'argc' and type(r) in (int, float) and a[0] in ('+', '-'):
                return V('argc', [l.a[0] + (r if a[0] == '+' else -r)])
            if isinstance(l, V) and l.k == 'count' and type(r) in (int, float) and a[0] in ('+', '-'):
                return V('count', [l.a[0], l.a[1] + (r if a[0] == '+' else -r)])
            if isinstance(r, V) and r.k == 'count' and type(l) in (int, float) and a[0] == '+':
                return V('count', [r.a[0], r.a[1] + l])
            if not isinstance(l, (N, V, dict)) and not isinstance(r, (N, V, dict)):
                ok, res = val(N('bin', [a[0], atom(l), atom(r)]))
                if ok:
                    return res
            return N('bin', [a[0], self.nx(l), self.nx(r)])
        if k == 'call':
            f = self.ex(a[0], env)
            args = [self.ex(q, env) for q in a[1]]
            if isinstance(f, V) and f.k == 'native' and f.a[0].k == 'id' and f.a[0].a[0] == 'select' and len(args) == 2 and args[0] == b'#' and isinstance(args[1], V) and args[1].k == 'varargs':
                return V('argc', [0])
            if args and isinstance(args[0], V) and args[0].k == 'regs':
                if not isinstance(f, V) or f.k != 'native' or not self.upfn(f.a[0]):
                    bad('register range callee semantics unresolved')
                if len(args) == 3 and type(args[1]) in (int, float) and isinstance(args[2], V) and args[2].k == 'count':
                    temp, shif = args[2].a
                    base = int(shif + 1)
                    beg = int(args[1])
                    if abs(base - beg) > len(self.pro['i']) * 100:
                        bad('open result prefix exceeds guard')
                    head = [self.slot(i) for i in range(beg, base)]
                    unpk = self.nx(f)
                    call = N('call', [unpk, [temp, atom(max(1, beg - base + 1)), N('dot', [temp, N('id', ['n'])])]])
                    return V('spread', [head + [call]])
                if len(args) != 3 or any(type(v) not in (int, float) for v in args[1:]):
                    bad('open result range lifting pending')
                beg, end = int(args[1]), int(args[2])
                if end - beg > len(self.pro['i']) * 100:
                    bad('register argument range exceeds guard')
                return V('spread', [[self.slot(i) for i in range(beg, end + 1)]])
            if isinstance(f, V):
                if f.k == 'native':
                    f = self.nx(f)
                elif f.k == 'pack':
                    return V('multi', [self.nx(args[0])])
                elif f.k == 'interp':
                    ch = next((v for v in args if isinstance(v, V) and v.k == 'child'), None)
                    if ch is None:
                        bad('closure child binding absent')
                    ups = {}
                    for v in args:
                        if isinstance(v, V) and v.k == 'proxy':
                            for idx, pair in v.a[0].a[0].items():
                                vals = pair.a[0]
                                rts = [(k, q) for k, q in vals.items() if isinstance(q, V) and q.k in ('regs', 'up')]
                                if len(vals) != 2 or len(rts) != 1:
                                    bad('capture reference layout unresolved')
                                fld, root = rts[0]
                                kfld, key = next((k, q) for k, q in vals.items() if k != fld)
                                self.cfld.add((fld, kfld))
                                if root.k == 'regs':
                                    ups[idx] = self.slot(key)
                                elif key in root.a[0]:
                                    ups[idx] = root.a[0][key]
                                else:
                                    bad('parent capture reference absent')
                    vv = V('closure', [ch.a[0], ups])
                    self.clos.append(vv)
                    return vv
                else:
                    bad('callee lifting pending for ' + f.k)
            if len(args) == 2 and all(isinstance(v, V) and v.k == 'table' for v in args):
                meta = args[1].a[0]
                if b'__index' in meta and b'__newindex' in meta:
                    acc = meta[b'__index']
                    if isinstance(acc, V) and acc.k == 'fn':
                        fn, cap = acc.a
                        for z in fn.a[1]:
                            if z.k == 'loc' and z.a[1] and z.a[1][0].k == 'idx':
                                n = z.a[1][0].a[0]
                                if n.k == 'id' and isinstance(cap.get(n.a[0]), V) and cap[n.a[0]].k == 'table':
                                    return V('proxy', [cap[n.a[0]]])
            flat = []
            for i, v in enumerate(args):
                if isinstance(v, V) and v.k == 'spread':
                    if i == len(args) - 1:
                        flat.extend(v.a[0])
                    else:
                        flat.append(v.a[0][0] if v.a[0] else atom(None))
                else:
                    flat.append(self.nx(v))
            return N('call', [self.nx(f), flat])
        bad('expression lifting pending for ' + k)

    def put(self, n, v, env, eve0, loca=False):
        if n.k == 'id':
            key = n.a[0]
            if isinstance(v, V) and v.k == 'closure':
                v = N('closure', v.a)
            if isinstance(v, V) and v.k == 'array' and v.a[0].k == 'tab':
                tmp = self.temp()
                eve0.append(('st', N('loc', [[tmp], [v.a[0]]])))
                v = V('array', [tmp])
            if loca:
                env['$shadow'] = env.get('$shadow', frozenset()) | {key}
            if key in self.pers and key not in env.get('$shadow', ()):
                env['$def'] = env.get('$def', frozenset()) | {key}
            if key == self.hp.pc and key not in env.get('$shadow', ()):
                if type(v) not in (int, float):
                    bad('program counter target lifting pending')
                env[key] = v
            elif isinstance(v, N):
                old = env.get(key)
                if not loca and isinstance(old, N) and old.k == 'id' and old.a[0].startswith('var_'):
                    eve0.append(('st', N('set', [[old], [v], '='])))
                else:
                    tmp = self.temp()
                    eve0.append(('st', N('loc', [[tmp], [v]])))
                    env[key] = tmp
            else:
                env[key] = v
            return
        if n.k not in ('idx', 'dot'):
            bad('assignment target lifting pending')
        obj = self.ex(n.a[0], env)
        if isinstance(obj, V) and obj.k == 'upctx':
            return
        key = self.ex(n.a[1], env) if n.k == 'idx' else n.a[1].a[0].encode()
        if isinstance(obj, V) and obj.k == 'table':
            obj.a[0][key] = v
            return
        if isinstance(obj, V) and obj.k == 'regs':
            targ = self.slot(key)
        elif isinstance(obj, V) and obj.k in ('up', 'global'):
            targ = self.ex(n, env)
        else:
            targ = N('idx', [self.nx(obj), self.nx(key)])
        if isinstance(v, V) and v.k == 'closure':
            expr = N('closure', v.a)
        else:
            expr = self.nx(v)
        eve0.append(('st', N('set', [[targ], [expr], '='])))

    def dfor(self, z, env, es, vals, dist):
        beg, cnt = vals[:2]
        temp, z2 = cnt.a
        if type(z2) not in (int, float) or not math.isfinite(z2) or z2 != int(z2) or not math.isfinite(beg):
            bad('dynamic range traversal origin unresolved')
        base = int(z2 + 1)
        if len(vals) == 3 and vals[2] != 1 or beg != int(beg):
            bad('dynamic range traversal bounds unresolved')
        name = z.a[0][0].a[0]
        en = dict(env)
        en['$shadow'] = en.get('$shadow', frozenset()) | {name}
        if dist:
            if int(beg) != base:
                bad('variadic distribution origin unresolved')
            en[name] = int(beg)
        else:
            if beg < base:
                for i in range(int(beg), base):
                    self.tick()
                    en[name] = i
                    path = self.scp(z.a[2], [(en, [], None)])
                    if len(path) != 1 or path[0][2] is not None or any(q[0] != 'st' for q in path[0][1]):
                        bad('dynamic result prefix effects unresolved')
                    en, rows, term = path[0]
                    es.extend(rows)
                beg = base
            idx = self.temp()
            en[name] = idx if base == 1 else N('bin', ['+', idx, atom(base - 1)])
            en['$range'] = (temp, idx, base)
        path = self.scp(z.a[2], [(en, [], None)])
        if len(path) != 1 or path[0][2] is not None:
            bad('dynamic handler loop branch lifting pending')
        out, z3, term = path[0]
        if any(q[0] != 'st' for q in z3):
            bad('dynamic handler loop predicate unresolved')
        if dist:
            z6, z7 = {}, []
            for kind, q in z3:
                if q.k not in ('loc', 'set') or len(q.a[0]) != len(q.a[1]) or len(q.a[0]) != 1 or q.a[0][0].k != 'id':
                    bad('variadic distribution effect unresolved')
                rhs = q.a[1][0]
                seen = set()
                while rhs.k == 'id' and rhs.a[0] in z6 and rhs.a[0] not in seen:
                    seen.add(rhs.a[0])
                    rhs = z6[rhs.a[0]]
                if rhs.k != 'idx' or rhs.a[0].k != 'id' or rhs.a[0].a[0] != temp.a[0] or val(rhs.a[1]) != (True, 1):
                    bad('variadic distribution value unresolved')
                lhs = q.a[0][0].a[0]
                if lhs == self.slot(beg).a[0]:
                    z7.append(q)
                elif lhs.startswith('var_'):
                    z6[lhs] = rhs
                else:
                    bad('variadic distribution has an unrelated store')
            if len(z7) != 1:
                bad('variadic distribution destination unresolved')
            es.append(('st', N('dist', [base, temp])))
        else:
            body = [q[1] for q in z3]
            es.append(('st', N('for', [[idx], [atom(beg - base + 1), N('dot', [temp, N('id', ['n'])])], body])))
        env['$use'] = env.get('$use', frozenset()) | out.get('$use', frozenset())
        for key, z4 in out.items():
            if key.startswith('$') or key == name:
                continue
            old = env.get(key)
            if dist and isinstance(z4, N) and z4.k == 'id' and z4.a[0] in z6:
                env[key] = V('pending', [key])
                continue
            if z4 is not old and z4 != old:
                if not dist and isinstance(z4, N) and isinstance(old, N) and z4.k == old.k == 'id' and z4.a == old.a:
                    continue
                env[key] = V('pending', [key])

    def clse(self, z, env, es):
        stat = {'ng': 0, 'nr': 0, 'ni': 0, 'wr': 0, 'pred': None, 'snap': None, 'vars': set()}

        def cx(q, en):
            self.tick()
            q = ung(q)
            k, a = q.k, q.a
            if k in ('num', 'str', 'true', 'false', 'nil'):
                return cv(q, {}, {})
            if k == 'id' and a[0] in en and not isinstance(en[a[0]], N):
                return en[a[0]]
            if k in ('idx', 'dot'):
                obj = cx(a[0], en)
                key = cx(a[1], en) if k == 'idx' else a[1].a[0].encode()
                if isinstance(obj, V):
                    if obj.k == 'upctx' and isinstance(key, V) and key.k == 'gi':
                        return V('cg')
                    if obj.k == 'cg' and isinstance(key, V) and key.k == 'ri':
                        return V('cr')
                    if obj.k == 'cr' and isinstance(key, (int, float, bytes)):
                        return V('cs', [key])
                    if obj.k == 'cs' and isinstance(key, V) and key.k == 'cs':
                        return V('cv', [obj.a[0], key.a[0]])
                    if obj.k == 'table' and not obj.a[0] and isinstance(key, V) and key.k == 'cs':
                        return V('ix', [obj, key.a[0]])
            if k == 'un' and a[0] == '#':
                obj = cx(a[1], en)
                if isinstance(obj, V) and obj.k in ('upctx', 'cg'):
                    return V('len', [obj.k])
            if k == 'bin':
                l, r = cx(a[1], en), cx(a[2], en)
                if a[0] == '==':
                    if isinstance(r, V) and r.k == 'cs':
                        l, r = r, l
                    if isinstance(l, V) and l.k == 'cs' and isinstance(r, V) and r.k == 'regs':
                        return V('eqr', [l.a[0]])
                if a[0] in ('>=', '<='):
                    if a[0] == '<=':
                        l, r = r, l
                    if isinstance(l, V) and l.k == 'cs' and type(r) in (int, float) and math.isfinite(r) and int(r) == r:
                        return V('ger', [l.a[0], int(r)])
                if a[0] == 'and' and isinstance(l, V) and isinstance(r, V):
                    if l.k == 'ger':
                        l, r = r, l
                    if l.k == 'eqr' and r.k == 'ger':
                        return V('pred', [l.a[0], r.a[0], r.a[1]])
            bad('upvalue close expression proof incomplete')

        def proc(bs, en, mode):
            for q in bs:
                self.tick()
                a = q.a
                if q.k == 'do':
                    proc(a[0], dict(en), mode)
                elif q.k == 'loc':
                    vals = [cx(n, en) for n in a[1]]
                    for i, n in enumerate(a[0]):
                        if n.k != 'id':
                            bad('upvalue close local binding unresolved')
                        en[n.a[0]] = vals[i] if i < len(vals) else None
                elif q.k == 'set' and mode in ('grp', 'ref') and a[2] == '=' and len(a[0]) == len(a[1]) == 1 and a[0][0].k == 'id':
                    name = a[0][0].a[0]
                    if name not in env or name not in env.get('$shadow', ()):
                        bad('upvalue close scratch binding absent')
                    en[name] = cx(a[1][0], en)
                    stat['vars'].add(name)
                elif q.k == 'for':
                    vals = [cx(n, en) for n in a[1]]
                    if len(a[0]) != 1 or len(vals) not in (2, 3) or not isinstance(vals[1], V) or vals[1].k != 'len' or len(vals) == 3 and vals[2] != 1:
                        bad('upvalue close traversal proof incomplete')
                    kind = vals[1].a[0]
                    if kind == 'upctx' and mode == 'top' and vals[0] == 1:
                        stat['ng'] += 1
                        tag, nxt = 'gi', 'grp'
                    elif kind == 'cg' and mode == 'grp' and vals[0] == 0:
                        stat['nr'] += 1
                        tag, nxt = 'ri', 'ref'
                    else:
                        bad('upvalue close traversal bounds unresolved')
                    sub = dict(en)
                    sub[a[0][0].a[0]] = V(tag)
                    proc(a[2], sub, nxt)
                elif q.k == 'if':
                    if mode != 'ref' or len(a[0]) != 1 or a[1]:
                        bad('upvalue close guard proof incomplete')
                    cond, bs = a[0][0]
                    pred = cx(cond, en)
                    if not isinstance(pred, V) or pred.k != 'pred' or stat['pred'] is not None:
                        bad('upvalue close storage predicate unresolved')
                    stat['pred'] = pred.a
                    stat['ni'] += 1
                    proc(bs, dict(en), 'take')
                elif q.k == 'set' and mode == 'take' and a[2] == '=' and len(a[0]) == len(a[1]) == 1:
                    lhs, rhs = cx(a[0][0], en), cx(a[1][0], en)
                    fld, idx, thr = stat['pred']
                    if isinstance(lhs, V) and lhs.k == 'ix' and lhs.a[1] == idx and isinstance(rhs, V) and rhs.k == 'cv' and rhs.a == [fld, idx] and stat['wr'] == 0:
                        stat['snap'] = lhs.a[0]
                        stat['wr'] = 1
                    elif isinstance(lhs, V) and lhs.k == 'cs' and lhs.a[0] == fld and rhs is stat['snap'] and stat['wr'] == 1:
                        stat['wr'] = 2
                    else:
                        bad('upvalue close snapshot proof incomplete')
                else:
                    bad('upvalue close effect proof incomplete')
        proc([z], dict(env), 'top')
        if (stat['ng'], stat['nr'], stat['ni'], stat['wr']) != (1, 1, 1, 2):
            bad('upvalue close traversal shape unresolved')
        fld, idx, thr = stat['pred']
        es.append(('st', N('close', [thr, fld, idx])))
        for name, v in list(env.items()):
            if v is stat['snap']:
                env[name] = V('closed')
            elif name in stat['vars']:
                env[name] = V('pending', [name])

    def scp(self, bs, sta1):
        out = []
        for env, eve0, term in sta1:
            shad = env.get('$shadow', frozenset())
            save = {n.a[0]: (n.a[0] in env, env.get(n.a[0])) for q in bs if q.k == 'loc' for n in q.a[0]}
            vals = self.bloc(bs, [(env, eve0, term)])
            for en, es, tr in vals:
                en['$shadow'] = shad
                for key, (had, v) in save.items():
                    if had:
                        en[key] = v
                    else:
                        en.pop(key, None)
                out.append((en, es, tr))
        return out

    def bloc(self, bs, sta1):
        cur = sta1
        for z in bs:
            self.tick()
            nxt = []
            for env, eve0, term in cur:
                if term is not None:
                    nxt.append((env, eve0, term))
                    continue
                k, a = z.k, z.a
                if k == 'do':
                    nxt.extend(self.scp(a[0], [(env, eve0, None)]))
                elif k in ('loc', 'set'):
                    vals = [self.ex(q, env) for q in a[1]]
                    if len(vals) == 1 and isinstance(vals[0], V) and vals[0].k == 'multi':
                        key = (self.curp, id(z))
                        if key not in self.pac0:
                            self.pac0[key] = self.temp()
                            self.hois.append(self.pac0[key])
                        temp = self.pac0[key]
                        pack = self.nx(V('native', [N('dot', [N('id', ['table']), N('id', ['pack'])])]))
                        eve0.append(('st', N('set', [[temp], [N('call', [pack, [vals[0].a[0]]])], '='])))
                        vals = [V('results', [temp]), V('count', [temp, 0])]
                    elif len(a[0]) > 1:
                        lhs, rhs, out = [], [], []
                        for i, v in enumerate(vals):
                            if isinstance(v, N) or isinstance(v, V) and v.k == 'array':
                                cnt = max(1, len(a[0]) - i) if isinstance(v, N) and v.k == 'call' and i == len(vals) - 1 else 1
                                ts = [self.temp() for j in range(cnt)]
                                lhs.extend(ts)
                                rhs.append(self.nx(v))
                                out.extend(ts)
                            else:
                                out.append(v)
                        if lhs:
                            eve0.append(('st', N('loc', [lhs, rhs])))
                        vals = out
                    for i, n in enumerate(a[0]):
                        v = vals[i] if i < len(vals) else None
                        if k == 'set' and a[2] != '=':
                            v = self.ex(N('bin', [a[2][:-1], n, atom(v)]), env)
                        self.put(n, v, env, eve0, k == 'loc')
                    nxt.append((env, eve0, None))
                elif k == 'stmt':
                    v = self.ex(a[0], env)
                    eve0.append(('st', N('stmt', [self.nx(v)])))
                    nxt.append((env, eve0, None))
                elif k == 'ret':
                    vals = []
                    for i, q in enumerate(a[0]):
                        v = self.ex(q, env)
                        if isinstance(v, V) and v.k == 'spread':
                            vals.extend(v.a[0] if i == len(a[0]) - 1 else [v.a[0][0] if v.a[0] else atom(None)])
                        else:
                            vals.append(self.nx(v))
                    nxt.append((env, eve0, ('ret', vals)))
                elif k == 'if':
                    pend = [(env, eve0)]
                    for cond, body in a[0]:
                        rest = []
                        for en, es in pend:
                            v = self.ex(cond, en)
                            if isinstance(v, N):
                                nxt.extend(self.scp(body, [(dict(en), es + [('br', v, True)], None)]))
                                rest.append((dict(en), es + [('br', v, False)]))
                            elif tru(v):
                                nxt.extend(self.scp(body, [(en, es, None)]))
                            else:
                                rest.append((en, es))
                        pend = rest
                    for en, es in pend:
                        nxt.extend(self.scp(a[1], [(en, es, None)]))
                elif k == 'for':
                    end = ung(a[1][1]) if len(a[1]) >= 2 else None
                    if end is not None and end.k == 'un' and end.a[0] == '#':
                        obj = self.ex(end.a[1], env)
                        if isinstance(obj, V) and obj.k == 'upctx':
                            self.clse(z, env, eve0)
                            nxt.append((env, eve0, None))
                            continue
                    vals = [self.ex(q, env) for q in a[1]]
                    if len(vals) >= 2 and type(vals[0]) in (int, float) and isinstance(vals[1], V) and vals[1].k == 'count':
                        dist = any(q.k == 'idx' and q.a[0].k == 'id' and isinstance(env.get(q.a[0].a[0]), V) and env[q.a[0].a[0]].k == 'vargs' for q in walk(a[2]))
                        call = any(q.k == 'stmt' and q.a[0].k == 'call' for q in walk(a[2]))
                        if dist or call:
                            self.dfor(z, env, eve0, vals, dist)
                            nxt.append((env, eve0, None))
                            continue
                        temp, shif = vals[1].a
                        base = int(vals[0])
                        if shif != base - 1:
                            bad('multiple return destination range lifting pending')
                        foun = None
                        cou0 = None
                        for q in a[2]:
                            if q.k != 'set' or len(q.a[0]) != 1 or len(q.a[1]) != 1:
                                bad('multiple return copy effect lifting pending')
                            lhs, rhs = q.a[0][0], ung(q.a[1][0])
                            if lhs.k == 'idx' and isinstance(self.ex(lhs.a[0], env), V) and self.ex(lhs.a[0], env).k == 'regs':
                                src = self.ex(rhs.a[0], env) if rhs.k == 'idx' else None
                                if not isinstance(src, V) or src.k != 'results' or src.a[0].a[0] != temp.a[0] or rhs.a[1].k != 'id':
                                    bad('multiple return source range lifting pending')
                                if lhs.a[1].k != 'id' or lhs.a[1].a[0] != a[0][0].a[0]:
                                    bad('multiple return register destination lifting pending')
                                foun = rhs.a[1].a[0]
                            elif lhs.k == 'id':
                                v = self.ex(rhs, env)
                                if type(v) not in (int, float):
                                    bad('multiple return source index lifting pending')
                                env[lhs.a[0]] = v
                                cou0 = lhs.a[0]
                            else:
                                bad('multiple return copy target lifting pending')
                        if foun is None or foun != cou0 or env[foun] != 1:
                            bad('multiple return source index origin lifting pending')
                        env[foun] = V('count', [temp, 0])
                        eve0.append(('st', N('dist', [base, temp])))
                        nxt.append((env, eve0, None))
                        continue
                    if any(type(v) not in (int, float) for v in vals):
                        bad('handler range lifting pending')
                    beg, end = vals[:2]
                    step = vals[2] if len(vals) == 3 else 1
                    if step == 0 or abs(end - beg) > len(self.pro['i']) * 100:
                        bad('handler range exceeds guard')
                    name = a[0][0].a[0]
                    old = (name in env, env.get(name), env.get('$shadow', frozenset()))
                    acti = [(env, eve0, None)]
                    for i in range(int(beg), int(end) + (1 if step > 0 else -1), int(step)):
                        for en, es, tr in acti:
                            en['$shadow'] = old[2] | {name}
                            en[name] = i
                        acti = self.scp(a[2], acti)
                    for en, es, tr in acti:
                        en['$shadow'] = old[2]
                        if old[0]:
                            en[name] = old[1]
                        else:
                            en.pop(name, None)
                    nxt.extend(acti)
                else:
                    bad('statement lifting pending for ' + k)
            if len(nxt) > 256:
                bad('instruction branch count exceeds guard')
            cur = nxt
        return cur

    def grap(self):
        todo = [(1, {key: self.env[key] for key in self.pers})]
        seen = {}
        uses, defs, conf = {}, {}, []
        while todo:
            pc, sta0 = todo.pop()
            mark = {}
            for key, v in sta0.items():
                if isinstance(v, V) and v.k == 'count':
                    mark[key] = ('count', v.a[0].a[0], v.a[1])
                elif isinstance(v, (V, N)):
                    mark[key] = ('object', id(v))
                else:
                    mark[key] = ('value', v)
            if pc in seen:
                if seen[pc] != mark:
                    conf.append((pc, {key for key in mark if seen[pc].get(key) != mark[key]}))
                continue
            seen[pc] = mark
            self.curp = pc
            if pc not in self.pro['i']:
                bad('control flow target instruction absent at index ' + str(pc))
            env = dict(self.env)
            env.update(sta0)
            env[self.hp.pc] = pc
            env[self.hp.ins] = self.pro['i'][pc]
            env['$use'] = frozenset()
            env['$def'] = frozenset()
            opco = env[self.hp.ins][self.hp.fld]
            body = self.hp.get(opco)
            path = self.bloc(body, [(env, [], None)])
            out = []
            for en, eve0, term in path:
                if term is None:
                    targ = en[self.hp.pc]
                    if type(targ) not in (int, float) or targ != int(targ):
                        bad('control flow target is not integral')
                    term = ('jump', int(targ))
                    todo.append((int(targ), {key: en[key] for key in self.pers}))
                out.append((eve0, term))
            self.gph[pc] = out
            uses[pc] = set().union(*(en.get('$use', set()) for en, es, tr in path))
            defs[pc] = set.intersection(*(set(en.get('$def', ())) for en, es, tr in path))
        if conf:
            keys = set().union(*(ks for pc, ks in conf))
            rev = {pc: set() for pc in self.gph}
            for pc, path in self.gph.items():
                for es, tr in path:
                    if tr[0] == 'jump':
                        rev[tr[1]].add(pc)
            live = {pc: ks & keys for pc, ks in uses.items()}
            todo = [pc for pc, ks in live.items() if ks]
            pend = set(todo)
            while todo:
                self.tick()
                pc = todo.pop()
                pend.discard(pc)
                for pre in rev[pc]:
                    self.tick()
                    add = live[pc] - defs[pre] - live[pre]
                    if add:
                        live[pre].update(add)
                        if pre not in pend:
                            pend.add(pre)
                            todo.append(pre)
            for pc, ks in conf:
                if live[pc] & ks:
                    bad('multiple return state merge lifting pending at instruction ' + str(pc))
        dmap = {}
        for pc, path in self.gph.items():
            for eve0, term in path:
                out = []
                for even in eve0:
                    if even[0] != 'st' or even[1].k != 'dist':
                        out.append(even)
                        continue
                    z = even[1]
                    if id(z) not in dmap:
                        base, temp = z.a
                        body = []
                        for idx in sorted(self.regs):
                            if idx < base:
                                continue
                            off = idx - base + 1
                            cond = N('bin', ['>=', N('dot', [temp, N('id', ['n'])]), atom(off)])
                            stmt = N('set', [[self.slot(idx)], [N('idx', [temp, atom(off)])], '='])
                            body.append(('st', N('if', [[[cond, [stmt]]], []])))
                        dmap[id(z)] = body
                    out.extend(dmap[id(z)])
                eve0[:] = out
        return self.gph

    def box(self, v):
        return N('tab', [[[N('key', ['value']), v]]], tag=1)

    def cell(self):
        own = {self.slot(i).a[0]: i for i in self.regs}
        clos, ends = {}, {}
        for path in self.gph.values():
            for es, tr in path:
                for q in walk([z[1] for z in es] + ([tr[1]] if tr[0] == 'ret' else [])):
                    if q.k == 'closure':
                        clos[id(q)] = q
                    elif q.k == 'close':
                        ends[id(q)] = q
        if not ends:
            return
        caps = {v.a[0] for q in clos.values() for v in q.a[1].values() if v.k == 'id' and v.a[0] in own}
        if caps and (len(self.cfld) != 1 or any(tuple(q.a[1:]) not in self.cfld for q in ends.values())):
            bad('upvalue close fields disagree with capture layout')
        cels = {name: self.temp() for name in sorted(caps, key=lambda name: own[name])}
        for name, dst in cels.items():
            val = N('id', [name]) if own[name] < self.npar else atom(None)
            init = self.box(val)
            self.cels.append(N('loc', [[dst], [init]]))
        defs, z5 = {}, {}
        for key, q in clos.items():
            pre, ups = [], {}
            for idx, v in q.a[1].items():
                if v.k == 'id' and v.a[0] in cels:
                    dst = self.temp()
                    pre.append(N('loc', [[dst], [cels[v.a[0]]]]))
                    ups[idx] = N('dot', [dst, N('id', ['value'])])
                else:
                    ups[idx] = v
            defs[key] = pre
            z5[key] = N('closure', [q.a[0], ups])
        memo = {}

        def rep(q, dep=0):
            self.tick()
            if dep > 160:
                bad('capture cell expression depth exceeded')
            if not isinstance(q, (N, list, tuple, dict)):
                return q
            key = id(q)
            if key in memo:
                return memo[key]
            if isinstance(q, N):
                if q.k == 'id' and q.a[0] in cels:
                    out = N('dot', [cels[q.a[0]], N('id', ['value'])])
                elif q.k == 'closure':
                    out = z5[key]
                else:
                    out = N(q.k, [], q.s, q.e, q.ln)
                    memo[key] = out
                    out.a = [rep(q.a[0], dep + 1), q.a[1]] if q.k in ('dot', 'met') else [rep(v, dep + 1) for v in q.a]
            elif isinstance(q, dict):
                out = {}
                memo[key] = out
                out.update((k, rep(v, dep + 1)) for k, v in q.items())
            elif isinstance(q, tuple):
                out = tuple(rep(v, dep + 1) for v in q)
            else:
                out = []
                memo[key] = out
                out.extend(rep(v, dep + 1) for v in q)
            memo[key] = out
            return out
        done = {}
        for key, q in ends.items():
            done[key] = [N('set', [[dst], [self.box(N('dot', [dst, N('id', ['value'])]))], '=']) for name, dst in cels.items() if own[name] >= q.a[0]]
        for pc, path in self.gph.items():
            out = []
            for es, tr in path:
                z8 = []
                for kind, q, *rest in es:
                    if kind == 'st' and q.k == 'close':
                        z8.extend(('st', v) for v in done[id(q)])
                        continue
                    seen = set()
                    for v in walk(q):
                        if v.k == 'closure' and id(v) not in seen:
                            seen.add(id(v))
                            z8.extend(('st', z) for z in defs[id(v)])
                    z8.append((kind, rep(q), *rest))
                if tr[0] == 'ret':
                    seen = set()
                    for v in walk(tr[1]):
                        if v.k == 'closure' and id(v) not in seen:
                            seen.add(id(v))
                            z8.extend(('st', z) for z in defs[id(v)])
                    tr = ('ret', rep(tr[1]))
                out.append((z8, tr))
            self.gph[pc] = out


class Cf:
    def __init__(self, fx):
        self.fx = fx
        self.entr = getattr(fx, 'entr', 1)
        self.ldep = getattr(fx, 'ldep', 0)
        if self.ldep > 160:
            bad('natural loop nesting depth exceeded')
        self.gph = dict(fx.gph)
        self.succ = {}
        self.pdom = {}
        self.dept = {None: 0}
        self.up = {None: []}
        self.seen = set()
        self.stp = 0
        self.cop = 0
        self.alt = False
        self.clim = max(10000, sum(1 for ps in self.gph.values() for es, tr in ps for q in walk([es, tr])) * 8)
        self.lim = max(10000, len(self.gph) * 200, self.clim)
        self.fuse()
        self.coal()
        self.cyc()
        self.tals()
        self.prep()

    def tals(self):
        for pc, ps in list(self.gph.items()):
            if len(ps) < 2:
                continue
            out = []
            for es, tr in ps:
                cur, rows = tr, []
                while cur[0] == 'jump':
                    self.tick()
                    dst = cur[1]
                    qs = self.gph[dst]
                    if len(qs) != 1 or any(q[0] != 'st' for q in qs[0][0]):
                        break
                    rows.append(qs[0][0])
                    cur = qs[0][1]
                if cur[0] in ('ret', 'brk', 'cont'):
                    es = list(es)
                    for row in rows:
                        for q in row:
                            self.tick()
                            es.append(q)
                    tr = cur
                out.append((es, tr))
            self.gph[pc] = out

    def fuse(self):
        jump = {pc: path[0][1][1] for pc, path in self.gph.items() if len(path) == 1 and not path[0][0] and path[0][1][0] == 'jump'}
        reps = {}
        for pc in jump:
            path, pos = [], {}
            cur = pc
            while cur in jump and cur not in reps:
                self.tick()
                if cur in pos:
                    cyc = path[pos[cur]:]
                    dst = self.entr if self.entr in cyc else min(cyc)
                    reps[dst] = dst
                    self.gph[dst] = [([], ('jump', dst))]
                    break
                pos[cur] = len(path)
                path.append(cur)
                cur = jump[cur]
            else:
                dst = reps.get(cur, cur)
            for cur in path:
                reps[cur] = dst
        for pc, path in list(self.gph.items()):
            if pc in reps and pc != self.entr and pc != reps[pc] and pc not in getattr(self.fx, 'keep', ()):
                self.gph.pop(pc)
                continue
            self.gph[pc] = [(es, ('jump', reps.get(tr[1], tr[1])) if tr[0] == 'jump' else tr) for es, tr in path]

    def coal(self):
        pred = {pc: set() for pc in self.gph}
        adj = {}
        for pc, rows in self.gph.items():
            adj[pc] = {tr[1] for es, tr in rows if tr[0] == 'jump'}
            for q in adj[pc]:
                pred[q].add(pc)
        inde = {pc: len(ps) for pc, ps in pred.items()}
        todo = dq(pc for pc, n in inde.items() if n == 0)
        acyc = set()
        while todo:
            self.tick()
            pc = todo.popleft()
            acyc.add(pc)
            for q in adj[pc]:
                inde[q] -= 1
                if inde[q] == 0:
                    todo.append(q)
        keep = getattr(self.fx, 'keep', ())
        for pc in list(self.gph):
            if pc not in self.gph or pc not in acyc:
                continue
            if pc != self.entr and pc not in keep and len(pred[pc]) == 1:
                prev = next(iter(pred[pc]))
                rows = self.gph.get(prev, ())
                if len(rows) == 1 and rows[0][1] == ('jump', pc):
                    continue
            cur, es, dead = pc, [], []
            while True:
                self.tick()
                rows = self.gph[cur]
                if len(rows) != 1 or rows[0][1][0] != 'jump':
                    break
                dst = rows[0][1][1]
                if dst not in acyc or dst == self.entr or dst in keep or len(pred[dst]) != 1:
                    break
                es.extend(rows[0][0])
                dead.append(dst)
                cur = dst
            if not dead:
                continue
            rows = self.gph[cur]
            cost = len(es) * len(rows)
            if self.cop + cost > self.clim:
                continue
            self.cop += cost
            self.gph[pc] = [(es + evs, tr) for evs, tr in rows]
            for dst in dead:
                self.gph.pop(dst)

    def cano(self, x, defs, seen=None):
        seen = set() if seen is None else seen
        if x.k == 'id' and x.a[0] in defs:
            if x.a[0] in seen:
                bad('loop expression alias cycle detected')
            return self.cano(defs[x.a[0]], defs, seen | {x.a[0]})
        if x.k in ('grp', 'cast'):
            return self.cano(x.a[0], defs, seen)
        if x.k in ('un', 'bin'):
            return N(x.k, [self.cano(q, defs, seen) if isinstance(q, N) else q for q in x.a])
        return x

    def same(self, a, b):
        return Em().ex(a) == Em().ex(b)

    def pre0(self, path):
        out = []
        idx = 0
        while all(idx < len(es) and es[idx][0] == 'st' for es, tr in path):
            x = path[0][0][idx][1]
            if not all(es[idx][1] is x for es, tr in path):
                break
            out.append(x)
            idx += 1
        return out

    def dead(self, pc, nams):
        todo = [(pc, set(nams))]
        seen = {}
        def used(q, live):
            for n in walk(q):
                self.tick()
                if n.k == 'id' and n.a[0] in live:
                    return True
            return False
        while todo:
            pc, live = todo.pop()
            self.tick()
            for name in live:
                self.tick()
            live = live - seen.get(pc, set())
            if not live:
                continue
            seen.setdefault(pc, set()).update(live)
            for es, tr in self.gph[pc]:
                for name in live:
                    self.tick()
                left = set(live)
                for ev in es:
                    if ev[0] != 'st':
                        if used(ev[1:], left):
                            return False
                        continue
                    z = ev[1]
                    if z.k in ('loc', 'set'):
                        lhs, rhs = z.a[:2]
                        rds = [rhs, [q for q in lhs if q.k != 'id']]
                        if z.k == 'set' and len(z.a) > 2 and z.a[2] != '=':
                            rds.append(lhs)
                        if used(rds, left):
                            return False
                        left.difference_update(q.a[0] for q in lhs if q.k == 'id')
                    elif used(z, left):
                        return False
                    if not left:
                        break
                if left:
                    if used(tr, left):
                        return False
                    if tr[0] == 'jump':
                        todo.append((tr[1], left))
        return True

    def cyc(self):
        caps = set()
        locs = {self.fx.slot(i).a[0] for i in list(getattr(self.fx, 'regs', ()))}
        for rows in self.gph.values():
            for q in walk(rows):
                if q.k == 'closure':
                    caps.update(n.a[0] for n in walk(list(q.a[1].values())) if n.k == 'id')
                elif q.k == 'loc':
                    locs.update(n.a[0] for n in q.a[0])
        adj = {pc: {tr[1] for es, tr in ps if tr[0] == 'jump'} for pc, ps in self.gph.items()}
        rev = {pc: set() for pc in adj}
        for pc, ss in adj.items():
            for q in ss:
                rev[q].add(pc)
        seen = set()
        seq = []
        for root in adj:
            if root in seen:
                continue
            stk = [(root, False)]
            while stk:
                self.tick()
                pc, done = stk.pop()
                if done:
                    seq.append(pc)
                    continue
                if pc in seen:
                    continue
                seen.add(pc)
                stk.append((pc, True))
                stk.extend((q, False) for q in adj[pc] if q not in seen)
        seen.clear()
        grou = []
        for root in reversed(seq):
            if root in seen:
                continue
            comp = set()
            stk = [root]
            while stk:
                pc = stk.pop()
                if pc in seen:
                    continue
                seen.add(pc)
                comp.add(pc)
                stk.extend(q for q in rev[pc] if q not in seen)
            if len(comp) > 1 or root in adj[root]:
                grou.append(comp)
        def sync(keys):
            for pc in keys:
                old = adj.get(pc, set())
                new = {tr[1] for es, tr in self.gph[pc] if tr[0] == 'jump'} if pc in self.gph else set()
                for q in old - new:
                    if q in rev:
                        rev[q].discard(pc)
                for q in new - old:
                    rev.setdefault(q, set()).add(pc)
                if pc in self.gph:
                    adj[pc] = new
                else:
                    adj.pop(pc, None)
            for pc in keys:
                if pc not in self.gph:
                    rev.pop(pc, None)

        for comp in grou:
            if not comp <= self.gph.keys():
                continue
            entr = {(p, q) for q in comp for p in rev[q] if p not in comp}
            exi0 = {q for p in comp for q in adj[p] if q not in comp}
            hds = {q for p, q in entr}
            if not hds and self.entr in comp:
                hds.add(self.entr)
            if len(hds) != 1:
                bad('loop region entry structuring pending')
            head = next(iter(hds))
            if len(exi0) > 1:
                sync(self.mlop(comp, head, exi0))
                continue
            end = next(iter(exi0)) if exi0 else None
            pre = next(iter(entr))[0] if len(entr) == 1 else None
            lats = [p for p in comp if adj[p] == {head, end}]
            if end is None or pre is None or len(lats) != 1 or adj[pre] != {head, end}:
                self.wlop(comp, head, end)
                sync(comp)
                continue
            lat = lats[0]
            path = self.gph[lat]
            pre0 = self.pre0(path)
            defs = {z.a[0][0].a[0]: z.a[1][0] for z in pre0 if z.k == 'loc' and len(z.a[0]) == len(z.a[1]) == 1}
            ind = step = inc = None
            for z in pre0:
                if z.k != 'set' or len(z.a[0]) != 1 or z.a[0][0].k != 'id':
                    continue
                rhs = self.cano(z.a[1][0], defs)
                if rhs.k == 'bin' and rhs.a[0] == '+':
                    lhs = z.a[0][0]
                    if self.same(lhs, rhs.a[1]):
                        ind, step, inc = lhs, rhs.a[2], rhs
                    elif self.same(lhs, rhs.a[2]):
                        ind, step, inc = lhs, rhs.a[1], rhs
            if ind is None or step.k != 'id':
                self.wlop(comp, head, end)
                sync(comp)
                continue
            pub = boun = None
            for es, tr in path:
                if tr != ('jump', head):
                    continue
                for even in es:
                    if even[0] == 'br':
                        c = self.cano(even[1], defs)
                        if c.k == 'bin' and c.a[0] in ('<=', '>=') and self.same(c.a[1], inc):
                            boun = c.a[2]
                    elif even[0] == 'st':
                        z = even[1]
                        if z.k == 'set' and len(z.a[0]) == 1 and z.a[0][0].k == 'id' and not self.same(z.a[0][0], ind):
                            if self.same(self.cano(z.a[1][0], defs), inc):
                                pub = z.a[0][0]
            if pub is None or boun is None or boun.k != 'id':
                self.wlop(comp, head, end)
                sync(comp)
                continue
            preb = self.pre0(self.gph[pre])
            init, last = {}, {}
            keys = {ind.a[0], step.a[0], boun.a[0]}
            for i, z in enumerate(preb):
                if z.k == 'set' and len(z.a[0]) == 1 and z.a[0][0].k == 'id' and z.a[0][0].a[0] in keys:
                    name = z.a[0][0].a[0]
                    init[name] = z.a[1][0]
                    last[name] = i
            if set(init) != keys or not all(val(init[k])[0] for k in (ind.a[0], step.a[0])):
                self.wlop(comp, head, end)
                sync(comp)
                continue
            if (keys | {pub.a[0]}) & caps or not self.dead(end, keys | {pub.a[0]}):
                self.wlop(comp, head, end)
                sync(comp)
                continue
            iset = {id(preb[i]) for i in last.values()}
            keep = [z for z in preb if id(z) not in iset]
            safe = set()
            good = True
            for z in preb[min(last.values()):]:
                if id(z) in iset:
                    continue
                if z.k != 'loc':
                    good = False
                    break
                for n, q in zip(z.a[0], z.a[1]):
                    if not val(q)[0] and not (q.k == 'id' and q.a[0] in locs and q.a[0] not in caps):
                        good = False
                        break
                    if q.k == 'id' and q.a[0] in keys:
                        safe.add(n.a[0])
            used = [q.a[1] for q in keep if q.k in ('loc', 'set')] + list(init.values())
            if not good or safe & caps or any(q.k == 'id' and q.a[0] in safe for q in walk(used)) or not self.dead(head, safe):
                self.wlop(comp, head, end)
                sync(comp)
                continue
            if any(tr[0] == 'jump' and tr[1] not in comp for pc in comp - {lat} for es, tr in self.gph[pc]):
                self.wlop(comp, head, end)
                sync(comp)
                continue
            part = {}
            for pc in comp - {lat}:
                ps = []
                for es, tr in self.gph[pc]:
                    if tr == ('jump', lat):
                        tr = ('stop', [])
                    ps.append((es, tr))
                part[pc] = ps
            sub = V('region')
            sub.gph = part
            sub.entr = head
            sub.ldep = self.ldep + 1
            body = Cf(sub).regn(head)
            if any(n.k == 'id' and n.a[0] in keys for n in walk(body)):
                self.wlop(comp, head, end)
                sync(comp)
                continue
            loop = N('for', [[pub], [init[ind.a[0]], init[boun.a[0]], init[step.a[0]]], body])
            keep.append(loop)
            self.gph[pre] = [([('st', z) for z in keep], ('jump', end))]
            for pc in comp:
                self.gph.pop(pc)
            sync(comp | {pre})

    def mlop(self, comp, head, exts):
        part = {}
        todo = list(exts)
        while todo:
            self.tick()
            pc = todo.pop()
            if pc in part:
                continue
            if pc in comp:
                bad('loop exit reenters component')
            part[pc] = self.gph[pc]
            todo.extend(tr[1] for es, tr in part[pc] if tr[0] == 'jump' and tr[1] not in part)
        sub = V('region')
        root = min(part) - 1
        part[root] = [([], ('jump', pc)) for pc in sorted(exts)]
        sub.gph, sub.entr, sub.ldep = part, root, self.ldep + 1
        sub.keep = set(exts)
        ext = Cf(sub)
        dest = iter(exts)
        end = next(dest)
        for pc in dest:
            end = ext.lca(end, pc)
        tals = {pc: ext.regn(pc, end) for pc in exts}
        self.wlop(comp, head, end, tals)
        old = set(self.gph)
        live = set()
        todo = [self.entr]
        while todo:
            self.tick()
            pc = todo.pop()
            if pc in live:
                continue
            live.add(pc)
            todo.extend(tr[1] for es, tr in self.gph[pc] if tr[0] == 'jump' and tr[1] not in live)
        for pc in old - live:
            self.gph.pop(pc)
        return comp | (old - live)

    def wlop(self, comp, head, end, tals=None):
        part = {}
        cut = 0
        mark = object()
        for pc in comp:
            path = []
            for es, tr in self.gph[pc]:
                if tr == ('jump', head):
                    tr = ('cont', mark)
                    cut += 1
                elif tr[0] == 'jump' and tr[1] not in comp:
                    if tals is not None:
                        body = tals[tr[1]]
                        es = list(es) + [('st', z) for z in self.cpy(body)]
                        tr = ('stop', []) if body and body[-1].k == 'ret' else ('brk', mark)
                    else:
                        if tr[1] != end:
                            bad('natural loop exit target unresolved')
                        tr = ('brk', mark)
                path.append((es, tr))
            part[pc] = path
        if not cut:
            bad('natural loop back edge absent')
        sub = V('region')
        sub.gph = part
        sub.entr = head
        sub.ldep = self.ldep + 1
        body = Cf(sub).regn(head)
        loop = N('wh', [N('true'), body], tag=mark)
        self.gph[head] = [([('st', loop)], ('jump', end) if end is not None else ('stop', []))]
        for pc in comp - {head}:
            self.gph.pop(pc)

    def tick(self):
        self.stp += 1
        if self.stp > self.lim:
            bad('control flow structuring step limit exceeded')

    def lca(self, a, b):
        if a == b:
            return a
        if self.dept[a] < self.dept[b]:
            a, b = b, a
        diff = self.dept[a] - self.dept[b]
        bit = 0
        while diff:
            if diff & 1:
                a = self.up[a][bit]
            diff >>= 1
            bit += 1
        if a == b:
            return a
        for bit in range(min(len(self.up[a]), len(self.up[b])) - 1, -1, -1):
            aa = self.up[a][bit] if bit < len(self.up[a]) else None
            bb = self.up[b][bit] if bit < len(self.up[b]) else None
            if aa != bb:
                a, b = aa, bb
        return self.up[a][0]

    def prep(self):
        inde = {pc: 0 for pc in self.gph}
        for pc, path in self.gph.items():
            ss = set()
            for eve0, term in path:
                ss.add(term[1] if term[0] == 'jump' else None)
            self.succ[pc] = ss
            for q in ss:
                if q is not None:
                    inde[q] += 1
        todo = [pc for pc, deg in inde.items() if deg == 0]
        hq.heapify(todo)
        seq = []
        while todo:
            self.tick()
            pc = hq.heappop(todo)
            seq.append(pc)
            for q in self.succ[pc]:
                if q is not None:
                    inde[q] -= 1
                    if inde[q] == 0:
                        hq.heappush(todo, q)
        if len(seq) != len(self.gph):
            bad('cyclic region structuring pending')
        self.ends = {pc for pc, ss in self.succ.items() if ss == {None}}
        safe = all(tr[0] in ('jump', 'ret', 'brk', 'cont') for ps in self.gph.values() for es, tr in ps)
        self.rank = {pc: i for i, pc in enumerate(seq)}
        self.link = {pc: ss - {None} for pc, ss in self.succ.items()} if safe else None
        self.merg = {}
        if safe:
            for i, pc in enumerate(seq[:-1]):
                if None in self.succ[pc]:
                    self.succ[pc] = (self.succ[pc] - {None}) | {seq[i + 1]}
        for pc in reversed(seq):
            ss = iter(self.succ[pc])
            par = next(ss)
            for q in ss:
                par = self.lca(par, q)
            self.pdom[pc] = par
            self.dept[pc] = self.dept[par] + 1
            row = [par]
            j = 0
            while row[j] is not None:
                prev = row[j]
                row.append(self.up[prev][j] if j < len(self.up[prev]) else None)
                j += 1
            self.up[pc] = row

    def tree(self, path, dep=0):
        self.tick()
        if dep > 160:
            bad('branch tree depth exceeded')
        out = []
        idx = 0
        while all(idx < len(eve0) and eve0[idx][0] == 'st' for eve0, term in path):
            z = path[0][0][idx][1]
            if not all(eve0[idx][1] is z for eve0, term in path):
                bad('handler shared effect factoring pending')
            out.append(z)
            idx += 1
        path = [(eve0[idx:], term) for eve0, term in path]
        if len(path) == 1 and not path[0][0]:
            term = path[0][1]
            if term[0] == 'jump':
                out.append(N('jmp', [term[1]]))
            elif term[0] == 'ret':
                out.append(N('ret', [term[1]]))
            elif term[0] == 'brk':
                out.append(N('break', [term[1]]))
            elif term[0] == 'cont':
                out.append(N('continue', [term[1]]))
            elif term[0] != 'stop':
                bad('control flow terminal record absent')
            return out
        if not all(eve0 and eve0[0][0] == 'br' for eve0, term in path):
            bad('handler branch factoring pending')
        cond = path[0][0][0][1]
        if not all(eve0[0][1] is cond for eve0, term in path):
            bad('handler decision order factoring pending')
        yes, no = [], []
        for eve0, term in path:
            (yes if eve0[0][2] else no).append((eve0[1:], term))
        if not yes or not no:
            bad('handler decision alternative absent')
        out.append(N('if', [[[cond, self.tree(yes, dep + 1)]], self.tree(no, dep + 1)]))
        return out

    def bran(self, body, stop, dep):
        out = []
        for z in body:
            if z.k == 'jmp':
                if z.a[0] != stop:
                    out.extend(self.regi(z.a[0], stop, dep))
            elif z.k == 'if':
                bs = [[cond, self.bran(b, stop, dep + 1)] for cond, b in z.a[0]]
                othe = self.bran(z.a[1], stop, dep + 1)
                out.append(N('if', [bs, othe]))
            else:
                out.append(z)
        return out

    def cpy(self, x):
        root = [None]
        todo = [(x, root, 0)]
        while todo:
            q, dst, idx = todo.pop()
            if isinstance(q, N):
                self.cop += 1
                if self.cop > self.clim:
                    bad('structured control flow copy budget exceeded')
                node = N(q.k, [None] * len(q.a), q.s, q.e, q.ln, q.tag)
                dst[idx] = node
                todo.extend((v, node.a, i) for i, v in enumerate(q.a))
            elif isinstance(q, (list, tuple)):
                node = [None] * len(q)
                dst[idx] = node
                todo.extend((v, node, i) for i, v in enumerate(q))
            elif isinstance(q, dict):
                node = {}
                dst[idx] = node
                todo.extend((v, node, k) for k, v in q.items())
            else:
                dst[idx] = q
        return root[0]

    def join(self, pc, stop):
        if not self.alt or self.link is None:
            return self.pdom[pc]
        vals = tuple(sorted(self.link[pc]))
        if not vals:
            return None
        if len(vals) == 1:
            return vals[0]
        if stop in vals:
            return stop
        key = (vals, stop)
        if key in self.merg:
            return self.merg[key]
        seen = {q: 1 << i for i, q in enumerate(vals)}
        todo = [(self.rank[q], q) for q in vals]
        hq.heapify(todo)
        full = (1 << len(vals)) - 1
        out = None
        while todo:
            self.tick()
            rank, cur = hq.heappop(todo)
            if seen[cur] == full:
                out = cur
                break
            if cur == stop:
                out = stop
                break
            for dst in self.link[cur]:
                self.tick()
                if dst not in seen:
                    seen[dst] = 0
                    hq.heappush(todo, (self.rank[dst], dst))
                seen[dst] |= seen[cur]
        self.merg[key] = out
        return out

    def regi(self, pc, stop=None, dep=0):
        if dep > 160:
            bad('control flow region depth exceeded')
        out = []
        while pc is not None and pc != stop:
            self.tick()
            self.seen.add(pc)
            join = self.join(pc, stop)
            body = self.cpy(self.tree(self.gph[pc]))
            out.extend(self.bran(body, join, dep))
            if pc in self.ends:
                break
            pc = join
        return out

    def esc(self, body):
        flag = {}

        def name(dst):
            if dst not in flag:
                flag[dst] = self.fx.temp()
            return flag[dst]

        def blk(bs, anc, dep=0):
            if dep > 160:
                bad('loop continuation nesting depth exceeded')
            out, exts = [], set()
            for z in bs:
                self.tick()
                if z.k in ('break', 'continue'):
                    dst = z.a[0] if z.a else anc[-1] if anc else None
                    if dst not in anc:
                        bad('loop control scope unresolved')
                    if dst == anc[-1]:
                        out.append(N(z.k))
                    else:
                        key = (dst, z.k)
                        out.extend([N('set', [[name(key)], [N('true')], '=']), N('break')])
                        exts.add(key)
                    continue
                if z.k in ('wh', 'for'):
                    idx = 1 if z.k == 'wh' else 2
                    dest = z.tag or z
                    more = blk(z.a[idx], anc + (dest,), dep + 1)
                    out.append(z)
                    for key in sorted(more, key=lambda key: (anc.index(key[0]), key[1])):
                        dst, kind = key
                        nm = name(key)
                        if anc and dst == anc[-1]:
                            tail = [N('set', [[nm], [N('false')], '=']), N(kind)]
                        else:
                            tail = [N('break')]
                            exts.add(key)
                        out.append(N('if', [[[nm, tail]], []]))
                    continue
                if z.k == 'if':
                    for cond, rows in z.a[0]:
                        exts.update(blk(rows, anc, dep + 1))
                    exts.update(blk(z.a[1], anc, dep + 1))
                elif z.k == 'do':
                    exts.update(blk(z.a[0], anc, dep + 1))
                out.append(z)
            bs[:] = out
            return exts
        if blk(body, ()):
            bad('loop continuation escapes function')
        if flag:
            body.insert(0, N('loc', [list(flag.values()), [N('false') for dst in flag]]))

    def regn(self, pc, stop=None):
        try:
            return self.regi(pc, stop)
        except Err as err:
            if str(err) not in ('control flow region depth exceeded', 'structured control flow copy budget exceeded', 'control flow structuring step limit exceeded'):
                raise
        if self.link is not None:
            self.alt = True
            self.stp = 0
            self.cop = 0
            self.seen.clear()
            return self.regi(pc, stop)
        mark = object()
        sub = V('region')
        sub.gph = {key: [(es, ('brk', mark) if tr[0] == 'stop' else tr) for es, tr in rows] for key, rows in self.gph.items()}
        sub.entr = pc
        sub.ldep = self.ldep + 1
        alt = Cf(sub)
        alt.alt = True
        body = alt.regi(pc, stop)
        body.append(N('break', [mark]))
        return [N('wh', [N('true'), body], tag=mark)]

    def fn(self):
        body = self.regn(self.entr)
        self.esc(body)
        pars = [self.fx.slot(i) for i in range(self.fx.npar)]
        slo0 = [self.fx.slot(i) for i in sorted(self.fx.regs) if i >= self.fx.npar]
        slo0.extend(self.fx.hois)
        if slo0:
            body.insert(0, N('loc', [slo0, []]))
        head = []
        if self.fx.varg is not None:
            head.extend(self.fx.vpre)
            if pars:
                head.append(N('loc', [pars, [N('idx', [self.fx.raw, atom(i + 1)]) for i in range(len(pars))]]))
            pars = [N('id', ['...'])]
        return N('fn', [pars, head + list(self.fx.cels) + body])


def fact(fn, fx):
    head = {fx.slot(i).a[0] for i in fx.regs}
    head.update(q.a[0] for q in fx.hois)
    head.update(q.a[0][0].a[0] for q in fx.cels)
    z11 = {}
    for q in walk(fn):
        if q.k != 'closure':
            continue
        key = [q.a[0]]
        for idx, ref in sorted(q.a[1].items()):
            if ref.k == 'id' and ref.a[0] in head:
                key.append((idx, 'id', ref.a[0]))
            elif ref.k == 'dot' and ref.a[0].k == 'id':
                key.append((idx, 'dot', ref.a[1].a[0]))
            else:
                break
        else:
            z11.setdefault(tuple(key), []).append(q)
    decl = []
    for z10 in z11.values():
        if len(z10) < 2:
            continue
        node = z10[0]
        args = {idx: fx.temp() for idx, ref in sorted(node.a[1].items()) if ref.k == 'dot'}
        refs = {idx: N('dot', [args[idx], ref.a[1]]) if idx in args else ref for idx, ref in node.a[1].items()}
        name = fx.temp()
        body = N('closure', [node.a[0], refs])
        z12 = N('fn', [list(args.values()), [N('ret', [[body]])]], tag=2)
        decl.append(N('loc', [[name], [z12]]))
        for q in z10:
            vals = [q.a[1][idx].a[0] for idx in args]
            q.k, q.a = 'call', [name, vals]
    pos = len(fx.vpre) + len(fx.cels)
    if fx.varg is not None and fx.npar:
        pos += 1
    if fx.hois or any(i >= fx.npar for i in fx.regs):
        pos += 1
    fn.a[1][pos:pos] = decl


def bld(ast, hp, sc, pro, fid=0, ups=None):
    root = N('pending')
    ae = sc.ae
    ctx = ae.out.get(id(hp.fn))
    if ctx is None:
        bad('interpreter lexical bindings unresolved')
    pool = {}
    rsv = {q.a[0] for q in walk(ast) if q.k == 'id'}
    vals = [lit(q.a[0]) for q in walk(ast) if q.k == 'str']
    todo = [pro]
    while todo:
        item = todo.pop()
        vals.extend(v for v in item['k'].values() if isinstance(v, bytes))
        todo.extend(item['p'])
    for v in vals:
        if re.fullmatch(rb'[A-Za-z_][A-Za-z_0-9]*', v):
            rsv.add(v.decode('ascii'))
    skip = set()
    for name in rsv:
        mt = re.match(r'(?:l_|var_)([0-9]+)_', name)
        if mt:
            skip.add(int(mt[1]))
    todo = [(pro, {} if ups is None else ups, root, 0)]
    seen = 0
    while todo:
        item, cap, out, dep = todo.pop()
        if dep > 160:
            bad('closure nesting depth exceeded')
        fid += 1
        while fid in skip:
            fid += 1
        fx = Fx(ast, hp, sc, item, fid, cap, ctx, pool, ae.cal, rsv)
        fx.grap()
        fx.cell()
        fn = Cf(fx).fn()
        fact(fn, fx)
        out.k, out.a = fn.k, fn.a
        for z in walk(fn):
            seen += 1
            if seen > 2000000:
                bad('closure expression size exceeds guard')
            if z.k == 'closure':
                idx, refs = z.a
                todo.append((item['p'][idx], refs, z, dep + 1))
    used = {q.a[0] for q in walk(root) if q.k == 'id'}
    root.a[1][:0] = [N('loc', [[name], [expr]]) for name, expr in pool.values() if name.a[0] in used]
    Sa(root, rsv)
    return opt(root)


class Sa:
    def __init__(self, ast, rsv=None):
        self.rsv = {q.a[0] for q in walk(ast) if q.k == 'id'}
        if rsv is not None:
            self.rsv.update(rsv)
        self.cnt = 0
        self.stp = 0
        func = [z for z in walk(ast) if z.k == 'fn']
        for fn in reversed(func):
            self.flow = {}
            self.aftr = {}
            self.loc = {n.a[0] for n in fn.a[0] if n.k == 'id'}
            self.caps = set()
            for z in walk(fn.a[1]):
                if z.k == 'loc':
                    self.loc.update(n.a[0] for n in z.a[0])
                    self.caps.update(n.a[0] for n in z.a[0] if n.k == 'id' and n.a[0].startswith('var_0_'))
                if z.k == 'for':
                    self.loc.update(n.a[0] for n in z.a[0])
                if z.k == 'fn':
                    self.caps.update(n.a[0] for n in walk(z) if n.k == 'id')
            self.ann(fn.a[1], set())
            self.tx(fn.a[1])

    def tick(self):
        self.stp += 1
        if self.stp > 4000000:
            bad('expression versioning step limit exceeded')

    def ids(self, x):
        return {n.a[0] for n in walk(x) if n.k == 'id'}

    def info(self, z):
        k, a = z.k, z.a
        if k in ('loc', 'set'):
            gen = self.ids(a[1])
            kill = set()
            for n in a[0]:
                if n.k == 'id':
                    kill.add(n.a[0])
                else:
                    gen.update(self.ids(n))
            return gen, kill
        if k == 'if':
            gen = set()
            kil0 = []
            for cond, body in a[0]:
                gen.update(self.ids(cond))
                g, d = self.sum(body)
                gen.update(g)
                kil0.append(d)
            g, d = self.sum(a[1])
            gen.update(g)
            kil0.append(d)
            return gen, set.intersection(*kil0)
        if k == 'for':
            g, d = self.sum(a[2])
            return self.ids(a[1]) | (g - self.ids(a[0])), set()
        if k == 'wh':
            g, d = self.sum(a[1])
            return self.ids(a[0]) | g, set()
        if k in ('break', 'continue'):
            return set(), set()
        if k == 'ret':
            return self.ids(a[0]), set()
        if k == 'stmt':
            return self.ids(a[0]), set()
        if k == 'do':
            return self.sum(a[0])
        bad('expression liveness record pending for ' + k)

    def sum(self, body):
        key = id(body)
        if key not in self.flow:
            gen, kill = set(), set()
            for z in body:
                self.tick()
                g, d = self.info(z)
                gen.update(g - kill)
                kill.update(d)
            self.flow[key] = gen, kill
        return self.flow[key]

    def ann(self, body, live, dep=0):
        if dep > 160:
            bad('expression liveness depth exceeded')
        rows = [None] * len(body)
        live = set(live)
        for i in range(len(body) - 1, -1, -1):
            self.tick()
            z = body[i]
            rows[i] = set(live)
            if z.k == 'if':
                for c, bs in z.a[0]:
                    self.ann(bs, live, dep + 1)
                self.ann(z.a[1], live, dep + 1)
            elif z.k == 'for':
                gen, kill = self.sum(z.a[2])
                self.ann(z.a[2], live | (gen - self.ids(z.a[0])), dep + 1)
            elif z.k == 'wh':
                gen, kill = self.sum(z.a[1])
                self.ann(z.a[1], live | gen | self.ids(z.a[0]), dep + 1)
            elif z.k == 'do':
                self.ann(z.a[0], live, dep + 1)
            gen, kill = self.info(z)
            live = gen | (live - kill)
        self.aftr[id(body)] = rows

    def sub(self, x, env, dep=0):
        self.tick()
        if dep > 160:
            bad('expression substitution depth exceeded')
        if not isinstance(x, N):
            if isinstance(x, list):
                return [self.sub(q, env, dep + 1) for q in x]
            return x
        if x.k == 'id':
            return env.get(x.a[0], x)
        if x.k == 'fn':
            return x
        if x.k in ('dot', 'met'):
            return N(x.k, [self.sub(x.a[0], env, dep + 1), x.a[1]])
        if x.k == 'mcall':
            return N(x.k, [self.sub(x.a[0], env, dep + 1), x.a[1], self.sub(x.a[2], env, dep + 1)])
        return N(x.k, [self.sub(q, env, dep + 1) for q in x.a], x.s, x.e, x.ln, x.tag)

    def chun(self, chun, live):
        env = {}
        out = []
        new = set()
        for z in chun:
            self.tick()
            k, a = z.k, z.a
            if k == 'loc' and not a[1]:
                out.append(z)
                continue
            if k in ('loc', 'set') and len(a[0]) == len(a[1]) == 1 and a[0][0].k == 'id':
                name = a[0][0].a[0]
                if name in self.loc and name not in self.caps:
                    rhs = self.sub(a[1][0], env)
                    self.cnt += 1
                    while 'l_ssa_' + str(self.cnt) in self.rsv:
                        self.cnt += 1
                    tmp = N('id', ['l_ssa_' + str(self.cnt)])
                    self.rsv.add(tmp.a[0])
                    out.append(N('loc', [[tmp], [rhs]]))
                    env[name] = tmp
                    if k == 'loc':
                        new.add(name)
                    continue
            if k in ('loc', 'set'):
                lhs = [n if n.k == 'id' else self.sub(n, env) for n in a[0]]
                rhs = [self.sub(q, env) for q in a[1]]
                out.append(N(k, [lhs, rhs] + a[2:]))
                for n in a[0]:
                    if n.k == 'id':
                        env.pop(n.a[0], None)
            else:
                out.append(self.sub(z, env))
        for name, valu in env.items():
            if name in live:
                kind = 'loc' if name in new else 'set'
                args = [[N('id', [name])], [valu]]
                if kind == 'set':
                    args.append('=')
                out.append(N(kind, args))
        return out

    def tx(self, body, dep=0):
        if dep > 160:
            bad('expression versioning depth exceeded')
        rows = self.aftr[id(body)]
        out = []
        i = 0
        while i < len(body):
            self.tick()
            z = body[i]
            if z.k in ('loc', 'set', 'stmt'):
                end = i + 1
                while end < len(body) and body[end].k in ('loc', 'set', 'stmt'):
                    end += 1
                out.extend(self.chun(body[i:end], rows[end - 1]))
                i = end
                continue
            if z.k == 'if':
                for c, bs in z.a[0]:
                    self.tx(bs, dep + 1)
                self.tx(z.a[1], dep + 1)
            elif z.k == 'for':
                self.tx(z.a[2], dep + 1)
            elif z.k == 'wh':
                self.tx(z.a[1], dep + 1)
            elif z.k == 'do':
                self.tx(z.a[0], dep + 1)
            out.append(z)
            i += 1
        body[:] = out


def opt(ast):
    rea0 = {}
    stor = {}
    todo = [('ex', ast)]
    blo0 = []
    caps = set()
    for z in walk(ast):
        if z.k == 'fn' and z is not ast:
            caps.update(n.a[0] for n in walk(z.a[1]) if n.k == 'id')
    while todo:
        kind, x = todo.pop()
        if isinstance(x, list):
            todo.extend((kind, q) for q in reversed(x))
            continue
        if not isinstance(x, N):
            continue
        k, a = x.k, x.a
        if kind == 'ex':
            if k == 'id':
                rea0[a[0]] = rea0.get(a[0], 0) + 1
            elif k == 'fn':
                blo0.append(a[1])
                todo.extend(('st', q) for q in reversed(a[1]))
            elif k in ('dot', 'met'):
                todo.append(('ex', a[0]))
            elif k == 'mcall':
                todo.extend(('ex', q) for q in reversed(a[2]))
                todo.append(('ex', a[0]))
            elif k == 'call':
                todo.extend(('ex', q) for q in reversed(a[1]))
                todo.append(('ex', a[0]))
            elif k == 'tab':
                for key, q in reversed(a[0]):
                    todo.append(('ex', q))
                    if key is not None and key.k != 'key':
                        todo.append(('ex', key))
            else:
                todo.extend(('ex', q) for q in reversed(a) if isinstance(q, N))
        elif k in ('loc', 'set'):
            for n in a[0]:
                if n.k == 'id':
                    if a[1]:
                        stor[n.a[0]] = stor.get(n.a[0], 0) + 1
                else:
                    todo.append(('ex', n))
            todo.extend(('ex', q) for q in reversed(a[1]))
        elif k == 'if':
            for cond, body in a[0]:
                todo.append(('ex', cond))
                blo0.append(body)
                todo.extend(('st', q) for q in reversed(body))
            blo0.append(a[1])
            todo.extend(('st', q) for q in reversed(a[1]))
        elif k == 'for':
            for n in a[0]:
                stor[n.a[0]] = stor.get(n.a[0], 0) + 1
            todo.extend(('ex', q) for q in reversed(a[1]))
            blo0.append(a[2])
            todo.extend(('st', q) for q in reversed(a[2]))
        elif k == 'wh':
            todo.append(('ex', a[0]))
            blo0.append(a[1])
            todo.extend(('st', q) for q in reversed(a[1]))
        elif k in ('break', 'continue'):
            pass
        elif k == 'ret':
            todo.extend(('ex', q) for q in reversed(a[0]))
        elif k == 'stmt':
            todo.append(('ex', a[0]))
        else:
            bad('expression reconstruction pending for ' + k)

    def fst(x):
        if x.k == 'id':
            return x.a[0]
        if x.k in ('grp', 'cast', 'dot', 'met', 'idx', 'call', 'mcall'):
            return fst(x.a[0])
        if x.k in ('un', 'bin'):
            return fst(x.a[1])
        return None

    def rep(x, name, rhs):
        if x.k == 'id' and x.a[0] == name:
            return rhs
        a = list(x.a)
        idx = 0 if x.k in ('grp', 'cast', 'dot', 'met', 'idx', 'call', 'mcall') else 1
        a[idx] = rep(a[idx], name, rhs)
        return N(x.k, a, x.s, x.e, x.ln)

    for body in reversed(blo0):
        out = []
        for z in body:
            while out:
                prev = out[-1]
                if prev.k not in ('loc', 'set') or len(prev.a[0]) != 1 or len(prev.a[1]) != 1 or prev.a[0][0].k != 'id':
                    break
                name = prev.a[0][0].a[0]
                once = rea0.get(name) == 1 and stor.get(name) == 1
                over = z.k in ('loc', 'set') and len(z.a[0]) == len(z.a[1]) == 1 and z.a[0][0].k == 'id' and z.a[0][0].a[0] == name and name not in caps
                if over:
                    over = sum(n.k == 'id' and n.a[0] == name for n in walk(z.a[1])) == 1
                if not once and not over:
                    break
                if z.k in ('loc', 'set') and z.a[1] and all(n.k == 'id' for n in z.a[0]):
                    x = z.a[1][0]
                    dst = z.a[1]
                    idx = 0
                elif z.k == 'stmt':
                    x, dst, idx = z.a[0], z.a, 0
                elif z.k == 'ret' and z.a[0]:
                    x, dst, idx = z.a[0][0], z.a[0], 0
                else:
                    break
                if fst(x) != name:
                    break
                dst[idx] = rep(x, name, prev.a[1][0])
                rea0[name] = rea0.get(name, 0) - 1
                stor[name] = stor.get(name, 0) - 1
                if over and prev.k == 'loc':
                    z.k = 'loc'
                    z.a = z.a[:2]
                out.pop()
            out.append(z)
        body[:] = out
    for body in blo0:
        out = []
        for z in body:
            if z.k == 'loc' and not z.a[1]:
                z.a[0] = [n for n in z.a[0] if rea0.get(n.a[0], 0) or stor.get(n.a[0], 0)]
                if not z.a[0]:
                    continue
            out.append(z)
            if z.k in ('ret', 'break', 'continue'):
                break
        body[:] = out
    kw = Prs([]).kw
    for z in walk(ast):
        if z.k == 'idx' and z.a[1].k == 'str':
            ok, valu = val(z.a[1])
            if ok:
                try:
                    name = valu.decode('ascii')
                except UnicodeDecodeError:
                    continue
                if re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', name) and name not in kw:
                    z.k = 'dot'
                    z.a[1] = N('id', [name])
    return ast


def sdec(fn):
    ps = {p.a[0] for p in fn.a[0] if p.k == 'id'}
    rows = []
    todo = list(fn.a[1])
    while todo:
        q = todo.pop()
        if isinstance(q, N):
            if q.k == 'fn':
                continue
            rows.append(q)
            todo.extend(q.a)
        elif isinstance(q, (list, tuple)):
            todo.extend(q)
    loop = any(q.k == 'for' and len(q.a[1]) >= 2 and ung(q.a[1][1]).k == 'un' and ung(q.a[1][1]).a[0] == '#' and ung(ung(q.a[1][1]).a[1]).k == 'id' and ung(ung(q.a[1][1]).a[1]).a[0] in ps for q in rows)
    size = any(q.k == 'un' and q.a[0] == '#' and ung(q.a[1]).k == 'id' and ung(q.a[1]).a[0] in ps for q in rows)
    loop = loop or size and any(q.k == 'wh' for q in rows)
    char = any(q.k == 'dot' and q.a[0].k == 'id' and q.a[0].a[0] == 'string' and q.a[1].a[0] == 'char' for q in rows)
    cach = any(q.k == 'idx' and q.a[0].k == 'id' and q.a[0].a[0] not in ps and q.a[1].k == 'id' and q.a[1].a[0] in ps for q in rows)
    return loop and char and cach


class Sd:
    def __init__(self, fn):
        self.fn = fn
        if any(n.k != 'id' for n in fn.a[0]):
            raise ValueError()
        self.ps = [n.a[0] for n in fn.a[0]]
        self.memo = {}
        self.seen = {}
        self.cal0 = 0
        self.cac0 = None
        self.stp = 0
        self.lim = max(1024, sum(1 for q in walk(fn)) * 256)
        loo0 = [z for z in walk(fn.a[1]) if z.k == 'for']
        if len(loo0) != 1:
            raise ValueError()
        loop = loo0[0]
        if len(loop.a[0]) != 1 or len(loop.a[1]) not in (2, 3):
            raise ValueError()
        end = ung(loop.a[1][1])
        if end.k != 'un' or end.a[0] != '#' or ung(end.a[1]).k != 'id':
            raise ValueError()
        self.inp = ung(end.a[1]).a[0]
        if self.inp not in self.ps:
            raise ValueError()
        ok, beg = val(loop.a[1][0])
        ok2, step = val(loop.a[1][2]) if len(loop.a[1]) == 3 else (True, 1)
        if not ok or not ok2 or beg != 1 or step != 1:
            raise ValueError()
        self.idx = loop.a[0][0].a[0]
        defs = {z.a[0][0].a[0]: z.a[1][0] for z in loop.a[2] if z.k == 'loc' and len(z.a[0]) == len(z.a[1]) == 1}
        sets = [z for z in loop.a[2] if z.k == 'set' and len(z.a[0]) == len(z.a[1]) == 1 and z.a[0][0].k == 'id']
        expr = None
        out = None
        for z in sets:
            rhs = self.can(z.a[1][0], defs)
            lhs = z.a[0][0]
            if rhs.k == 'bin' and rhs.a[0] == '..' and self.eq(rhs.a[1], lhs):
                call = ung(rhs.a[2])
                if call.k == 'call' and len(call.a[1]) == 1 and self.api(call.a[0], 'char'):
                    expr = call.a[1][0]
                    out = lhs.a[0]
        if expr is None:
            raise ValueError()
        self.key = None
        upd = None
        for z in sets:
            name = z.a[0][0].a[0]
            if name != out:
                self.key = name
                upd = self.can(z.a[1][0], defs)
        if self.key is None or upd is None:
            raise ValueError()
        self.out = out
        if len(sets) != 2 or loop.a[2][-2:] != sets or [z.a[0][0].a[0] for z in sets] != [out, self.key]:
            raise ValueError()
        used = set()
        todo = [z.a[1][0] for z in sets]
        while todo:
            q = todo.pop()
            for n in walk(q):
                if n.k == 'id' and n.a[0] in defs and n.a[0] not in used:
                    used.add(n.a[0])
                    todo.append(defs[n.a[0]])
        if set(defs) != used:
            raise ValueError()
        self.cf, self.cm = self.form(expr, True)
        self.kf, self.km = self.form(upd, False)
        pre0 = None
        todo = [fn.a[1]]
        while todo:
            bs = todo.pop()
            for i, z in enumerate(bs):
                if z is loop:
                    pre0 = bs[:i]
                elif z.k == 'if':
                    todo.extend(body for c, body in z.a[0])
                    todo.append(z.a[1])
        if pre0 is None:
            raise ValueError()
        defs = {}
        self.init = None
        self.ostr = None
        for z in pre0:
            if z.k == 'loc':
                for n, q in zip(z.a[0], z.a[1]):
                    defs[n.a[0]] = self.can(q, defs)
            elif z.k == 'set':
                for n, q in zip(z.a[0], z.a[1]):
                    if n.k == 'id' and n.a[0] == self.key:
                        self.init = self.can(q, defs)
                    if n.k == 'id' and n.a[0] == self.out:
                        self.ostr = self.can(q, defs)
        if self.init is None or self.ostr is None:
            raise ValueError()
        self.cidx = None
        for z in fn.a[1]:
            if z.k not in ('loc', 'set'):
                continue
            for q in z.a[1]:
                q = ung(q)
                if q.k == 'idx' and q.a[0].k == 'id' and q.a[1].k == 'id' and q.a[1].a[0] in self.ps and q.a[1].a[0] != self.inp:
                    self.cac0 = q.a[0].a[0]
                    self.cidx = q.a[1].a[0]
        if self.cac0 is None:
            raise ValueError()
        self.vfy(fn, loop)

    def vfy(self, fn, loop):
        loc = set(self.ps)
        for z in walk(fn.a[1]):
            if z.k == 'loc':
                loc.update(n.a[0] for n in z.a[0])
        idx = N('idx', [N('id', [self.cac0]), N('id', [self.cidx])])
        todo = [(fn.a[1], {}, None, False)]
        coun = 0
        while todo:
            bs, env, role, wrt = todo.pop()
            for z in bs:
                if z.k == 'for':
                    if z is not loop or role != 'miss':
                        raise ValueError()
                    tmp = dict(env)
                    for name in (self.key, self.out, self.idx):
                        tmp.pop(name, None)
                    todo.append((z.a[2], tmp, 'loop', False))
                    env.pop(self.key, None)
                    env.pop(self.out, None)
                    continue
                if z.k == 'if':
                    coun += 1
                    if coun != 1 or len(z.a[0]) != 1:
                        raise ValueError()
                    cond, body = z.a[0][0]
                    cond = self.can(cond, env)
                    neg = cond.k == 'un' and cond.a[0] == 'not'
                    cond = cond.a[1] if neg else cond
                    if not self.eq(cond, idx):
                        raise ValueError()
                    miss, hit = (body, z.a[1]) if neg else (z.a[1], body)
                    if not any(q is loop for q in walk(miss)) or any(q is loop for q in walk(hit)):
                        raise ValueError()
                    if not hit or not miss or hit[-1].k != 'ret' or miss[-1].k != 'ret':
                        raise ValueError()
                    todo.extend([(miss, dict(env), 'miss', False), (hit, dict(env), 'hit', False)])
                    continue
                if z.k == 'ret':
                    if len(z.a[0]) != 1:
                        raise ValueError()
                    rhs = self.can(z.a[0][0], env)
                    good = self.eq(rhs, idx) and (role == 'hit' or wrt)
                    good = good or role == 'miss' and rhs.k == 'id' and rhs.a[0] == self.out
                    if not good:
                        raise ValueError()
                    continue
                if z.k not in ('loc', 'set') or z.k == 'set' and z.a[2] != '=':
                    raise ValueError()
                if z.k == 'loc' and not z.a[1]:
                    continue
                if len(z.a[0]) != len(z.a[1]):
                    raise ValueError()
                for lhs, rhs in zip(z.a[0], z.a[1]):
                    rhs = self.can(rhs, env)
                    if not self.pure(rhs, loc | {self.idx}, role == 'loop'):
                        raise ValueError()
                    if lhs.k == 'id':
                        if lhs.a[0] not in loc:
                            raise ValueError()
                        env[lhs.a[0]] = rhs
                    elif role == 'miss' and self.eq(self.can(lhs, env), idx) and rhs.k == 'id' and rhs.a[0] == self.out:
                        wrt = True
                    else:
                        raise ValueError()
        if coun != 1:
            raise ValueError()

    def pure(self, x, loc, call):
        todo = [x]
        while todo:
            q = ung(todo.pop())
            if q.k in ('num', 'str', 'true', 'false', 'nil'):
                continue
            if q.k == 'id' and q.a[0] in loc | {self.cac0, 'string'}:
                continue
            if q.k == 'idx' and q.a[0].k == 'id' and q.a[0].a[0] == self.cac0 and q.a[1].k == 'id' and q.a[1].a[0] == self.cidx:
                continue
            if q.k == 'dot' and any(self.api(q, n) for n in ('char', 'sub', 'byte')):
                continue
            if call and q.k == 'call' and any(self.api(q.a[0], n) for n in ('char', 'sub', 'byte')):
                todo.extend(q.a[1])
                continue
            if call and q.k == 'bin' and q.a[0] in ('+', '-', '*', '%', '..'):
                todo.extend(q.a[1:])
                continue
            raise ValueError()
        return True

    def eq(self, a, b):
        return Em().ex(a) == Em().ex(b)

    def tick(self):
        self.stp += 1
        if self.stp > self.lim:
            bad('string decoder analysis budget exceeded')

    def can(self, x, defs, seen=None):
        self.tick()
        seen = set() if seen is None else seen
        if x.k == 'id' and x.a[0] in defs:
            if x.a[0] in seen:
                raise ValueError()
            return self.can(defs[x.a[0]], defs, seen | {x.a[0]})
        if x.k in ('grp', 'cast'):
            return self.can(x.a[0], defs, seen)
        if x.k in ('num', 'str', 'id', 'nil', 'true', 'false'):
            return x
        if x.k == 'call':
            return N('call', [self.can(x.a[0], defs, seen), [self.can(q, defs, seen) for q in x.a[1]]])
        if x.k in ('dot', 'met'):
            return N(x.k, [self.can(x.a[0], defs, seen), x.a[1]])
        return N(x.k, [self.can(q, defs, seen) if isinstance(q, N) else q for q in x.a])

    def api(self, x, name):
        x = ung(x)
        if x.k != 'dot' or x.a[1].a[0] != name:
            return False
        obj = ung(x.a[0])
        if obj.k == 'id' and obj.a[0] == 'string':
            return True
        if name == 'sub':
            return obj.k == 'id' and obj.a[0] == self.inp
        return name == 'byte' and self.seg(obj)

    def seg(self, x):
        x = ung(x)
        if x.k != 'call' or not self.api(x.a[0], 'sub') or len(x.a[1]) != 3:
            return False
        arg, beg, end = [ung(q) for q in x.a[1]]
        return arg.k == 'id' and arg.a[0] == self.inp and beg.k == end.k == 'id' and beg.a[0] == end.a[0] == self.idx

    def byte(self, x):
        x = ung(x)
        if x.k != 'call' or not self.api(x.a[0], 'byte') or len(x.a[1]) != 1:
            return False
        sub = ung(x.a[1][0])
        if sub.k != 'call' or not self.api(sub.a[0], 'sub') or len(sub.a[1]) != 3:
            return False
        arg, beg, end = [ung(q) for q in sub.a[1]]
        return arg.k == 'id' and arg.a[0] == self.inp and beg.k == end.k == 'id' and beg.a[0] == end.a[0] == self.idx

    def poly(self, x, byte):
        self.tick()
        x = ung(x)
        if byte and self.byte(x):
            return {'$byte': 1}
        ok, v = val(x)
        if ok and type(v) in (int, float):
            return {'': v}
        if x.k == 'id' and x.a[0] in self.ps + [self.key]:
            return {x.a[0]: 1}
        if x.k == 'bin' and x.a[0] in ('+', '-', '*'):
            l, r = self.poly(x.a[1], byte), self.poly(x.a[2], byte)
            if x.a[0] == '*':
                if set(l) <= {''}:
                    return {k: l.get('', 0) * v for k, v in r.items()}
                if set(r) <= {''}:
                    return {k: r.get('', 0) * v for k, v in l.items()}
                raise ValueError()
            out = dict(l)
            for k, v in r.items():
                out[k] = out.get(k, 0) + (v if x.a[0] == '+' else -v)
            return out
        raise ValueError()

    def form(self, x, byte):
        x = ung(x)
        if x.k != 'bin' or x.a[0] != '%':
            raise ValueError()
        ok, mod = val(x.a[2])
        if not ok or type(mod) not in (int, float) or mod <= 0:
            raise ValueError()
        return self.poly(x.a[1], byte), mod

    def dec(self, args):
        if len(args) != len(self.ps):
            bad('string decoder argument count unresolved')
        env = dict(zip(self.ps, args))
        buf = env[self.inp]
        key = env[self.cidx]
        if not isinstance(buf, bytes) or key is None:
            bad('string decoder input or cache index is not constant')
        mark = tuple(args)
        if mark in self.memo:
            return self.memo[mark]
        ok, sta0 = val(self.init, env)
        if not ok or type(sta0) not in (int, float):
            bad('string decoder initial key unresolved')
        good, pref = val(self.ostr, env)
        if not good or not isinstance(pref, bytes):
            bad('string decoder output prefix unresolved')
        c0 = self.cf.get('', 0)
        k0 = self.kf.get('', 0)
        for name in self.ps:
            if self.cf.get(name, 0) or self.kf.get(name, 0):
                if type(env[name]) not in (int, float):
                    bad('string decoder arithmetic argument is not numeric')
                c0 += self.cf.get(name, 0) * env[name]
                k0 += self.kf.get(name, 0) * env[name]
        cb = self.cf.get('$byte', 0)
        ck = self.cf.get(self.key, 0)
        kk = self.kf.get(self.key, 0)
        out = bytearray(len(buf))
        for i, b in enumerate(buf):
            v = (c0 + cb * b + ck * sta0) % self.cm
            if v != int(v) or not 0 <= v <= 255:
                bad('string decoder byte outside range at offset ' + str(i))
            out[i] = int(v)
            sta0 = (k0 + kk * sta0) % self.km
        out = pref + bytes(out)
        key = (type(key).__name__, key)
        if key in self.seen and self.seen[key] != out:
            bad('string decoder cache key has conflicting constant values')
        self.seen[key] = out
        self.memo[mark] = out
        self.cal0 += 1
        return out


class Cp:
    def __init__(self, fn, seed=None):
        self.unk = V('unknown')
        self.pla0 = {}
        self.dec = {}
        self.fctx = {}
        self.fval = {}
        self.freq = {}
        self.safe = set()
        self.plai = set()
        self.pfun = {z.a[0][0].a[0] for z in fn.a[1] if z.k == 'loc' and len(z.a[0]) == len(z.a[1]) == 1 and z.a[0][0].k == 'id' and z.a[0][0].a[0].startswith('var_0_') and z.a[1][0].k == 'dot' and z.a[1][0].a[0].k == 'id' and z.a[1][0].a[0].a[0] == 'table' and z.a[1][0].a[1].a[0] == 'pack'}
        self.boxs = set()
        self.borg = {}
        self.bver = {}
        self.epoc = 0
        self.mut = set()
        self.stp = 0
        self.fold = 0
        self.seed = {} if seed is None else dict(seed)
        self.bini(fn)
        for z in walk(fn):
            if z.k != 'fn' or z is fn:
                continue
            loca = {n.a[0] for n in z.a[0] if n.k == 'id'}
            for n in walk(z.a[1]):
                if n.k == 'loc':
                    loca.update(q.a[0] for q in n.a[0])
            for n in walk(z.a[1]):
                if n.k == 'set':
                    self.mut.update(q.a[0] for q in n.a[0] if q.k == 'id' and q.a[0] not in loca)
        self.blk(fn.a[1], dict(self.seed))
        self.priv(fn)
        self.clea(fn)

    def bini(self, fn):
        defs, rev, adj, own = {}, {}, {}, {}
        for q in walk(fn):
            if q.k not in ('loc', 'set'):
                continue
            for i, lhs in enumerate(q.a[0]):
                if lhs.k != 'id':
                    continue
                name = lhs.a[0]
                rhs = q.a[1][i] if i < len(q.a[1]) else N('nil')
                defs.setdefault(name, []).append(rhs)
                if rhs.k == 'tab' and rhs.tag == 1:
                    own.setdefault(name, set()).add(rhs)
                elif rhs.k == 'id':
                    rev.setdefault(rhs.a[0], set()).add(name)
                    adj.setdefault(name, set()).add(rhs.a[0])
                    adj.setdefault(rhs.a[0], set()).add(name)
        self.btyp = set(own)
        todo = list(own)
        while todo:
            name = todo.pop()
            for dst in rev.get(name, ()):
                if dst not in self.btyp:
                    self.btyp.add(dst)
                    todo.append(dst)
        todo = [name for name in self.btyp if any(not (q.k == 'tab' and q.tag == 1 or q.k == 'id' and q.a[0] in self.btyp) for q in defs.get(name, ()))]
        while todo:
            name = todo.pop()
            if name not in self.btyp:
                continue
            self.btyp.remove(name)
            todo.extend(rev.get(name, ()))
        self.bori = {}
        seen = set()
        for root in own:
            if root in seen:
                continue
            todo, comp, objs = [root], set(), set()
            while todo:
                name = todo.pop()
                if name in seen:
                    continue
                seen.add(name)
                comp.add(name)
                objs.update(own.get(name, ()))
                todo.extend(adj.get(name, ()))
            objs = frozenset(objs)
            for name in comp:
                self.bori[name] = objs

    def bcut(self, env, z13):
        for name in z13:
            v = env.get(name)
            if name in self.btyp and isinstance(v, V) and v.k == 'box':
                obj = N('pending')
                self.borg[obj] = self.borg[v.a[0]] | self.bori.get(name, frozenset())
                env[name] = V('box', [obj])
            else:
                env.pop(name, None)

    def priv(self, fn):
        cach = {p.cac0 for p in self.pla0.values() if p is not None}
        defs, refs, init = {}, {}, []
        pos = {id(q): i for i, q in enumerate(fn.a[1])}
        locs = {p.a[0] for p in fn.a[0] if p.k == 'id'}
        own = {}
        for i, q in enumerate(fn.a[1]):
            if q.k == 'loc':
                locs.update(n.a[0] for n in q.a[0] if n.k == 'id')
                if len(q.a[0]) == len(q.a[1]) == 1 and q.a[0][0].k == 'id' and q.a[1][0].k == 'tab':
                    own[q.a[0][0].a[0]] = i
        todo = [fn]
        while todo:
            self.tick()
            q = todo.pop()
            if isinstance(q, (list, tuple)):
                todo.extend(q)
                continue
            if not isinstance(q, N):
                continue
            if q.k == 'fn':
                if self.pla0.get(id(q)) is None:
                    todo.append(q.a[1])
            elif q.k in ('loc', 'set'):
                if q.k == 'loc' and len(q.a[0]) == len(q.a[1]) == 1 and q.a[0][0].k == 'id':
                    defs[q.a[0][0].a[0]] = q.a[1][0]
                for lhs in q.a[0]:
                    if lhs.k != 'id':
                        todo.append(lhs)
                    elif lhs.a[0] in cach:
                        if len(q.a[0]) != len(q.a[1]) or len(q.a[0]) != 1:
                            bad('string decoder cache initialization unresolved')
                        init.append((q.a[1][0], q))
                todo.extend(q.a[1])
            elif q.k == 'id':
                name = q.a[0]
                if name in cach:
                    bad('string decoder cache observable outside helper')
                refs[name] = refs.get(name, 0) + 1
            elif q.k in ('dot', 'met'):
                todo.append(q.a[0])
            elif q.k == 'mcall':
                todo.extend([q.a[0], q.a[2]])
            else:
                todo.extend(q.a)
        for orig, stmt in init:
            q = orig
            seen = set()
            safe = True
            while q.k == 'id' and q.a[0] in defs and q.a[0] not in seen:
                name = q.a[0]
                seen.add(name)
                if refs.get(name, 0) != 1:
                    safe = False
                    break
                q = defs[name]
            if not safe or q.k != 'tab' or q.a[0]:
                if not self.cprv(fn, pos.get(id(stmt)), orig, locs, own):
                    bad('string decoder cache provenance is not private and empty')
        if cach and not init:
            bad('string decoder cache initialization absent')

    def cprv(self, fn, idx, expr, locs, own):
        bs = fn.a[1]
        if idx is None or idx == 0 or idx + 1 >= len(bs):
            return False
        prev, nxt = bs[idx - 1], bs[idx + 1]
        for q in (prev, nxt):
            if q.k not in ('loc', 'set') or len(q.a[0]) != len(q.a[1]) or len(q.a[0]) != 1 or q.k == 'set' and q.a[2] != '=':
                return False
            if Em().ex(q.a[0][0]) != Em().ex(expr):
                return False
        if prev.a[1][0].k != 'tab' or prev.a[1][0].a[0] or not val(nxt.a[1][0])[0]:
            return False
        if expr.k == 'id':
            return expr.a[0] in locs
        if expr.k not in ('dot', 'idx') or expr.a[0].k != 'id':
            return False
        if expr.k == 'idx' and not val(expr.a[1])[0]:
            return False
        name = expr.a[0].a[0]
        if name not in own or own[name] >= idx - 1:
            return False
        for q in bs[own[name] + 1:idx - 1]:
            self.tick()
            if any(n.k == 'id' and n.a[0] == name for n in walk(q)):
                return False
        return True

    def tick(self):
        self.stp += 1
        if self.stp > 4000000:
            bad('constant propagation step limit exceeded')

    def ex(self, x, env, dep=0):
        self.tick()
        if dep > 160:
            bad('constant propagation depth exceeded')
        k, a = x.k, x.a
        if k == 'id':
            v = env.get(a[0], self.unk)
            if isinstance(v, V) and v.k == 'alias':
                return v.a[0], self.unk
            return (x if isinstance(v, V) else atom(v)), v
        if k in ('num', 'str', 'nil', 'true', 'false'):
            return x, cv(x, {}, {})
        if k == 'fn':
            if x.tag == 2:
                return x, V('factory', [x])
            if id(x) not in self.pla0:
                try:
                    self.pla0[id(x)] = Sd(x)
                except ValueError:
                    if sdec(x):
                        bad('string decoder semantic proof incomplete')
                    self.pla0[id(x)] = None
            plan = self.pla0[id(x)]
            if plan is not None:
                return x, V('decoder', [plan])
            chil = dict(self.seed)
            chil.update((name, v) for name, v in env.items() if isinstance(v, V) and v.k in ('decoder', 'box', 'factory'))
            for p in a[0]:
                if p.k == 'id':
                    chil.pop(p.a[0], None)
            self.blk(a[1], chil)
            return x, self.unk
        if k in ('grp', 'cast'):
            return self.ex(a[0], env, dep + 1)
        if k == 'bin':
            l, lv = self.ex(a[1], env, dep + 1)
            if not isinstance(lv, V) and a[0] in ('and', 'or'):
                if a[0] == 'and' and not tru(lv) or a[0] == 'or' and tru(lv):
                    return l, lv
                return self.ex(a[2], env, dep + 1)
            r, rv = self.ex(a[2], env, dep + 1)
            z = N(k, [a[0], l, r])
            if not isinstance(lv, V) and not isinstance(rv, V):
                ok, v = val(N('bin', [a[0], atom(lv), atom(rv)]))
                if ok:
                    return atom(v), v
            return z, self.unk
        if k == 'un':
            q, v = self.ex(a[1], env, dep + 1)
            z = N(k, [a[0], q])
            if not isinstance(v, V):
                ok, valx = val(N('un', [a[0], atom(v)]))
                if ok:
                    return atom(valx), valx
            return z, self.unk
        if k == 'call':
            f, fv = self.ex(a[0], env, dep + 1)
            pai0 = [self.ex(q, env, dep + 1) for q in a[1]]
            if f.k == 'id' and f.a[0] in self.pfun and all(not isinstance(v, V) for q, v in pai0):
                vals = tuple(v for q, v in pai0)
                fs = [[atom(i + 1), atom(v)] for i, v in enumerate(vals)]
                fs.append([N('key', ['n']), atom(len(vals))])
                return N('tab', [fs], tag=3), V('pack', [vals, self.epoc])
            if isinstance(fv, V) and fv.k == 'factory':
                fn = fv.a[0]
                key = id(fn)
                if key not in self.freq:
                    self.freq[key] = {q.a[0] for q in walk(fn) if q.k == 'id'}
                ctx = {name: v for name, v in env.items() if name in self.freq[key] and isinstance(v, V) and v.k == 'decoder'}
                refs = [v.a[0] if isinstance(v, V) and v.k == 'box' else None for q, v in pai0]
                rels = tuple('same' if u is v else 'apart' if not (self.borg[u] & self.borg[v]) else 'maybe' for i, u in enumerate(refs) for v in refs[i + 1:] if u is not None and v is not None)
                mark = (tuple(sorted((name, id(v.a[0])) for name, v in ctx.items())), tuple(v is not None for v in refs), rels)
                if key in self.fctx:
                    if self.fctx[key] != mark:
                        bad('closure factory capture context differs')
                    valx = self.fval[key]
                else:
                    self.fctx[key] = mark
                    loc = dict(self.seed)
                    loc.update(ctx)
                    for i, p in enumerate(fn.a[0]):
                        loc[p.a[0]] = pai0[i][1] if i < len(pai0) else None
                    q, valx = self.ex(fn.a[1][0].a[0][0], loc, dep + 1)
                    fn.a[1][0].a[0][0] = q
                    self.fval[key] = valx
                return N(k, [f, [q for q, v in pai0]]), valx
            if isinstance(fv, V) and fv.k == 'decoder' and all(not isinstance(v, V) for q, v in pai0):
                v = fv.a[0].dec([v for q, v in pai0])
                self.fold += 1
                return atom(v), v
            self.epoc += 1
            for name in self.mut:
                env.pop(name, None)
            return N(k, [f, [q for q, v in pai0]]), self.unk
        if k == 'mcall':
            obj = self.ex(a[0], env, dep + 1)[0]
            args = [self.ex(q, env, dep + 1)[0] for q in a[2]]
            self.epoc += 1
            for name in self.mut:
                env.pop(name, None)
            return N(k, [obj, a[1], args]), self.unk
        if k in ('dot', 'met'):
            q, v = self.ex(a[0], env, dep + 1)
            node = N(k, [q, a[1]])
            if k == 'dot' and isinstance(v, V) and v.k == 'pack' and v.a[1] == self.epoc:
                valx = self.pget(v, a[1].a[0].encode())
                return atom(valx), valx
            return node, self.cget(node, env)
        if k == 'idx':
            l, lv = self.ex(a[0], env, dep + 1)
            r, rv = self.ex(a[1], env, dep + 1)
            node = N(k, [l, r])
            if isinstance(lv, V) and lv.k == 'pack' and lv.a[1] == self.epoc and not isinstance(rv, V):
                valx = self.pget(lv, rv)
                return atom(valx), valx
            return node, self.cget(node, env)
        if k == 'tab':
            fs = []
            for key, q in a[0]:
                if key is not None and key.k != 'key':
                    key = self.ex(key, env, dep + 1)[0]
                fs.append([key, self.ex(q, env, dep + 1)[0]])
            node = x
            node.a = [fs]
            if x.tag == 1:
                self.borg[node] = frozenset([node])
                return node, V('box', [node])
            return node, self.unk
        return x, self.unk

    def pget(self, v, key):
        vals = v.a[0]
        if key == b'n':
            return len(vals)
        if type(key) in (int, float) and math.isfinite(key) and key == int(key) and 1 <= key <= len(vals):
            return vals[int(key) - 1]
        return None

    def cget(self, q, env):
        item = env.get(self.skey(q, env))
        if item is None or item[0] != self.epoc:
            return self.unk
        for obj, ver in item[2]:
            self.tick()
            if self.bver.get(obj, 0) != ver:
                return self.unk
        return item[1]

    def skey(self, q, env=None):
        if q.k not in ('dot', 'idx') or q.a[0].k != 'id':
            return None
        name = q.a[0].a[0]
        if env is not None:
            v = env.get(name)
            if not isinstance(v, V) or v.k != 'box':
                return None
            name = v.a[0]
        elif name not in self.boxs:
            return None
        ok, key = (True, q.a[1].a[0].encode()) if q.k == 'dot' else val(q.a[1])
        return ('$cell', name, type(key).__name__, key) if ok else None

    def blk(self, body, env, dep=0):
        if dep > 160:
            bad('constant propagation statement depth exceeded')
        out = []
        for z in body:
            self.tick()
            k, a = z.k, z.a
            if k in ('loc', 'set'):
                wide = bool(a[1]) and a[1][-1].k in ('call', 'mcall', '...')
                vals = [self.ex(q, env) for q in a[1]]
                for i, n in enumerate(a[0]):
                    if n.k == 'id':
                        v = vals[i][1] if i < len(vals) else self.unk if wide else None
                        rhs = vals[i][0] if i < len(vals) else atom(None)
                        if isinstance(v, V) and v.k == 'unknown' and rhs.k == 'id' and rhs.a[0].startswith('l_ssa_'):
                            v = V('alias', [rhs])
                        box = rhs.k == 'tab' and rhs.tag == 1
                        if box or rhs.k == 'id' and rhs.a[0] in self.boxs:
                            self.boxs.add(n.a[0])
                        else:
                            self.boxs.discard(n.a[0])
                        env[n.a[0]] = v
                        if rhs.k == 'call' and rhs.a[0].k == 'id' and rhs.a[0].a[0] in self.pfun:
                            self.plai.add(n.a[0])
                        elif rhs.k == 'id' and rhs.a[0] in self.plai:
                            self.plai.add(n.a[0])
                        if isinstance(v, V) and v.k == 'decoder':
                            self.dec[n.a[0]] = v.a[0]
                            self.safe.add(n.a[0])
                    else:
                        if n.k not in ('dot', 'idx'):
                            bad('constant propagation assignment target unresolved')
                        obj = self.ex(n.a[0], env)[0]
                        idx = self.ex(n.a[1], env)[0] if n.k == 'idx' else n.a[1]
                        node = N(n.k, [obj, idx])
                        a[0][i] = node
                        key = self.skey(node, env)
                        if key is not None:
                            v = vals[i][1] if i < len(vals) else self.unk
                            for obj in self.borg[key[1]]:
                                self.tick()
                                self.bver[obj] = self.bver.get(obj, 0) + 1
                            z15 = tuple((obj, self.bver[obj]) for obj in self.borg[key[1]])
                            env[key] = (self.epoc, v if not isinstance(v, V) or v.k == 'decoder' else self.unk, z15)
                        else:
                            self.epoc += 1
                a[1] = [q for q, v in vals]
                out.append(z)
            elif k == 'if':
                bra0 = []
                rest = []
                sele = None
                know = True
                for c, bs in a[0]:
                    cond, v = self.ex(c, env)
                    if not isinstance(v, V):
                        if tru(v):
                            if not bra0:
                                sele = bs
                            else:
                                rest = bs
                            break
                        continue
                    know = False
                    chil = dict(env)
                    self.blk(bs, chil, dep + 1)
                    bra0.append((cond, bs, chil))
                else:
                    rest = a[1]
                if sele is not None or know and not bra0:
                    bs = sele if sele is not None else rest
                    self.blk(bs, env, dep + 1)
                    out.extend(bs)
                else:
                    chil = dict(env)
                    self.blk(rest, chil, dep + 1)
                    sta1 = [en for c, bs, en in bra0] + [chil]
                    merg = {}
                    bphi = {}
                    for name, v in sta1[0].items():
                        if all(name in en and en[name] == v for en in sta1[1:]):
                            merg[name] = v
                        elif isinstance(v, V) and v.k == 'box' and all(isinstance(en.get(name), V) and en[name].k == 'box' for en in sta1[1:]):
                            refs = tuple(en[name].a[0] for en in sta1)
                            if refs not in bphi:
                                obj = N('pending')
                                self.borg[obj] = frozenset().union(*(self.borg[ref] for ref in refs))
                                bphi[refs] = V('box', [obj])
                            merg[name] = bphi[refs]
                    env.clear()
                    env.update(merg)
                    out.append(N('if', [[[c, bs] for c, bs, en in bra0], rest]))
            elif k == 'for':
                a[1] = [self.ex(q, env)[0] for q in a[1]]
                chan = {n.a[0] for q in walk(a[2]) if q.k in ('set', 'loc') for n in q.a[0] if n.k == 'id'}
                chil = dict(env)
                self.bcut(chil, chan | self.mut | {n.a[0] for n in a[0]})
                self.bcut(env, chan | self.mut)
                self.epoc += 1
                self.blk(a[2], chil, dep + 1)
                self.epoc += 1
                out.append(z)
            elif k == 'wh':
                chan = {n.a[0] for q in walk(a[1]) if q.k in ('set', 'loc') for n in q.a[0] if n.k == 'id'}
                chil = dict(env)
                self.bcut(chil, chan | self.mut)
                self.bcut(env, chan | self.mut)
                self.epoc += 1
                a[0] = self.ex(a[0], chil)[0]
                self.blk(a[1], chil, dep + 1)
                self.epoc += 1
                out.append(z)
            elif k == 'ret':
                a[0] = [self.ex(q, env)[0] for q in a[0]]
                out.append(z)
            elif k == 'stmt':
                a[0] = self.ex(a[0], env)[0]
                out.append(z)
            else:
                out.append(z)
        body[:] = out
        return env

    def dsto(self, fn):
        rows = []
        for q in walk(fn):
            if q.k == 'fn':
                rows.append(q.a[1])
            elif q.k == 'if':
                rows.extend(bs for cond, bs in q.a[0])
                rows.append(q.a[1])
            elif q.k == 'for':
                rows.append(q.a[2])
            elif q.k == 'wh':
                rows.append(q.a[1])
        for bs in rows:
            pend, gone, bins = {}, set(), {}
            for q in bs:
                self.tick()
                if q.k not in ('loc', 'set') or len(q.a[0]) != len(q.a[1]) or len(q.a[0]) != 1 or q.k == 'set' and q.a[2] != '=':
                    pend.clear()
                    bins.clear()
                    continue
                lhs, rhs = q.a[0][0], q.a[1][0]
                key, cls = None, None
                if lhs.k == 'id' and lhs.a[0].startswith(('l_', 'var_')):
                    key = ('id', lhs.a[0])
                elif lhs.k == 'dot' and lhs.a[0].k == 'id' and lhs.a[0].a[0] in self.btyp:
                    name = lhs.a[0].a[0]
                    key, cls = ('cell', name, lhs.a[1].a[0]), self.bori.get(name)
                    pend.pop(('id', name), None)
                if key is None or not (rhs.k in ('nil', 'true', 'false', 'num', 'str', 'fn') or rhs.k == 'id' and rhs.a[0] in self.safe or rhs.k == 'tab' and rhs.tag == 3):
                    pend.clear()
                    bins.clear()
                    continue
                if rhs.k == 'id':
                    pend.pop(('id', rhs.a[0]), None)
                prev = pend.get(key)
                if prev is not None:
                    gone.add(id(prev))
                    if prev.k == 'loc':
                        q.k, q.a = 'loc', q.a[:2]
                if cls is not None:
                    z14 = bins.get(cls)
                    if z14 is not None and z14 != key:
                        pend.pop(z14, None)
                    bins[cls] = key
                pend[key] = q
            bs[:] = [q for q in bs if id(q) not in gone]

    def ssto(self, fn):
        info = Cp.__new__(Cp)
        info.bini(fn)
        esc = set()
        todo = [(fn, False)]
        while todo:
            q, safe = todo.pop()
            if isinstance(q, (list, tuple)):
                todo.extend((v, False) for v in q)
                continue
            if not isinstance(q, N):
                continue
            if q.k == 'id':
                if not safe and q.a[0] in info.btyp:
                    esc.update(info.bori.get(q.a[0], ()))
            elif q.k in ('dot', 'met', 'idx'):
                todo.append((q.a[0], True))
                if q.k == 'idx':
                    todo.append((q.a[1], False))
            elif q.k in ('loc', 'set'):
                lhs, rhs = q.a[:2]
                for n in lhs:
                    if n.k != 'id':
                        todo.append((n, False))
                ok = len(lhs) == len(rhs) == 1 and lhs[0].k == 'id' and lhs[0].a[0].startswith(('l_', 'var_'))
                todo.extend((v, ok and v.k == 'id') for v in rhs)
            elif q.k == 'fn':
                todo.append((q.a[1], False))
            elif q.k in ('for', 'iter'):
                todo.extend((v, False) for v in q.a[1:])
            else:
                todo.extend((v, False) for v in q.a)

        try:
            Cs(fn, info, esc, self.safe, self.mut)
        except Cut:
            pass

    def clea(self, fn):
        self.dsto(fn)
        self.ssto(fn)
        rows = []
        todo = [fn.a[1]]
        refs, rds, subs, cnt, defs = {}, {}, {}, {}, {}
        prev, nxt, node = {}, {}, {}
        cac0 = {p.cac0 for p in self.pla0.values() if p is not None}
        while todo:
            bs = todo.pop()
            rows.append(bs)
            for i, z in enumerate(bs):
                key = id(z)
                node[key] = z
                prev[key] = id(bs[i - 1]) if i else None
                nxt[key] = id(bs[i + 1]) if i + 1 < len(bs) else None
                self.tick()
                key = id(z)
                cnt[key] = cnt.get(key, 0) + 1
                expr = []
                chil = []
                if z.k in ('loc', 'set'):
                    expr.extend(z.a[1])
                    expr.extend(n for n in z.a[0] if n.k != 'id')
                    if len(z.a[0]) == len(z.a[1]) == 1 and z.a[0][0].k == 'id':
                        name, rhs = z.a[0][0].a[0], z.a[1][0]
                        safe = name in self.dec or name in cac0
                        if z.k == 'loc' or name.startswith(('l_', 'var_')):
                            safe = safe or rhs.k in ('num', 'str', 'true', 'false', 'nil') or rhs.k == 'fn' and rhs.tag == 2 or rhs.k == 'tab' and (not rhs.a[0] or rhs.tag == 3) or rhs.k == 'id' and (rhs.a[0] in self.safe or rhs.a[0].startswith('l_ssa_'))
                            if rhs.k == 'idx' and rhs.a[0].k == 'id' and rhs.a[0].a[0] in self.plai and val(rhs.a[1])[0]:
                                safe = True
                        if safe:
                            defs.setdefault(name, []).append(z)
                elif z.k == 'if':
                    expr.extend(c for c, body in z.a[0])
                    chil.extend(body for c, body in z.a[0])
                    chil.append(z.a[1])
                elif z.k == 'for':
                    expr.extend(z.a[1])
                    chil.append(z.a[2])
                elif z.k == 'wh':
                    expr.append(z.a[0])
                    chil.append(z.a[1])
                elif z.k in ('stmt', 'ret'):
                    expr.extend(z.a[0] if z.k == 'ret' else [z.a[0]])
                rea0 = []
                stk = list(expr)
                while stk:
                    q = stk.pop()
                    if isinstance(q, list):
                        stk.extend(q)
                    elif isinstance(q, N):
                        if q.k == 'id':
                            rea0.append(q.a[0])
                        elif q.k == 'fn':
                            chil.append(q.a[1])
                        elif q.k in ('dot', 'met'):
                            stk.append(q.a[0])
                        elif q.k == 'mcall':
                            stk.extend([q.a[0], q.a[2]])
                        else:
                            stk.extend(q.a)
                rds[key] = rea0
                subs[key] = [id(q) for body in chil for q in body]
                todo.extend(chil)
                for name in rea0:
                    refs[name] = refs.get(name, 0) + 1
        def dead(a, b):
            if a is None or b is None or cnt[id(a)] != 1 or cnt[id(b)] != 1:
                return False
            span = False
            while b.k in ('do', 'wh'):
                self.tick()
                if a.k != 'set' or len(a.a[0]) != 1 or a.a[0][0].k not in ('id', 'dot', 'idx'):
                    return False
                span = True
                if b.k == 'wh':
                    ok, v = val(b.a[0])
                    if not ok or not tru(v):
                        return False
                    body = b.a[1]
                else:
                    body = b.a[0]
                if not body or cnt.get(id(body[0])) != 1:
                    return False
                b = body[0]
            if a.k not in ('loc', 'set') or b.k not in ('loc', 'set') or len(a.a[0]) != len(a.a[1]) or len(a.a[0]) != 1 or len(b.a[0]) != len(b.a[1]) or len(b.a[0]) != 1:
                return False
            if a.k == 'set' and a.a[2] != '=' or b.k == 'set' and b.a[2] != '=':
                return False
            lhs, rhs = a.a[0][0], a.a[1][0]
            if lhs.k == 'id':
                if span and b.k != 'set':
                    return False
                if not lhs.a[0].startswith(('l_', 'var_')):
                    return False
            elif self.skey(lhs) is None:
                return False
            if Em().ex(lhs) != Em().ex(b.a[0][0]):
                return False
            if rhs.k not in ('num', 'str', 'true', 'false', 'nil', 'fn') and not (rhs.k == 'tab' and not rhs.a[0]) and not (rhs.k == 'id' and rhs.a[0] in self.safe):
                return False
            rhs = b.a[1][0]
            if rhs.k not in ('num', 'str', 'true', 'false', 'nil', 'id') and not (rhs.k == 'tab' and not rhs.a[0]):
                return False
            if lhs.k == 'id' and rhs.k == 'id' and lhs.a[0] == rhs.a[0]:
                return False
            return True
        work = [name for name in defs if refs.get(name, 0) == 0]
        work.extend(('$dead', key) for key, z in node.items() if dead(z, node.get(nxt[key])))
        gone = set()
        while work:
            self.tick()
            name = work.pop()
            if isinstance(name, tuple):
                key = name[1]
                if key in gone or not dead(node[key], node.get(nxt.get(key))):
                    continue
                if node[key].k == 'loc':
                    q = node[nxt[key]]
                    q.k, q.a = 'loc', q.a[:2]
                stk = [key]
            else:
                if refs.get(name, 0):
                    continue
                stk = [id(z) for z in defs[name] if id(z) not in gone]
            while stk:
                key = stk.pop()
                if cnt.get(key, 0) <= 0:
                    continue
                cnt[key] -= 1
                if cnt[key] == 0:
                    gone.add(key)
                    a, b = prev.get(key), nxt.get(key)
                    if a is not None:
                        nxt[a] = b
                    if b is not None:
                        prev[b] = a
                    if a is not None and a not in gone and dead(node[a], node.get(b)):
                        work.append(('$dead', a))
                for ref in rds.get(key, ()):
                    refs[ref] -= 1
                    if refs[ref] == 0 and ref in defs:
                        work.append(ref)
                stk.extend(subs.get(key, ()))
        for bs in reversed(rows):
            out = []
            for z in bs:
                if id(z) in gone:
                    continue
                if z.k == 'if' and not z.a[1] and all(not body for c, body in z.a[0]):
                    safe = True
                    for c, body in z.a[0]:
                        c = ung(c)
                        if c.k == 'bin' and c.a[0] == '>=' and c.a[1].k == 'dot' and c.a[1].a[0].k == 'id' and c.a[1].a[0].a[0] in self.plai and c.a[1].a[1].a[0] == 'n' and val(c.a[2])[0]:
                            continue
                        safe = False
                    if safe:
                        continue
                out.append(z)
            bs[:] = out


class Cut(Exception):
    pass


class Cs:
    def __init__(self, fn, info, esc, safe, mut):
        self.info, self.esc = info, esc
        self.safe, self.mut = safe, mut
        self.obs = set(esc)
        self.fcnt = {}
        for q in walk(fn):
            if q.k == 'fn':
                self.fcnt[id(q)] = self.fcnt.get(id(q), 0) + 1
        self.caps = {}
        self.phis = {}
        self.alt = {}
        self.cap = set()
        self.pub = set(esc)
        self.cost = 0
        self.lim = max(10000, sum(1 for q in walk(fn)) * 32)
        cnt = {}
        for q in walk(fn):
            lhs = q.a[0] if q.k in ('loc', 'set', 'for', 'iter', 'fn') else []
            for n in lhs:
                if n.k == 'id':
                    cnt[n.a[0]] = cnt.get(n.a[0], 0) + 1
        self.one = {n for n, c in cnt.items() if c == 1}
        self.func(fn, {}, False, 0)
        self.func(fn, {}, True, 0)

    def tick(self):
        self.cost += 1
        if self.cost > self.lim:
            raise Cut()

    def alts(self, obj):
        return self.alt.get(obj, frozenset([obj]))

    def publ(self, objs, env):
        vals = set(env.values())
        vals.update(objs)
        for obj in objs:
            for v in vals:
                self.tick()
                if self.alts(v) & self.alts(obj):
                    self.pub.add(v)

    def gate(self, pend, env, edit):
        if edit:
            for k in list(pend):
                self.tick()
                if k[0] in self.pub:
                    pend.pop(k, None)
        for n in self.mut:
            self.tick()
            env.pop(n, None)

    def func(self, fn, env, edit, dep):
        if edit and self.fcnt.get(id(fn), 0) > 1:
            return set()
        if dep > 160:
            raise Cut()
        own = set()
        todo = list(fn.a[1])
        while todo:
            self.tick()
            q = todo.pop()
            if isinstance(q, N):
                if q.k == 'fn':
                    continue
                if q.k == 'tab' and q.tag == 1:
                    own.add(q)
                todo.extend(q.a)
            elif isinstance(q, (list, tuple)):
                todo.extend(q)
        env = {n: v for n, v in env.items() if n in self.one}
        for n in fn.a[0]:
            env.pop(n.a[0], None)
        prev, pubs = self.cap, self.pub
        self.cap = set()
        self.pub = set(self.caps.get(id(fn), ())) | self.esc
        self.body(fn.a[1], env, own, edit, dep + 1)
        cap = self.cap
        if not edit:
            self.caps.setdefault(id(fn), set()).update(cap)
            self.obs.update(cap)
        self.cap, self.pub = prev, pubs
        return cap

    def expr(self, q, env, own, pend, edit, dep):
        self.tick()
        if dep > 160:
            raise Cut()
        if isinstance(q, (list, tuple)):
            for v in q:
                self.expr(v, env, own, pend, edit, dep + 1)
            return
        if not isinstance(q, N):
            return
        if q.k == 'fn':
            cap = self.func(q, env, edit, dep + 1)
            if edit:
                self.publ(self.caps.get(id(q), ()), env)
            else:
                self.cap.update(o for o in cap if not self.alts(o) <= own)
            return
        if q.k in ('dot', 'idx', 'met'):
            base = q.a[0]
            name = base.a[0] if base.k == 'id' else None
            if name in self.info.btyp:
                obj = env.get(name)
                objs = {obj} if obj is not None else self.info.bori.get(name, frozenset())
                if edit:
                    for k in list(pend):
                        self.tick()
                        if any(self.alts(k[0]) & self.alts(o) for o in objs):
                            pend.pop(k, None)
                else:
                    self.cap.update(o for o in objs if not self.alts(o) <= own)
            else:
                self.gate(pend, env, edit)
            self.expr(base, env, own, pend, edit, dep + 1)
            if q.k == 'idx':
                self.expr(q.a[1], env, own, pend, edit, dep + 1)
            return
        if q.k == 'id':
            if q.a[0] not in self.safe:
                self.gate(pend, env, edit)
            return
        if q.k == 'mcall':
            self.expr(q.a[0], env, own, pend, edit, dep + 1)
            self.expr(q.a[2], env, own, pend, edit, dep + 1)
            self.gate(pend, env, edit)
            return
        if q.k == 'tab':
            for k, v in q.a[0]:
                if k is not None and k.k != 'key':
                    self.expr(k, env, own, pend, edit, dep + 1)
                self.expr(v, env, own, pend, edit, dep + 1)
            return
        for v in q.a:
            self.expr(v, env, own, pend, edit, dep + 1)
        if q.k in ('call', 'un', 'bin'):
            self.gate(pend, env, edit)

    def join(self, rows, pubs):
        if not rows:
            return {}
        env = {}
        self.pub = set().union(*pubs)
        for n in rows[0]:
            self.tick()
            vals = tuple(r.get(n) for r in rows)
            if any(v is None for v in vals):
                continue
            obj = vals[0]
            if any(v is not obj for v in vals):
                if vals not in self.phis:
                    phi = object()
                    self.phis[vals] = phi
                    self.alt[phi] = frozenset().union(*(self.alts(v) for v in vals))
                obj = self.phis[vals]
                if any(v in p for v, p in zip(vals, pubs)):
                    self.pub.add(obj)
                else:
                    self.pub.discard(obj)
            env[n] = obj
        return env

    def body(self, bs, env, own, edit, dep):
        if dep > 160:
            raise Cut()
        orig, decl = dict(env), set()
        pend, gone = {}, set()
        for q in bs:
            self.tick()
            if q.k == 'if':
                pend.clear()
                for c, rows in q.a[0]:
                    self.expr(c, env, own, pend, edit, dep + 1)
                base, pubs, outs = set(self.pub), [], []
                for rows in [rows for c, rows in q.a[0]] + [q.a[1]]:
                    self.pub = set(base)
                    outs.append(self.body(rows, dict(env), own, edit, dep + 1))
                    pubs.append(self.pub)
                env = self.join(outs, pubs)
                continue
            if q.k == 'do':
                pend.clear()
                env = self.body(q.a[0], dict(env), own, edit, dep + 1)
                continue
            if q.k in ('for', 'iter', 'wh', 'rep'):
                pend.clear()
                args = q.a[1] if q.k in ('for', 'iter') else q.a[0] if q.k == 'wh' else q.a[1]
                self.expr(args, env, own, pend, edit, dep + 1)
                ctx = {n: v for n, v in env.items() if n in self.one}
                rows = q.a[2] if q.k in ('for', 'iter') else q.a[1] if q.k == 'wh' else q.a[0]
                self.pub.update(self.obs)
                self.pub.update(own)
                self.pub.update(env.values())
                for obj in self.obs:
                    self.pub.update(self.alts(obj))
                self.body(rows, ctx, own, edit, dep + 1)
                env = {n: v for n, v in env.items() if n in self.one}
                continue
            if q.k in ('loc', 'set'):
                lhs, rhs = q.a[:2]
                self.expr(rhs, env, own, pend, edit, dep + 1)
                for n in lhs:
                    if n.k == 'id' and q.k == 'set' and n.a[0] not in self.safe:
                        self.gate(pend, env, edit)
                    if n.k != 'id':
                        name = n.a[0].a[0] if n.k == 'dot' and n.a[0].k == 'id' else None
                        obj = env.get(name)
                        if obj is not None and name in self.info.btyp:
                            if not edit and not self.alts(obj) <= own:
                                self.cap.add(obj)
                        else:
                            self.expr(n, env, own, pend, edit, dep + 1)
                if len(lhs) == len(rhs) == 1 and lhs[0].k == 'dot' and lhs[0].a[0].k == 'id' and q.k == 'set' and q.a[2] == '=':
                    name = lhs[0].a[0].a[0]
                    obj = env.get(name)
                    val0 = rhs[0]
                    pure = val0.k in ('nil', 'true', 'false', 'num', 'str') or val0.k == 'id' and val0.a[0] in self.safe
                    if edit and obj is not None and not self.alts(obj) & self.esc and name in self.info.btyp:
                        key = (obj, lhs[0].a[1].a[0])
                        if key in pend:
                            gone.add(id(pend.pop(key)))
                        if pure:
                            pend[key] = q
                vals = [v if v.k == 'tab' and v.tag == 1 else env.get(v.a[0]) if v.k == 'id' else None for v in rhs]
                for i, n in enumerate(lhs):
                    if n.k != 'id':
                        continue
                    if q.k == 'loc':
                        decl.add(n.a[0])
                    obj = vals[i] if i < len(vals) else None
                    if obj is None or q.k == 'set' and q.a[2] != '=':
                        env.pop(n.a[0], None)
                    else:
                        env[n.a[0]] = obj
                continue
            self.expr(q.a, env, own, pend, edit, dep + 1)
            if q.k in ('ret', 'break', 'continue'):
                pend.clear()
        if edit:
            bs[:] = [q for q in bs if id(q) not in gone]
        for n in decl:
            if n in orig:
                env[n] = orig[n]
            else:
                env.pop(n, None)
        return env


def tree(ast):
    root = [None]
    todo = [(ast, root, 0, 0)]
    cost = 0
    while todo:
        src, dst, key, dep = todo.pop()
        cost += 1
        if cost > 8000000 or dep > 640:
            bad('syntax tree copy budget exceeded')
        if isinstance(src, N):
            obj = N(src.k, [], src.s, src.e, src.ln, src.tag)
            dst[key] = obj
            todo.append((src.a, obj.__dict__, 'a', dep + 1))
        elif isinstance(src, (list, tuple)):
            obj = [None] * len(src)
            dst[key] = obj
            todo.extend((v, obj, i, dep + 1) for i, v in enumerate(src))
        elif isinstance(src, dict):
            obj = {}
            dst[key] = obj
            todo.extend((v, obj, k, dep + 1) for k, v in src.items())
        else:
            dst[key] = src
    return root[0]


def trim(ast, rn):
    ctx, pos, par, lps = {}, {}, {}, set()
    todo, rows = [(ast, 0, False)], [ast] if isinstance(ast, list) else []
    while todo:
        q, own, loop = todo.pop()
        if isinstance(q, (list, tuple)):
            todo.extend((v, own, loop) for v in reversed(q))
            continue
        if not isinstance(q, N):
            continue
        pos[id(q)] = len(pos)
        loop = loop or q.k in ('for', 'iter', 'wh', 'rep')
        if loop:
            lps.add(id(q))
        if q.k == 'fn':
            par[id(q)] = own
            own = id(q)
            rows.append(q.a[1])
        elif q.k == 'if':
            rows.extend(bs for cond, bs in q.a[0])
            rows.append(q.a[1])
        elif q.k in ('for', 'iter'):
            rows.append(q.a[2])
        elif q.k in ('wh', 'rep', 'do'):
            rows.append(q.a[0] if q.k != 'wh' else q.a[1])
        if q.k == 'id':
            ctx[id(q)] = own
        todo.extend((v, own, loop) for v in reversed(q.a))
    caps = {}
    for r in rn.sy:
        own = ctx.get(id(r['refs'][0]))
        for n in r['refs']:
            cur = ctx.get(id(n))
            if cur == own:
                continue
            while cur in par and par[cur] != own:
                cur = par[cur]
            caps[id(r)] = min(caps.get(id(r), len(pos)), pos.get(cur, 0))
    edit = False
    for bs in rows:
        pend, gone = {}, set()
        for z in bs:
            if z.k not in ('loc', 'set', 'stmt'):
                pend.clear()
                continue
            expr = z.a[1] if z.k in ('loc', 'set') else z.a[0]
            for n in walk(expr):
                if n.k == 'id' and id(n) in rn.ref:
                    pend.pop(id(rn.ref[id(n)]), None)
            if z.k == 'stmt':
                continue
            for n in z.a[0]:
                if n.k != 'id':
                    for q in walk(n):
                        if q.k == 'id' and id(q) in rn.ref:
                            pend.pop(id(rn.ref[id(q)]), None)
            for n in z.a[0]:
                if n.k != 'id':
                    continue
                rec = rn.ref.get(id(n))
                if rec is None or pos[id(z)] >= caps.get(id(rec), len(pos)) or id(z) in lps and id(rec) in caps:
                    continue
                key = id(rec)
                if z.k == 'set' and z.a[2] != '=':
                    pend.pop(key, None)
                    continue
                if key in pend:
                    gone.add(id(pend.pop(key)))
                if z.k == 'set' and len(z.a[0]) == len(z.a[1]) == 1:
                    q = ung(z.a[1][0])
                    if q.k in ('num', 'str', 'true', 'false', 'nil') or q.k == 'id' and id(q) in rn.ref:
                        pend[key] = z
        if gone:
            edit = True
            bs[:] = [z for z in bs if id(z) not in gone]
    return edit


def back(ast):
    rn = Rn(ast)
    ctx, todo, bs = {}, [(ast, 0)], []
    nds = list(walk(ast))
    for q in nds:
        if q.k == 'fn':
            bs.append(q.a[1])
    if isinstance(ast, list):
        bs.append(ast)
    while todo:
        q, own = todo.pop()
        if isinstance(q, (list, tuple)):
            todo.extend((n, own) for n in q)
            continue
        if not isinstance(q, N):
            continue
        if q.k == 'fn':
            own = id(q)
        if q.k == 'id':
            ctx[id(q)] = own
        todo.extend((n, own) for n in q.a)
    caps = {id(r) for r in rn.sy if any(ctx[id(n)] != ctx[id(r['refs'][0])] for n in r['refs'])}
    alls = {id(r) for r in rn.sy}
    cost, lim, cac, gone = 0, max(10000, len(nds) * 48), {}, set()

    def tick(n=1):
        nonlocal cost
        cost += n
        if cost > lim:
            raise Cut()

    def read(q):
        key = id(q)
        if key not in cac:
            vals = set()
            for n in walk(q):
                tick()
                if n.k == 'id' and id(n) in rn.ref:
                    vals.add(id(rn.ref[id(n)]))
            cac[key] = frozenset(vals)
        return cac[key]

    def flow(rows, live, dep=0):
        tick(len(live))
        if dep > 160:
            raise Cut()
        live = set(live)
        for q in reversed(rows):
            tick()
            if q.k == 'if':
                out = set(live)
                for c, arm in q.a[0]:
                    out.update(flow(arm, live, dep + 1))
                    out.update(read(c))
                out.update(flow(q.a[1], live, dep + 1))
                live = out
            elif q.k == 'do':
                live = flow(q.a[0], live, dep + 1)
            elif q.k in ('wh', 'rep', 'for', 'iter'):
                arm = q.a[2] if q.k in ('for', 'iter') else q.a[1] if q.k == 'wh' else q.a[0]
                live.update(flow(arm, alls, dep + 1))
                live.update(read(q))
            elif q.k == 'ret':
                live = set(read(q.a))
            elif q.k in ('break', 'continue'):
                live = set(alls)
            elif q.k in ('set', 'loc'):
                lhs, rhs = q.a[:2]
                rec = rn.ref.get(id(lhs[0])) if len(lhs) == 1 and lhs[0].k == 'id' else None
                if q.k == 'set' and q.a[2] == '=' and rec is not None and id(rec) not in live and id(rec) not in caps and len(rhs) == 1:
                    val0 = ung(rhs[0])
                    if val0.k in ('num', 'str', 'nil', 'true', 'false') or val0.k == 'id' and id(val0) in rn.ref:
                        gone.add(id(q))
                        continue
                for n in lhs:
                    if n.k == 'id' and id(n) in rn.ref and (q.k == 'loc' or q.a[2] == '='):
                        live.discard(id(rn.ref[id(n)]))
                for n in lhs:
                    if n.k != 'id' or q.k == 'set' and q.a[2] != '=':
                        live.update(read(n))
                live.update(read(rhs))
            else:
                live.update(read(q.a))
        return live

    try:
        for rows in bs:
            flow(rows, set())
    except Cut:
        return 0
    for q in nds:
        if q.k == 'if':
            bs.extend(rows for c, rows in q.a[0])
            bs.append(q.a[1])
        elif q.k in ('do', 'wh', 'rep', 'for', 'iter'):
            bs.append(q.a[2] if q.k in ('for', 'iter') else q.a[1] if q.k == 'wh' else q.a[0])
    for rows in bs:
        rows[:] = [q for q in rows if id(q) not in gone]
    return len(gone)


def box(ast):
    rn = Rn(ast)
    par, ups, wrts, tabs, als, bs = {}, {}, {}, {}, {}, []
    todo = [(ast, None)]
    while todo:
        q, up = todo.pop()
        if isinstance(q, (list, tuple)):
            todo.extend((v, up) for v in q)
            continue
        if not isinstance(q, N):
            continue
        par[id(q)] = up
        todo.extend((v, q) for v in q.a)
        if q.k == 'fn':
            bs.append(q.a[1])
        elif q.k == 'if':
            bs.extend(rows for c, rows in q.a[0])
            bs.append(q.a[1])
        elif q.k in ('for', 'iter'):
            bs.append(q.a[2])
        elif q.k in ('wh', 'rep', 'do'):
            bs.append(q.a[1] if q.k == 'wh' else q.a[0])
        if q.k not in ('loc', 'set'):
            continue
        for n in q.a[0]:
            rec = rn.ref.get(id(n))
            if n.k == 'id' and rec is not None:
                key = id(rec)
                ups.setdefault(key, key)
                wrts[key] = wrts.get(key, 0) + 1
        if q.k != 'loc' or len(q.a[0]) != 1 or len(q.a[1]) != 1:
            continue
        rec = rn.ref.get(id(q.a[0][0]))
        if rec is None:
            continue
        key, rhs = id(rec), q.a[1][0]
        if rhs.k == 'tab' and rhs.tag == 1 and len(rhs.a[0]) == 1:
            fld, val0 = rhs.a[0][0]
            if fld is not None and fld.k == 'key':
                tabs[key] = (q, fld.a[0], val0)
        elif rhs.k == 'id' and id(rhs) in rn.ref:
            als[key] = (q, id(rn.ref[id(rhs)]))

    def find(key):
        while ups[key] != key:
            ups[key] = ups[ups[key]]
            key = ups[key]
        return key

    rank = {key: 0 for key in ups}
    for key, (q, src) in als.items():
        if src not in ups:
            continue
        a, b = find(key), find(src)
        if a == b:
            continue
        if rank[a] < rank[b]:
            a, b = b, a
        ups[b] = a
        if rank[a] == rank[b]:
            rank[a] += 1
    grps = {}
    for key in ups:
        grps.setdefault(find(key), []).append(key)
    refs = {id(r): r for r in rn.sy}
    used = {q.a[0] for q in walk(ast) if q.k == 'id'}
    gone, cnt = set(), 0
    for keys in grps.values():
        rts = [key for key in keys if key in tabs]
        if len(rts) != 1 or any(wrts[key] != 1 for key in keys):
            continue
        root = rts[0]
        if any(key != root and key not in als for key in keys):
            continue
        decl, fld, val0 = tabs[root]
        hits, good = [], True
        for key in keys:
            for n in refs[key]['refs']:
                up = par.get(id(n))
                if up is None:
                    good = False
                    break
                if up.k == 'loc' and n in up.a[0]:
                    continue
                if up.k == 'loc' and len(up.a[0]) == len(up.a[1]) == 1 and up.a[1][0] is n:
                    dst = rn.ref.get(id(up.a[0][0]))
                    if dst is not None and id(dst) in als and find(id(dst)) == find(root):
                        continue
                if up.k == 'dot' and up.a[0] is n and up.a[1].a[0] == fld:
                    hits.append(up)
                    continue
                good = False
                break
            if not good:
                break
        if not good:
            continue
        cnt += 1
        name = 'l_cell_' + str(cnt)
        while name in used:
            name += '_'
        used.add(name)
        decl.a[0][0].a[0] = name
        decl.a[1][0] = val0
        for q in hits:
            q.k, q.a, q.tag = 'id', [name], 0
        gone.update(id(als[key][0]) for key in keys if key != root)
    if isinstance(ast, list):
        bs.append(ast)
    for rows in bs:
        rows[:] = [q for q in rows if id(q) not in gone]
    return cnt


def simp(ast):
    rn = Rn(ast)
    bs = [ast] if isinstance(ast, list) else []
    for q in walk(ast):
        if q.k == 'fn':
            bs.append(q.a[1])
        elif q.k == 'if':
            bs.extend(rows for c, rows in q.a[0])
            bs.append(q.a[1])
        elif q.k in ('for', 'iter'):
            bs.append(q.a[2])
        elif q.k in ('wh', 'rep', 'do'):
            bs.append(q.a[1] if q.k == 'wh' else q.a[0])
    cnt = 0
    for rows in bs:
        out = []
        for q in rows:
            if out:
                prev = out[-1]
                if prev.k == 'loc' and len(prev.a[0]) == 1 and not prev.a[1] and q.k == 'set' and q.a[2] == '=' and len(q.a[0]) == len(q.a[1]) == 1 and q.a[0][0].k == 'id':
                    rec = rn.ref.get(id(prev.a[0][0]))
                    same = rec is not None and rn.ref.get(id(q.a[0][0])) is rec
                    if same and not any(n.k == 'id' and rn.ref.get(id(n)) is rec for n in walk(q.a[1])):
                        prev.a[1] = q.a[1]
                        cnt += 1
                        continue
                if prev.k == 'loc' and len(prev.a[0]) == len(prev.a[1]) == 1 and q.k == 'ret' and len(q.a[0]) == 1 and q.a[0][0].k == 'id':
                    rec = rn.ref.get(id(prev.a[0][0]))
                    if rec is not None and len(rec['refs']) == 2 and rn.ref.get(id(q.a[0][0])) is rec:
                        rhs = prev.a[1][0]
                        q.a[0][0] = N('grp', [rhs]) if rhs.k in ('call', 'mcall', '...') else rhs
                        out.pop()
                        cnt += 1
            out.append(q)
        rows[:] = out
    return cnt


def fuse(ast):
    rn = Rn(ast)
    slts, ctx, todo, rows = {}, {}, [(ast, None, 0, 0)], []
    if isinstance(ast, list):
        rows.append(ast)
    while todo:
        q, dst, idx, own = todo.pop()
        if isinstance(q, (list, tuple)):
            todo.extend((v, q, i, own) for i, v in enumerate(q))
            continue
        if not isinstance(q, N):
            continue
        slts[id(q)] = (dst, idx)
        if q.k == 'fn':
            own = id(q)
            rows.append(q.a[1])
        elif q.k == 'if':
            rows.extend(bs for c, bs in q.a[0])
            rows.append(q.a[1])
        elif q.k in ('for', 'iter'):
            rows.append(q.a[2])
        elif q.k in ('wh', 'rep', 'do'):
            rows.append(q.a[1] if q.k == 'wh' else q.a[0])
        if q.k == 'id':
            ctx[id(q)] = own
        todo.append((q.a, None, 0, own))
    caps = {id(r) for r in rn.sy if any(ctx[id(n)] != ctx[id(r['refs'][0])] for n in r['refs'])}

    def head(q, ref, dep=0):
        if dep > 160:
            return False, False
        if q is ref:
            return True, True
        if q.k == 'id':
            r = rn.ref.get(id(q))
            return False, r is not None and id(r) not in caps
        if q.k in ('num', 'nil', 'true', 'false') or q.k == 'str' and not q.a[0].startswith('`'):
            return False, True
        if q.k in ('grp', 'cast'):
            return head(q.a[0], ref, dep + 1)
        if q.k in ('dot', 'un'):
            return head(q.a[0] if q.k == 'dot' else q.a[1], ref, dep + 1)[0], False
        if q.k == 'call':
            pts = [q.a[0]] + q.a[1]
        elif q.k == 'mcall':
            return head(q.a[0], ref, dep + 1)[0], False
        elif q.k == 'idx':
            pts = q.a
        elif q.k == 'bin':
            pts = q.a[1:2] if q.a[0] in ('and', 'or') else q.a[1:]
        else:
            return False, False
        for n in pts:
            hit, pure = head(n, ref, dep + 1)
            if hit:
                return True, False
            if not pure:
                break
        return False, False

    cnt = 0
    for bs in rows:
        out = []
        for q in bs:
            if out and out[-1].k == 'loc':
                prev = out[-1]
                if len(prev.a[0]) == len(prev.a[1]) == 1:
                    rec = rn.ref.get(id(prev.a[0][0]))
                    rhs = prev.a[1][0]
                    if rec is not None and len(rec['refs']) == 2 and id(rec) not in caps and rhs.k != 'fn':
                        ref = rec['refs'][1]
                        vals = q.a[1] if q.k in ('set', 'loc') and all(n.k == 'id' for n in q.a[0]) else q.a[0] if q.k == 'ret' else [q.a[0]] if q.k == 'stmt' else []
                        if q.k == 'set' and q.a[2] != '=':
                            vals = []
                        if len(vals) == 1 and head(vals[0], ref)[0]:
                            dst, idx = slts[id(ref)]
                            if isinstance(dst, list):
                                dst[idx] = N('grp', [rhs]) if rhs.k in ('call', 'mcall', '...') else rhs
                                out.pop()
                                cnt += 1
            out.append(q)
        bs[:] = out
    return cnt


def flow(ast):
    rows = [ast] if isinstance(ast, list) else []
    ends = list(rows)
    nds = list(walk(ast))
    for q in nds:
        if q.k == 'fn':
            rows.append(q.a[1])
            ends.append(q.a[1])
        elif q.k == 'if':
            rows.extend(bs for c, bs in q.a[0])
            rows.append(q.a[1])
        elif q.k in ('for', 'iter'):
            rows.append(q.a[2])
        elif q.k in ('wh', 'rep', 'do'):
            rows.append(q.a[1] if q.k == 'wh' else q.a[0])

    def cond(q):
        q = ung(q)
        while q.k == 'un' and q.a[0] == 'not':
            sub = ung(q.a[1])
            if sub.k == 'un' and sub.a[0] == 'not':
                q = ung(sub.a[1])
            elif sub.k == 'bin' and sub.a[0] in ('==', '~='):
                return N('bin', ['~=' if sub.a[0] == '==' else '==', sub.a[1], sub.a[2]])
            else:
                break
        return q

    cnt = 0
    for q in reversed(nds):
        if q.k == 'if':
            q.a[0] = [(cond(c), bs) for c, bs in q.a[0]]
            if len(q.a[1]) == 1 and q.a[1][0].k == 'if':
                sub = q.a[1][0]
                q.a[0].extend(sub.a[0])
                q.a[1] = sub.a[1]
                cnt += 1
            if len(q.a[0]) == 1 and len(q.a[0][0][1]) == len(q.a[1]) == 1:
                c, arm = q.a[0][0]
                a, b = arm[0], q.a[1][0]
                if a.k == b.k == 'ret' and len(a.a[0]) == len(b.a[0]) == 1:
                    a, b = ung(a.a[0][0]), ung(b.a[0][0])
                    if a.k in ('true', 'false') and b.k in ('true', 'false') and a.k != b.k:
                        rhs = N('un', ['not', c])
                        if a.k == 'true':
                            rhs = c if c.k == 'bin' and c.a[0] in ('==', '~=', '<', '>', '<=', '>=') or c.k == 'un' and c.a[0] == 'not' or c.k in ('true', 'false') else N('un', ['not', rhs])
                        q.k, q.a = 'ret', [[rhs]]
                        cnt += 1
        elif q.k in ('wh', 'rep', 'iex'):
            idx = 1 if q.k == 'rep' else 0
            q.a[idx] = cond(q.a[idx])
    while ends:
        bs = ends.pop()
        if not bs:
            continue
        q = bs[-1]
        if q.k == 'ret' and not q.a[0]:
            bs.pop()
            cnt += 1
        elif q.k == 'if':
            ends.extend(arm for c, arm in q.a[0])
            ends.append(q.a[1])
        elif q.k == 'do':
            ends.append(q.a[0])
    return cnt


def tidy(ast):
    if isinstance(ast, list):
        ast[:] = tree(ast)
    else:
        ast.a = tree(ast.a)
    back(ast)
    box(ast)
    simp(ast)
    rn = Rn(ast)
    if trim(ast, rn):
        rn = Rn(ast)
    skip, wrts, cand = set(), {}, {}
    bods = [ast] if isinstance(ast, list) else []
    for z in walk(ast):
        lhs = []
        if z.k in ('loc', 'set'):
            lhs = z.a[0]
            if z.k == 'loc' or z.a[2] == '=':
                skip.update(id(n) for n in lhs if n.k == 'id')
            if z.k == 'loc' and len(lhs) == len(z.a[1]) == 1:
                rec = rn.ref.get(id(lhs[0]))
                if rec is not None:
                    cand[id(rec)] = z
        elif z.k == 'fn':
            skip.update(id(n) for n in z.a[0])
            bods.append(z.a[1])
        elif z.k == 'lfn':
            lhs = [z.a[0]]
            skip.add(id(z.a[0]))
            rec = rn.ref.get(id(z.a[0]))
            if rec is not None:
                cand[id(rec)] = z
        elif z.k == 'def' and z.a[0].k == 'id':
            lhs = [z.a[0]]
            skip.add(id(z.a[0]))
        elif z.k in ('for', 'iter'):
            lhs = z.a[0]
            skip.update(id(n) for n in lhs)
            bods.append(z.a[2])
        elif z.k == 'if':
            bods.extend(bs for c, bs in z.a[0])
            bods.append(z.a[1])
        elif z.k in ('wh', 'rep', 'do'):
            bods.append(z.a[0] if z.k in ('rep', 'do') else z.a[1])
        for n in lhs:
            rec = rn.ref.get(id(n)) if n.k == 'id' else None
            if rec is not None:
                key = id(rec)
                wrts[key] = wrts.get(key, 0) + 1
    read = {id(r): sum(id(n) not in skip for n in r['refs']) for r in rn.sy}

    def pure(q):
        todo = [q]
        while todo:
            q = ung(todo.pop())
            if q.k in ('num', 'str', 'nil', 'true', 'false', 'fn'):
                continue
            if q.k == 'id' and id(q) in rn.ref:
                continue
            if q.k == 'tab':
                for k, v in q.a[0]:
                    if k is not None and k.k != 'key':
                        if k.k not in ('num', 'str', 'true', 'false'):
                            return False
                        ok, val0 = val(k)
                        if not ok or val0 is None or isinstance(val0, float) and math.isnan(val0):
                            return False
                    todo.append(v)
                continue
            return False
        return True

    todo = dq(k for k in cand if read[k] == 0 and wrts.get(k) == 1)
    gone, done = set(), set()
    while todo:
        key = todo.popleft()
        z = cand[key]
        if key in done or id(z) in gone:
            continue
        done.add(key)
        rhs = ung(z.a[1] if z.k == 'lfn' else z.a[1][0])
        if not pure(rhs):
            if rhs.k in ('call', 'mcall'):
                z.k, z.a = 'stmt', [rhs]
            continue
        stk = [z]
        while stk:
            q = stk.pop()
            if isinstance(q, N):
                if id(q) in gone:
                    continue
                gone.add(id(q))
                if q.k == 'id' and id(q) not in skip and id(q) in rn.ref:
                    rec = id(rn.ref[id(q)])
                    read[rec] -= 1
                    if read[rec] == 0 and rec in cand and wrts.get(rec) == 1:
                        todo.append(rec)
                stk.extend(q.a)
            elif isinstance(q, (list, tuple)):
                stk.extend(q)
    for bs in reversed(bods):
        out = []
        for z in bs:
            if id(z) in gone or z.k == 'do' and not z.a[0]:
                continue
            if z.k == 'if':
                arms, tail = z.a
                if not tail and all(not rows and pure(cond) for cond, rows in arms):
                    continue
                if len(arms) == 1 and not arms[0][1] and tail:
                    z.a = [[(N('un', ['not', arms[0][0]]), tail)], []]
            out.append(z)
        bs[:] = out

    fuse(ast)
    flow(ast)


class Rn:
    def __init__(self, ast):
        self.sc = [{}]
        self.sy = []
        self.ref = {}
        self.glob = set()
        self.hint = []
        self.map = {}
        self.cnt = {'v': 0, 'f': 0, 'p': 0}
        self.bcnt = {}
        self.used = set()
        self.stp = 0
        self.run(ast)
        self.name()

    def bind(self, n, kind):
        rec = {'src': n.a[0], 'kind': kind, 'refs': [n], 'hint': set(), 'base': set(), 'defs': []}
        self.sy.append(rec)
        self.sc[-1][n.a[0]] = rec
        self.ref[id(n)] = rec

    def look(self, n):
        key = n.a[0]
        if key.startswith('\0'):
            self.glob.add('getfenv')
        for sc in reversed(self.sc):
            if key in sc:
                rec = sc[key]
                rec['refs'].append(n)
                self.ref[id(n)] = rec
                return
        self.glob.add(key)

    def run(self, ast):
        stk = [('bs', ast, False)]
        while stk:
            self.stp += 1
            if self.stp > 8000000:
                bad('rename cap exceeded')
            kind, x, arg = stk.pop()
            if kind == 'pop':
                self.sc.pop()
                continue
            if kind == 'bind':
                for n in x:
                    self.bind(n, arg)
                continue
            if kind == 'bs':
                if arg:
                    if len(self.sc) > 160:
                        bad('scope depth exceeded')
                    self.sc.append({})
                    stk.append(('pop', None, None))
                stk.extend(('st', z, None) for z in reversed(x))
                continue
            if kind == 'fn':
                self.sc.append({})
                stk.append(('pop', None, None))
                stk.append(('bs', x.a[1], False))
                stk.append(('bind', [p for p in x.a[0] if p.a[0] != '...'], 'p'))
                continue
            if kind == 'loop':
                self.sc.append({})
                stk.append(('pop', None, None))
                stk.append(('bs', x.a[2], False))
                stk.append(('bind', x.a[0], 'i'))
                continue
            if kind == 'ex':
                if not isinstance(x, N):
                    continue
                k, a = x.k, x.a
                if k == 'id':
                    self.look(x)
                elif k == 'fn':
                    stk.append(('fn', x, None))
                elif k in ('dot', 'met'):
                    stk.append(('ex', a[0], None))
                elif k == 'mcall':
                    if a[1].a[0] in ('Connect', 'Once'):
                        for q in a[2]:
                            if q.k == 'id':
                                self.hint.append(('ev', q, a[0]))
                    stk.extend(('ex', q, None) for q in reversed(a[2]))
                    stk.append(('ex', a[0], None))
                elif k == 'call':
                    stk.extend(('ex', q, None) for q in reversed(a[1]))
                    stk.append(('ex', a[0], None))
                elif k == 'interp':
                    stk.extend(('ex', q, None) for q in reversed(a[0]) if isinstance(q, N))
                elif k == 'tab':
                    seq = []
                    for key, v in a[0]:
                        if key is not None and key.k != 'key':
                            seq.append(key)
                        seq.append(v)
                    stk.extend(('ex', q, None) for q in reversed(seq))
                else:
                    stk.extend(('ex', q, None) for q in reversed(a) if isinstance(q, N))
                continue
            k, a = x.k, x.a
            if k == 'loc':
                kind = 'f' if len(a[1]) == 1 and ung(a[1][0]).k == 'fn' else 'v'
                stk.append(('bind', a[0], kind))
                stk.extend(('ex', q, None) for q in reversed(a[1]))
                for n, q in zip(a[0], a[1]):
                    self.hint.append(('rhs', n, q))
            elif k == 'lfn':
                self.bind(a[0], 'f')
                self.hint.append(('rhs', a[0], a[1]))
                stk.append(('fn', a[1], None))
            elif k == 'def':
                stk.append(('fn', a[1], None))
                stk.append(('ex', a[0], None))
            elif k == 'set':
                stk.extend(('ex', q, None) for q in reversed(a[1]))
                stk.extend(('ex', q, None) for q in reversed(a[0]))
                for n, q in zip(a[0], a[1]):
                    if n.k == 'dot' and ung(q).k == 'id':
                        self.hint.append(('prop', ung(q), n.a[1]))
                    elif n.k == 'id':
                        self.hint.append(('rhs', n, q))
            elif k == 'if':
                stk.append(('bs', a[1], True))
                for c, body in reversed(a[0]):
                    stk.append(('bs', body, True))
                    stk.append(('ex', c, None))
            elif k == 'wh':
                stk.append(('bs', a[1], True))
                stk.append(('ex', a[0], None))
            elif k == 'rep':
                self.sc.append({})
                stk.append(('pop', None, None))
                stk.append(('ex', a[1], None))
                stk.append(('bs', a[0], False))
            elif k in ('for', 'iter'):
                stk.append(('loop', x, None))
                stk.extend(('ex', q, None) for q in reversed(a[1]))
            elif k == 'do':
                stk.append(('bs', a[0], True))
            elif k == 'ret':
                stk.extend(('ex', q, None) for q in reversed(a[0]))
            elif k == 'stmt':
                stk.append(('ex', a[0], None))

    def garb(self, name):
        return len(name) == 1 or bool(re.fullmatch(r'_+l[_l]*|_+|_0x[0-9a-fA-F]+|l_[A-Za-z_0-9]+|var_[0-9_]+|[vfp][0-9]+', name))

    def word(self, text):
        if isinstance(text, bytes):
            try:
                text = text.decode('ascii')
            except UnicodeDecodeError:
                return None
        if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', text):
            return None
        text = text.lower()
        return text if text not in Prs([]).kw else None

    def root(self, q):
        seen = set()
        while True:
            q = ung(q)
            if q.k != 'id' or id(q) in seen:
                return q
            seen.add(id(q))
            rec = self.ref.get(id(q))
            if rec is None or len(rec['defs']) != 1:
                return q
            if len(seen) > 32:
                return q
            q = rec['defs'][0]

    def infr(self, q, dep=0):
        if dep > 32:
            return None
        q = ung(q)
        if q.k == 'id':
            rec = self.ref.get(id(q))
            if rec is not None and len(rec['defs']) == 1:
                return self.infr(rec['defs'][0], dep + 1)
            return None
        if q.k == 'dot':
            return self.word(q.a[1].a[0])
        if q.k == 'idx' and q.a[1].k == 'str':
            ok, v = val(q.a[1])
            return self.word(v) if ok else None
        if q.k == 'fn':
            body = q.a[1]
            if body and body[-1].k == 'ret' and len(body[-1].a[0]) == 1:
                todo = list(body[:-1])
                safe = True
                while todo:
                    z = todo.pop()
                    if isinstance(z, N):
                        if z.k == 'fn':
                            continue
                        if z.k == 'ret':
                            safe = False
                            break
                        todo.extend(z.a)
                    elif isinstance(z, (list, tuple)):
                        todo.extend(z)
                name = self.infr(body[-1].a[0][0], dep + 1) if safe else None
                if name:
                    return 'get' + name
            rows = body[:-1] if body and body[-1].k == 'ret' and not body[-1].a[0] else body
            if len(rows) == 1 and rows[0].k == 'stmt':
                rhs = ung(rows[0].a[0])
                if rhs.k == 'call':
                    fn = ung(rhs.a[0])
                    if fn.k == 'id' and id(fn) not in self.ref:
                        name = self.word(fn.a[0])
                        if name:
                            return 'call' + name
                    if fn.k == 'dot':
                        name = self.word(fn.a[1].a[0])
                        if name:
                            return 'call' + name
                elif rhs.k == 'mcall':
                    name = self.word(rhs.a[1].a[0])
                    if name:
                        return 'call' + name
            return None
        if q.k == 'call':
            fn = self.root(q.a[0])
            if fn.k == 'dot':
                meth = fn.a[1].a[0]
                if meth in ('GetService', 'WaitForChild', 'FindFirstChild', 'FindFirstChildOfClass', 'FindFirstChildWhichIsA') and len(q.a[1]) >= 2:
                    ok, v = val(self.root(q.a[1][1]))
                    if ok and isinstance(v, bytes):
                        return self.word(v)
                if meth == 'new':
                    obj = self.root(fn.a[0])
                    if obj.k == 'id' and obj.a[0] == 'Instance' and id(obj) not in self.ref and q.a[1]:
                        ok, v = val(self.root(q.a[1][0]))
                        return self.word(v) if ok and isinstance(v, bytes) else None
                    if obj.k == 'id' and id(obj) not in self.ref:
                        return self.word(obj.a[0])
        if q.k == 'mcall':
            meth = q.a[1].a[0]
            args = q.a[2]
            if meth in ('GetService', 'WaitForChild', 'FindFirstChild', 'FindFirstChildOfClass', 'FindFirstChildWhichIsA') and args:
                ok, v = val(self.root(args[0]))
                if ok and isinstance(v, bytes):
                    return self.word(v)
            if meth in ('Connect', 'Once'):
                name = self.infr(q.a[0], dep + 1)
                return (name or '') + 'connection'
        return None

    def name(self):
        for kind, n, q in self.hint:
            rec = self.ref.get(id(n))
            if rec is not None and kind == 'rhs':
                rec['defs'].append(q)
        for kind, n, q in self.hint:
            rec = self.ref.get(id(n))
            if rec is None:
                continue
            if kind == 'prop':
                name = self.word(q.a[0])
            elif kind == 'ev':
                name = self.infr(q)
                name = 'on' + name if name else None
            else:
                name = self.infr(q)
                if ung(q).k == 'fn':
                    rec['kind'] = 'f'
            if name:
                rec['base' if kind in ('prop', 'ev') else 'hint'].add(name)
        self.used = set(self.glob) | Prs([]).kw
        self.used.update(rec['src'] for rec in self.sy if not self.garb(rec['src']))
        lc = 0
        for rec in self.sy:
            src = rec['src']
            keep = not self.garb(src) and src not in self.glob
            if not self.garb(src):
                base = src
            elif len(rec['base']) == 1:
                base = next(iter(rec['base']))
            elif len(rec['hint']) == 1:
                base = next(iter(rec['hint']))
            else:
                kind = rec['kind']
                if kind == 'i':
                    lc += 1
                    if lc <= 3 and ('i', 'j', 'k')[lc - 1] not in self.used:
                        base = ('i', 'j', 'k')[lc - 1]
                    else:
                        kind = 'v'
                if kind != 'i':
                    self.cnt[kind] += 1
                    base = kind + str(self.cnt[kind])
                    while base in self.used:
                        self.cnt[kind] += 1
                        base = kind + str(self.cnt[kind])
            num = self.bcnt.get(base, 0) + 1
            self.bcnt[base] = num
            name = base if num == 1 else base + str(num)
            if not keep:
                while name in self.used:
                    num += 1
                    self.bcnt[base] = num
                    name = base + str(num)
            self.used.add(name)
            for n in rec['refs']:
                self.map[id(n)] = name


class Em:
    def __init__(self, src='', nms=None):
        self.src = src
        self.nms = {} if nms is None else nms
        self.dep = 0
        self.stp = 0

    def pfx(self, x, dep=0):
        out = self.ex(x, dep)
        if x.k not in ('id', 'grp', 'cast', 'dot', 'met', 'idx', 'call', 'mcall'):
            out = '(' + out + ')'
        return out

    def ex(self, x, dep=0):
        self.stp += 1
        if self.stp > 8000000:
            bad('emission step limit exceeded')
        self.dep += 1
        if self.dep > 160:
            bad('emission depth exceeded')
        try:
            k, a = x.k, x.a
            if k == 'id':
                if a[0].startswith('\0'):
                    return 'getfenv()[' + self.ex(atom(a[0][1:].encode('utf-8', 'surrogateescape')), dep) + ']'
                return self.nms.get(id(x), a[0])
            if k in ('str', 'num', 'key'):
                return a[0]
            if k == 'interp':
                return ''.join(self.ex(q, dep) if isinstance(q, N) else q for q in a[0])
            if k in ('nil', 'true', 'false', '...'):
                return k
            if k in ('grp', 'cast'):
                return '(' + self.ex(a[0], dep) + ')'
            if k == 'un':
                return a[0] + (' ' if a[0] == 'not' else '') + '(' + self.ex(a[1], dep) + ')'
            if k == 'bin':
                return '(' + self.ex(a[1], dep) + ' ' + a[0] + ' ' + self.ex(a[2], dep) + ')'
            if k in ('dot', 'met'):
                return self.pfx(a[0], dep) + ('.' if k == 'dot' else ':') + a[1].a[0]
            if k == 'idx':
                return self.pfx(a[0], dep) + '[' + self.ex(a[1], dep) + ']'
            if k == 'call':
                return self.pfx(a[0], dep) + '(' + ', '.join(self.ex(q, dep) for q in a[1]) + ')'
            if k == 'mcall':
                return self.pfx(a[0], dep) + ':' + a[1].a[0] + '(' + ', '.join(self.ex(q, dep) for q in a[2]) + ')'
            if k == 'tab':
                out = []
                for key, v in a[0]:
                    pre = '' if key is None else key.a[0] + ' = ' if key.k == 'key' else '[' + self.ex(key, dep) + '] = '
                    out.append(pre + self.ex(v, dep))
                return '{' + ', '.join(out) + '}'
            if k == 'fn':
                ps = ', '.join(self.ex(p, dep) for p in a[0])
                body = self.bs(a[1], dep + 1)
                return 'function(' + ps + ')\n' + body + '  ' * dep + 'end'
            if k == 'iex':
                return '(if ' + self.ex(a[0], dep) + ' then ' + self.ex(a[1], dep) + ' else ' + self.ex(a[2], dep) + ')'
            bad('expression emission record absent for ' + k)
        finally:
            self.dep -= 1

    def bs(self, bs, dep=0):
        if dep > 160:
            bad('statement emission depth exceeded')
        out = []
        pad = '  ' * dep
        for z in bs:
            self.stp += 1
            if self.stp > 8000000:
                bad('emission step limit exceeded')
            k, a = z.k, z.a
            if k in ('loc', 'set'):
                lhs = ', '.join(self.ex(n, dep) for n in a[0])
                op = ' = ' if k == 'loc' else ' ' + a[2] + ' '
                rhs = ', '.join(self.ex(q, dep) for q in a[1])
                s = ('local ' if k == 'loc' else '') + lhs + (op + rhs if a[1] else '')
            elif k in ('lfn', 'def'):
                fn = a[1]
                s = ('local ' if k == 'lfn' else '') + 'function ' + self.ex(a[0], dep) + '(' + ', '.join(self.ex(p, dep) for p in fn.a[0]) + ')\n'
                s += self.bs(fn.a[1], dep + 1) + pad + 'end'
            elif k == 'if':
                pts = []
                for i, (c, body) in enumerate(a[0]):
                    pts.append(('if ' if i == 0 else pad + 'elseif ') + self.ex(c, dep) + ' then\n' + self.bs(body, dep + 1))
                if a[1]:
                    pts.append(pad + 'else\n' + self.bs(a[1], dep + 1))
                pts.append(pad + 'end')
                s = ''.join(pts)
            elif k == 'wh':
                s = 'while ' + self.ex(a[0], dep) + ' do\n' + self.bs(a[1], dep + 1) + pad + 'end'
            elif k == 'rep':
                s = 'repeat\n' + self.bs(a[0], dep + 1) + pad + 'until ' + self.ex(a[1], dep)
            elif k == 'do':
                s = 'do\n' + self.bs(a[0], dep + 1) + pad + 'end'
            elif k in ('for', 'iter'):
                ns = ', '.join(self.ex(n, dep) for n in a[0])
                es = ', '.join(self.ex(q, dep) for q in a[1])
                s = 'for ' + ns + (' = ' if k == 'for' else ' in ') + es + ' do\n' + self.bs(a[2], dep + 1) + pad + 'end'
            elif k == 'ret':
                s = 'return' + (' ' + ', '.join(self.ex(q, dep) for q in a[0]) if a[0] else '')
            elif k in ('break', 'continue'):
                s = k
            elif k == 'stmt':
                s = self.ex(a[0], dep)
            elif k == 'type' and self.src:
                s = self.src[z.s:z.e]
            else:
                bad('statement emission record absent for ' + k)
            if s.startswith('('):
                s = ';' + s
            out.append(pad + s + '\n')
        return ''.join(out)


def fold(ast, src):
    mem = {}
    edt = []
    st = [ast]
    while st:
        x = st.pop()
        if isinstance(x, N):
            if x.k in ('bin', 'un', 'grp'):
                try:
                    v = cv(x, {}, mem)
                    if type(v) in (int, float):
                        s = num(v)
                        if src[x.s:x.e] != s:
                            edt.append((x.s, x.e, s))
                            x.k = 'num'
                            x.a = [s]
                            continue
                except (ValueError, TypeError, ZeroDivisionError, OverflowError, IndexError, KeyError):
                    pass
            st.extend(reversed(x.a))
        elif isinstance(x, (list, tuple)):
            st.extend(reversed(x))
    return edt


def put(src, edt):
    edt.sort()
    out = []
    pos = 0
    for s, e, v in edt:
        if s < pos:
            bad('overlapping source transformations')
        out.extend((src[pos:s], v))
        pos = e
    out.append(src[pos:])
    return ''.join(out)


def caps(ast):
    rn = Rn(ast)
    pars = {}
    todo = [(ast, None)]
    refs = []
    while todo:
        obj, par = todo.pop()
        if isinstance(obj, N):
            pars[id(obj)] = par
            if obj.k == 'id' and obj.a[0] in ('dofile', 'loadfile') and id(obj) not in rn.ref:
                if not (par is not None and par.k in ('dot', 'met', 'mcall') and par.a[1] is obj):
                    refs.append(obj)
            todo.extend((q, obj) for q in obj.a)
        elif isinstance(obj, (list, tuple)):
            todo.extend((q, par) for q in obj)
    seen = set()
    bind = set()
    while refs:
        obj = refs.pop()
        if id(obj) in seen:
            continue
        seen.add(id(obj))
        par = pars.get(id(obj))
        if par is None:
            return False
        if par.k in ('grp', 'cast') or par.k == 'bin' and par.a[0] in ('and', 'or'):
            refs.append(par)
        elif par.k == 'un' and par.a[0] == 'not':
            continue
        elif par.k == 'bin' and par.a[0] in ('==', '~='):
            continue
        elif par.k == 'if' and any(obj is cond for cond, body in par.a[0]):
            continue
        elif par.k in ('loc', 'set'):
            if any(obj is n for n in par.a[0]):
                if id(obj) not in rn.ref:
                    return False
                continue
            if len(par.a[0]) != len(par.a[1]):
                return False
            idx = next((i for i, q in enumerate(par.a[1]) if q is obj), None)
            if idx is None:
                return False
            rec = rn.ref.get(id(par.a[0][idx]))
            if rec is None:
                return False
            if id(rec) not in bind:
                bind.add(id(rec))
                refs.extend(rec['refs'])
        else:
            return False
    return True


def chk(src):
    tok = lex(src)
    for i, t in enumerate(tok):
        if t.v == 'goto':
            bad('output contains goto')
        if t.v == '::' and i + 2 < len(tok) and tok[i + 2].v == '::':
            bad('output contains goto')
        if i + 2 < len(tok) and tok[i + 1].v == '.':
            v = tok[i + 2].v
            if t.v == 'io' or t.v == 'os' and v in ('exit', 'execute', 'remove', 'rename', 'tmpname') or t.v == 'debug' and v == 'sethook':
                bad('output contains non-roblox construct')
    try:
        prs = Prs(tok)
        ast = prs.blk()
        if prs.cur().k != 'eof':
            bad('trailing tokens at line ' + str(prs.cur().ln))
    except Err as e:
        m = re.search(r'line ([0-9]+)', str(e))
        bad('output syntax error at line ' + (m[1] if m else '1'))
    if not caps(ast):
        bad('output contains non-roblox construct')
    if scan(ast)[1]:
        bad('output contains residual dispatcher loop')
    if dec(ast):
        bad('output contains residual encoded stream')
    return ast


def opn(p):
    cmd = sh.which('code')
    if cmd:
        args = [cmd, str(p)]
    elif sys.platform == 'darwin':
        cmd = sh.which('open')
        args = [cmd, '-a', 'Visual Studio Code', str(p)] if cmd else None
    elif os.name == 'nt':
        cmd = sh.which('code.cmd')
        args = [cmd, str(p)] if cmd else None
    else:
        cmd = sh.which('xdg-open')
        args = [cmd, str(p)] if cmd else None
    if args:
        try:
            sub.Popen(args, stdin=sub.DEVNULL, stdout=sub.DEVNULL, stderr=sub.DEVNULL, start_new_session=True)
            return
        except OSError:
            pass
    print('[] open skipped. no editor.')


def seed(ast):
    env = {}
    for z in ast:
        if z.k != 'set' or z.a[2] != '=':
            break
        vals = [val(q, env) for q in z.a[1]]
        for i, n in enumerate(z.a[0]):
            if n.k == 'id' and (i >= len(vals) or vals[i][0]):
                env[n.a[0]] = vals[i][1] if i < len(vals) else None
    return env


def rpls(src):
    prs = Prs(lex(src))
    ast = prs.blk()
    if prs.cur().k != 'eof' or not scan(ast)[1]:
        return
    strs = {}
    for q in walk(ast):
        if q.k != 'call' or len(q.a[1]) != 1 or q.a[1][0].k != 'str':
            continue
        fn = ung(q.a[0])
        if fn.k != 'fn' or not fn.a[1]:
            continue
        head = fn.a[1][0]
        if head.k != 'loc' or len(head.a[0]) != 2 or len(head.a[1]) != 2:
            continue
        if not any(z.k == 'wh' for z in fn.a[1]) or not any(z.k == 'mcall' and z.a[1].a[0] == 'sub' for z in walk(fn)):
            continue
        z = q.a[1][0]
        strs[(z.s, z.e, z.k)] = lit(z.a[0])
    if not strs:
        return
    raws = {}
    for q in walk(ast):
        if q.k != 'un' or q.a[0] != '#' or ung(q.a[1]).k != 'str':
            continue
        try:
            raw = lit(ung(q.a[1]).a[0])
            size = len(raw.decode('utf-8'))
        except (ValueError, UnicodeError):
            continue
        if size != len(raw):
            raws[(q.s, q.e, q.k)] = raw
    maps = []
    for cset in ('latin-1', 'cp1252'):
        inv = {}
        for i in range(256):
            try:
                char = bytes([i]).decode(cset)
            except UnicodeDecodeError:
                char = chr(i)
            inv[char] = i
        for i in range(256):
            inv.setdefault(chr(i), i)
        maps.append(inv)
    pool = None

    def invs(vals):
        nonlocal pool
        char = set()
        for raw in vals:
            try:
                char.update(raw.decode('utf-8'))
            except UnicodeError:
                return
        sigs = set()
        chs = sorted(char)
        for base in maps:
            opts = [base]
            miss = char - base.keys()
            if miss:
                if pool is None:
                    pool = []
                    for name in sorted(set(ca.aliases.values())):
                        if not re.fullmatch(r'cp[0-9]+|iso8859_[0-9]+|mac_[a-z0-9_]+', name):
                            continue
                        inv = {}
                        for i in range(256):
                            try:
                                text = bytes([i]).decode(name)
                            except (LookupError, UnicodeError):
                                continue
                            if len(text) == 1:
                                inv[text] = i
                        pool.append(inv)
                for inv in pool:
                    if not miss <= inv.keys():
                        continue
                    more = dict(base)
                    more.update((c, inv[c]) for c in miss)
                    opts.append(more)
            for inv in opts:
                sig = tuple(inv.get(c) for c in chs)
                if sig not in sigs:
                    sigs.add(sig)
                    yield inv

    todo = dq([{}])
    seen = {()}
    hold = 0
    work = 0
    lim = max(10000, len(src) * 128)

    def wfix(buf, inv):
        maps = {}
        for char, byte in inv.items():
            norm = ud.normalize('NFKC', char)
            if char.isspace() and len(norm) == 1 and norm.isascii() and norm.isspace():
                maps.setdefault(ord(norm), set()).add(byte)
        out = bytearray(buf)
        need = 0
        low, high = 128, 191
        for i, byte in enumerate(out):
            if need:
                if not low <= byte <= high:
                    vals = [v for v in maps.get(byte, ()) if low <= v <= high]
                    if len(vals) != 1:
                        return None
                    byte = vals[0]
                    out[i] = byte
                need -= 1
                low, high = 128, 191
            elif byte < 128:
                continue
            elif 194 <= byte <= 223:
                need = 1
            elif 224 <= byte <= 239:
                need = 2
                low = 160 if byte == 224 else 128
                high = 159 if byte == 237 else 191
            elif 240 <= byte <= 244:
                need = 3
                low = 144 if byte == 240 else 128
                high = 143 if byte == 244 else 191
            else:
                return None
        return bytes(out) if not need else None

    def undo(raw, inv):
        nonlocal work
        work += len(raw)
        if work > lim:
            bad('encoding recovery work budget exceeded')
        try:
            text = raw.decode('utf-8')
            buf = bytes(inv[c] for c in text)
        except (KeyError, UnicodeError):
            return None
        try:
            buf.decode('utf-8')
        except UnicodeError:
            buf = wfix(buf, inv)
            if buf is None:
                return None
        return buf if len(buf) < len(raw) else None

    def push(edts):
        nonlocal hold
        sig = tuple(sorted(edts.items()))
        if sig in seen:
            return
        hold += sum(len(v[1]) for v in edts.values())
        if hold > max(1000000, len(src) * 12):
            bad('encoding recovery memory budget exceeded')
        seen.add(sig)
        todo.append(edts)

    opts = {}
    pend = dq([raws]) if raws else dq()
    nsen = {tuple(sorted(raws.items()))}
    while pend:
        cur = pend.popleft()
        push({key: ('num', str(len(raw.decode('utf-8')))) for key, raw in cur.items()})
        for inv in invs(cur.values()):
            more = {}
            for key, raw in cur.items():
                buf = undo(raw, inv)
                more[key] = raw if buf is None else buf
                if buf is not None:
                    opts.setdefault(key, set()).update((len(buf), len(buf.decode('utf-8'))))
            sig = tuple(sorted(more.items()))
            if sig not in nsen:
                hold += sum(len(raw) for raw in more.values())
                if hold > max(1000000, len(src) * 12):
                    bad('encoding recovery memory budget exceeded')
                nsen.add(sig)
                pend.append(more)
    while todo:
        edts = todo.popleft()
        work += len(src)
        if work > lim:
            bad('encoding recovery work budget exceeded')
        if edts and all(key in edts and edts[key][0] == 'num' and int(edts[key][1]) in vals for key, vals in opts.items()):
            yield edts
        for key, orig in strs.items():
            raw = lit(edts[key][1]) if key in edts else orig
            vals = {buf for inv in invs([raw]) if (buf := undo(raw, inv)) is not None}
            for buf in sorted(vals):
                more = dict(edts)
                more[key] = ('str', atom(buf).a[0])
                push(more)


def wrap(src):
    prs = Prs(lex(src))
    ast = prs.blk()
    if prs.cur().k != 'eof' or not scan(ast)[1]:
        return
    ev = envs(ast)
    seen = set()
    work = 0
    for x, f, w, a in dec(ast):
        try:
            pair = rdr(ast, lit(a.a[0]))
        except Err:
            continue
        if pair is None:
            continue
        rd, name = pair
        bits = max(v[1] for v in rd.tab.values()) * 8
        if bits > sys.float_info.mant_dig:
            continue
        word = 1 << bits
        mods, deps = set(), set()
        for key, fn in rd.fun.items():
            if key not in rd.tab:
                continue
            for q in walk(fn):
                if q.k != 'bin' or q.a[0] != '%':
                    continue
                rhs = ung(q.a[2])
                ok, val0 = val(rhs, rd.env)
                if not ok or type(val0) not in (int, float):
                    continue
                if val0 > 0 and val0 == int(val0):
                    mods.add(val0)
                elif rhs.k == 'id':
                    deps.add(rhs.a[0])
        targ = {name: set(mods) for name in deps}
        try:
            sc = Sch(ast, Dc(rd, name))
        except Err:
            sc = None
        if sc is not None:
            refs = {}
            for q in walk(sc.fn):
                if q.k == 'idx' and ung(q.a[0]).k == 'id':
                    refs.setdefault(ung(q.a[0]).a[0], []).append(q)
            for z in walk(sc.fn):
                if z.k != 'loc':
                    continue
                for n, expr in zip(z.a[0], z.a[1]):
                    expr = ung(expr)
                    if expr.k != 'tab' or not expr.a[0] or any(k is not None for k, v in expr.a[0]):
                        continue
                    if not any(ung(v).k == 'nil' for k, v in expr.a[0]) or not any(ung(v).k == 'call' for k, v in expr.a[0]):
                        continue
                    for q in refs.get(n.a[0], ()):
                        key = ung(q.a[1])
                        ok, v = val(key, rd.env)
                        if key.k == 'id' and ok and type(v) in (int, float) and v != int(v):
                            targ.setdefault(key.a[0], set()).update(range(1, len(expr.a[0]) + 1))
        for ns, size, sets, ret in rd.tab.values():
            vals = [q for q in sets if any(n.a[0] == rd.pos for n in q.a[0])]
            if len(vals) != 1:
                continue
            q = vals[0]
            if len(q.a[0]) != 1 or len(q.a[1]) != 1:
                continue
            inc = ung(q.a[1][0])
            if inc.k != 'bin' or inc.a[0] != '+':
                continue
            left, rite = ung(inc.a[1]), ung(inc.a[2])
            if rite.k == 'id' and rite.a[0] == rd.pos:
                left, rite = rite, left
            if left.k == 'id' and left.a[0] == rd.pos and rite.k == 'id':
                targ.setdefault(rite.a[0], set()).add(size)
        for q in walk(f):
            if q.k != 'bin' or q.a[0] != '==':
                continue
            left, rite = ung(q.a[1]), ung(q.a[2])
            if left.k != 'bin' or left.a[0] != '%':
                left, rite = rite, left
            if left.k != 'bin' or left.a[0] != '%':
                continue
            for expr, want in ((ung(left.a[2]), 2), (rite, 0)):
                ok, val0 = val(expr, ev.get(id(x), {}))
                if ok and type(val0) in (int, float) and val0 != want and expr.k == 'id':
                    targ.setdefault(expr.a[0], set()).add(want)
        if not targ:
            continue
        stop = min(fn.s for fn in rd.fun.values())
        for z in rd.own.a[1]:
            if z.s >= stop:
                break
            if z.k != 'loc':
                continue
            for n, expr in zip(z.a[0], z.a[1]):
                if n.a[0] not in targ:
                    continue
                size = sum(1 for q in walk(expr))
                for q in walk(expr):
                    if q.k != 'num':
                        continue
                    ok, orig = val(q)
                    if not ok or type(orig) not in (int, float) or orig != int(orig) or abs(orig) >= word:
                        continue
                    old = q.a
                    for more in (orig - word, orig + word):
                        work += size
                        if work > max(10000, len(src) * 128):
                            bad('numeric recovery work budget exceeded')
                        try:
                            q.a = [num(more)]
                            ok, cand = val(expr, rd.env)
                        finally:
                            q.a = old
                        if not ok or type(cand) not in (int, float) or cand not in targ[n.a[0]]:
                            continue
                        key = (q.s, q.e, q.k)
                        sig = (key, num(more))
                        if sig not in seen:
                            seen.add(sig)
                            yield {key: ('num', sig[1])}


def tamp(src):
    prs = Prs(lex(src))
    ast = prs.blk()
    if prs.cur().k != 'eof' or not scan(ast)[1] or not dec(ast):
        return
    refs = {}
    decl = set()
    safe = set()
    opts = []
    for q in walk(ast):
        if q.k == 'id':
            refs.setdefault(q.a[0], []).append(q)
        if q.k in ('loc', 'set', 'for', 'iter'):
            decl.update(n.a[0] for n in q.a[0] if n.k == 'id')
        elif q.k == 'fn':
            decl.update(n.a[0] for n in q.a[0])
            for z in q.a[1]:
                if z.k not in ('loc', 'lfn'):
                    break
                if z.k == 'lfn':
                    continue
                for x in z.a[1]:
                    x = ung(x)
                    if x.k != 'bin' or x.a[0] != 'or' or val(x)[0]:
                        continue
                    left = ung(x.a[1])
                    if left.k != 'bin' or left.a[0] != 'and':
                        continue
                    a, b = val(left.a[2]), val(x.a[2])
                    if not a[0] or not b[0] or type(a[1]) not in (int, float) or type(b[1]) not in (int, float):
                        continue
                    pred = left.a[1]
                    if val(pred)[0]:
                        continue
                    key = (pred.s, pred.e, pred.k)
                    opts.append([{key: ('false', '')}, {key: ('true', '')}])
        elif q.k in ('lfn', 'def') and q.a[0].k == 'id':
            decl.add(q.a[0].a[0])
        if q.k == 'un' and q.a[0] == '#':
            tab = ung(q.a[1])
            if tab.k == 'tab' and all(k is None for k, v in tab.a[0]):
                safe.update(id(ung(v)) for k, v in tab.a[0] if ung(v).k == 'id')
    for name, vals in sorted(refs.items()):
        if name in decl or not all(id(q) in safe for q in vals):
            continue
        opts.append([{(q.s, q.e, q.k): (kind, '') for q in vals} for kind in ('nil', 'false')])
    if not opts:
        return
    todo = dq([(0, {})])
    work = 0
    hold = 0
    lim = max(1000000, len(src) * 128)
    seen = set()
    while todo:
        i, edts = todo.popleft()
        if i == len(opts):
            vals = {}
            end = -1
            for key, item in sorted(edts.items(), key=lambda q: (q[0][0], -q[0][1], q[0][2])):
                if key[0] >= end:
                    vals[key] = item
                    end = key[1]
            edts = vals
            sig = tuple(sorted(edts.items()))
            if sig not in seen:
                seen.add(sig)
                work += len(src)
                if work > lim:
                    bad('environment recovery work budget exceeded')
                yield edts
            continue
        for more in opts[i]:
            if any(key in edts and edts[key] != item for key, item in more.items()):
                continue
            vals = dict(edts)
            vals.update(more)
            hold += len(vals) * 64
            if hold > max(1000000, len(src) * 12):
                bad('environment recovery memory budget exceeded')
            todo.append((i + 1, vals))


def sfix(src):
    prs = Prs(lex(src))
    ast = prs.blk()
    if prs.cur().k != 'eof':
        return
    ev = envs(ast)
    work = 0
    for x, f, w, a in dec(ast):
        try:
            buf = enc(x, f, w, a, ev.get(id(x), {}))
            pair = rdr(ast, buf) if buf is not None else None
            if pair is None:
                continue
            rd, name = pair
            sc = Sch(ast, Dc(rd, name))
        except Err:
            continue
        recs, tabs = {}, []
        for z in walk(sc.fn):
            if z.k != 'loc':
                continue
            for n, q in zip(z.a[0], z.a[1]):
                q = ung(q)
                if q.k != 'tab' or not q.a[0]:
                    continue
                if all(k is None for k, v in q.a[0]):
                    hole = {i for i, (k, v) in enumerate(q.a[0], 1) if ung(v).k == 'nil'}
                    if hole and any(ung(v).k == 'call' for k, v in q.a[0]):
                        recs[n.a[0]] = hole
                elif all(k is not None and ung(v).k == 'fn' for k, v in q.a[0]):
                    tabs.append(q)
        init = {}
        stop = min(fn.s for fn in rd.fun.values())
        for z in rd.own.a[1]:
            if z.s >= stop:
                break
            if z.k == 'loc':
                init.update((n.a[0], q) for n, q in zip(z.a[0], z.a[1]))
        for tab in tabs:
            rows, edts, alts, glob = [], {}, {}, set()
            good = True
            for key, fn in tab.a[0]:
                fn = ung(fn)
                if not fn.a[1] or any(z.k != 'set' or len(z.a[0]) != 1 or len(z.a[1]) != 1 for z in fn.a[1]):
                    good = False
                    break
                part = []
                for z in fn.a[1]:
                    lhs, rhs = ung(z.a[0][0]), z.a[1][0]
                    if lhs.k != 'idx' or ung(lhs.a[0]).k != 'id' or ung(lhs.a[0]).a[0] not in recs:
                        good = False
                        break
                    obj = ung(lhs.a[0]).a[0]
                    ok, dest = val(lhs.a[1], rd.env)
                    if not ok or type(dest) not in (int, float):
                        good = False
                        break
                    part.append([obj, dest, ung(lhs.a[1]), rhs])
                if not good:
                    break
                used = {}
                for obj, dest, expr, rhs in part:
                    used.setdefault(obj, set()).add(dest)
                work += sum(len(recs[obj]) + len(vals) for obj, vals in used.items())
                if work > max(10000, len(src) * 128):
                    bad('schema recovery work budget exceeded')
                miss = {obj: recs[obj] - vals for obj, vals in used.items()}
                for row in part:
                    obj, dest, expr, rhs = row
                    if dest in recs[obj]:
                        continue
                    opts = miss[obj]
                    if len(opts) != 1 or expr.k != 'id' or expr.a[0] not in init:
                        good = False
                        break
                    want = next(iter(opts))
                    q = init[expr.a[0]]
                    key = (q.s, q.e, q.k)
                    item = ('num', num(want))
                    if key in edts and edts[key] != item:
                        good = False
                        break
                    edts[key] = item
                    glob.add(key)
                    alts[(expr.s, expr.e, expr.k)] = item
                    row[1] = want
                rows.extend(part)
            if not good or not edts:
                continue
            refs, bads = {}, []
            for obj, dest, expr, rhs in rows:
                for q in walk(rhs):
                    if q.k != 'call' or ung(q.a[0]).k != 'idx':
                        continue
                    cal = ung(q.a[0])
                    if ung(cal.a[0]).k != 'id' or ung(cal.a[0]).a[0] != name or q.a[1]:
                        continue
                    ok, key = val(cal.a[1], rd.env)
                    if not ok:
                        good = False
                        break
                    mark = (obj, dest)
                    if key in rd.tab:
                        refs.setdefault(mark, set()).add(key)
                    elif key not in rd.fun:
                        bads.append((mark, cal.a[1]))
            if not good or not bads:
                continue
            for mark, q in bads:
                opts = refs.get(mark, set())
                if len(opts) != 1:
                    good = False
                    break
                edts[(q.s, q.e, q.k)] = ('num', num(next(iter(opts))))
            if good:
                yield edts
                more = {key: v for key, v in edts.items() if key not in glob}
                more.update(alts)
                if more != edts:
                    yield more


def rcvr(src, edts):
    ast = peel(src, edts)
    for q in walk(ast):
        if q.k == 'call' and ung(q.a[0]).k in ('nil', 'true', 'false', 'num', 'str'):
            bad('recovery produces a noncallable literal')
    return rend(ast, src)


def recv(src):
    try:
        return rend(peel(src), src)
    except Err as err:
        orig = err
    out = None
    eeds, teds = [], []
    for edts in rpls(src):
        eeds.append(edts)
        try:
            cand = rcvr(src, edts)
        except Err:
            continue
        if out is not None and cand != out:
            bad('encoding recovery has multiple valid results')
        out = cand
    if out is not None:
        print('[] recovered source encoding.')
        return out
    for edts in tamp(src):
        teds.append(edts)
        try:
            cand = rcvr(src, edts)
        except Err:
            continue
        if out is not None and cand != out:
            bad('environment recovery has multiple valid results')
        out = cand
    if out is not None:
        print('[] recovered payload. environment checks removed.')
        return out
    work = 0
    seen = set()
    for left in eeds:
        for rite in teds:
            work += len(src)
            if work > max(1000000, len(src) * 128):
                bad('combined recovery work budget exceeded')
            if any(key in left and left[key] != item for key, item in rite.items()):
                continue
            vals = dict(left)
            vals.update(rite)
            edts = {}
            end = -1
            for key, item in sorted(vals.items(), key=lambda q: (q[0][0], -q[0][1], q[0][2])):
                if key[0] >= end:
                    edts[key] = item
                    end = key[1]
            sig = tuple(sorted(edts.items()))
            if sig in seen:
                continue
            seen.add(sig)
            try:
                cand = rcvr(src, edts)
            except Err:
                continue
            if out is not None and cand != out:
                bad('combined recovery has multiple valid results')
            out = cand
    if out is not None:
        print('[] recovered source encoding and payload. environment checks removed.')
        return out
    for edts in wrap(src):
        try:
            cand = rcvr(src, edts)
        except Err:
            continue
        if out is not None and cand != out:
            bad('numeric recovery has multiple valid results')
        out = cand
    if out is not None:
        print('[] recovered numeric encoding. integer wrap removed.')
        return out
    for edts in sfix(src):
        try:
            cand = rcvr(src, edts)
        except Err:
            continue
        if out is not None and cand != out:
            bad('schema recovery has multiple valid results')
        out = cand
    if out is None:
        raise orig
    print('[] recovered schema constraints.')
    return out


def rend(ast, src):
    tidy(ast)
    nms = Rn(ast)
    body = Em(src, nms.map).bs(ast)
    if body.strip() == src.strip():
        bad('result identical to input')
    if not body.strip():
        bad('result empty')
    mark = '--this file generated by astra ( moonsecv2 deobfuscator ) << https://discord.gg/D3ZFcWjAzJ >>'
    out = mark + '\n' + body.rstrip('\r\n') + '\n' + mark + '\n'
    chk(out)
    return out


def fin(out):
    data = out.encode('utf-8')
    tmp = None
    print('[] ok wr out.')
    try:
        fd, tmp = tf.mkstemp(prefix='.output-', suffix='.tmp', dir='.')
        with os.fdopen(fd, 'wb') as fp:
            fp.write(data)
            fp.flush()
            os.fsync(fp.fileno())
        os.replace(tmp, 'output.lua')
    except OSError:
        bad('output file write failed')
    finally:
        if tmp is not None:
            try:
                os.unlink(tmp)
            except OSError:
                pass
    opn(P('output.lua').absolute())


def run():
    if len(sys.argv) > 2:
        bad('multiple inputs not supported')
    p = P(sys.argv[1] if len(sys.argv) == 2 else 'sample.lua')
    if re.fullmatch(r'output[0-9]*\.lua', p.name, re.I):
        bad('input is output file')
    if not p.is_file():
        bad('sample.lua not found' if len(sys.argv) == 1 else 'input file not found')
    if p.stat().st_size > 32000000:
        bad('input size limit exceeded')
    try:
        buf = p.read_bytes()
    except OSError:
        bad('input unreadable')
    if len(buf) > 32000000:
        bad('input size limit exceeded')
    if not buf.strip():
        bad('input empty')
    try:
        src = buf.decode('utf-8-sig')
    except UnicodeDecodeError:
        bad('input source encoding is not utf8')
    fin(recv(src))


def peel(src, edts=None):
    tok = lex(src)
    prs = Prs(tok)
    ast = prs.blk()
    if prs.cur().k != 'eof':
        bad('parse error at line ' + str(prs.cur().ln))
    if edts:
        seen = set()
        for q in walk(ast):
            key = (q.s, q.e, q.k)
            if key in edts:
                q.k, q.a = edts[key][0], [edts[key][1]]
                seen.add(key)
        if len(seen) != len(edts):
            bad('encoding recovery edit location unresolved')
    fs, vms = scan(ast)
    ds = dec(ast)
    ev = envs(ast)
    pros = []
    for x, f, w, a in ds:
        buf = enc(x, f, w, a, ev.get(id(x), {}))
        if buf is None:
            bad('encoded alphabet parameters unresolved at line ' + str(x.ln))
        pair = rdr(ast, buf)
        if pair is None:
            bad('encoded stream reader table absent at line ' + str(x.ln))
        rd, name = pair
        dc = Dc(rd, name)
        sc = Sch(ast, dc)
        pro = sc.prs()
        if rd.env[rd.pos] - 1 != len(buf):
            bad('prototype stream has trailing bytes at offset ' + str(int(rd.env[rd.pos] - 1)))
        pros.append((pro, ev.get(id(x), {}), sc))
    out = None
    for vm in vms:
        for pro, env, sc in pros:
            hp = Hp(ast, vm, env)
            ops = set()
            stk = [pro]
            while stk:
                z = stk.pop()
                for ins in z['i'].values():
                    if hp.fld not in ins:
                        bad('opcode instruction field absent')
                    ops.add(ins[hp.fld])
                stk.extend(z['p'])
            for op in ops:
                body = hp.get(op)
                if any(z.k == 'wh' for z in walk(body)):
                    bad('handler dispatch predicate unresolved for opcode ' + num(op))
            fn = bld(ast, hp, sc, pro)
            cp = Cp(fn, seed(ast))
            opt(fn)
            cp.clea(fn)
            opt(fn)
            if any(z.k == 'fn' and cp.pla0.get(id(z)) is not None for z in walk(fn)):
                bad('string decoder input argument remains nonconstant')
            if out is not None:
                bad('independent vm invocation ordering reconstruction pending')
            out = fn.a[1]
    if out is not None:
        return out
    if ds:
        bad('encoded stream reconstruction incomplete at line ' + str(ds[0][0].ln))
    edt = fold(ast, src)
    if not edt:
        prev = Em(src).bs(ast)
        tidy(ast)
        rn = Rn(ast)
        if Em(src, rn.map).bs(ast) == prev:
            bad('nothing actionable in sample')
    return ast


if __name__ == '__main__':
    try:
        run()
    except Err as e:
        print('[] failed. ' + str(e).lower().rstrip('.') + '.')
        sys.exit(1)
    except RecursionError:
        print('[] failed. recursion depth exceeded.')
        sys.exit(1)
    except MemoryError:
        print('[] failed. memory limit exceeded.')
        sys.exit(1)
    except Exception as e:
        print('[] failed. internal ' + type(e).__name__.lower() + '.')
        sys.exit(1)