#!/usr/bin/env python3
"""Compute Kauffman bracket of the trefoil (closure of sigma1^3)
using the 2-strand Temperley-Lieb algebra representation.

Basis: 1, e with e^2 = d e where d = -A^2 - A^{-2}.
Generator: R = A*1 + A^{-1} e. For trefoil (sigma1^3) compute tr(R^3)
with closure trace tr(1)=d, tr(e)=1.
"""
from collections import defaultdict

def add(p,q):
    r = defaultdict(int)
    for e,c in p.items():
        r[e] += c
    for e,c in q.items():
        r[e] += c
    # remove zeros
    return {e:c for e,c in r.items() if c!=0}

def mul(p,q):
    r = defaultdict(int)
    for e1,c1 in p.items():
        for e2,c2 in q.items():
            r[e1+e2] += c1*c2
    return {e:c for e,c in r.items() if c!=0}

def const(c):
    return {0:c}

def A_pow(k):
    return {k:1}

def poly_to_str(p):
    if not p:
        return '0'
    terms = []
    for e in sorted(p.keys(), reverse=True):
        coef = p[e]
        part = f'{coef:+}' if coef!=1 else '+'
        if e==0:
            part += '1'
        elif e==1:
            part += 'A'
        else:
            part += f'A^{e}'
        terms.append(part)
    s = ' '.join(terms)
    return s.lstrip('+')

def scalar_mul_poly(scalar, p):
    return {e: scalar*c for e,c in p.items()}

def poly_mul_scalar(p, scalar_poly):
    # multiply p (Laurent) by polynomial scalar_poly
    return mul(p, scalar_poly)

def main():
    # Symbols: basis elements 1 and e. Represent algebra elements as pair (p1,pE)
    # where p1,pE are Laurent polynomials in A (dict exp->coeff)

    def add_elem(x,y):
        return (add(x[0],y[0]), add(x[1],y[1]))

    def mul_elem(x,y):
        # (a + b e)(c + d e) = ac + (ad+bc)e + bd e^2 = ac + (ad+bc)e + bd d e
        a,c = x[0], y[0]
        b,d = x[1], y[1]
        ac = mul(a,c)
        ad = mul(a,d)
        bc = mul(b,c)
        bd = mul(b,d)
        # e^2 = d_scalar * e where d_scalar = -A^2 - A^{-2}
        d_scalar = add( scalar_mul_poly(-1, A_pow(2)), scalar_mul_poly(-1, A_pow(-2)) )
        bd_times_d = mul(bd, d_scalar)
        new1 = ac
        newE = add(add(ad, bc), bd_times_d)
        return (new1, newE)

    # define R = A*1 + A^{-1} e
    R = (A_pow(1), A_pow(-1))

    # compute R^3
    def pow_elem(x,n):
        res = (const(1), {})
        for _ in range(n):
            res = mul_elem(res, x)
        return res

    R3 = pow_elem(R,3)

    # closure trace: tr(1)=d_scalar, tr(e)=1
    d_scalar = add( scalar_mul_poly(-1, A_pow(2)), scalar_mul_poly(-1, A_pow(-2)) )

    val = add( mul(R3[0], d_scalar), R3[1] )

    # print polynomial
    print("Kauffman bracket <Trefoil> = ")
    # format output
    items = sorted(val.items(), reverse=True)
    s_parts = []
    for e,c in items:
        if c==0: continue
        coeff = '' if c==1 else str(c)+'*'
        if e==0:
            s_parts.append(f'{coeff}1')
        elif e==1:
            s_parts.append(f'{coeff}A')
        else:
            s_parts.append(f'{coeff}A^{e}')
    print(' + '.join(s_parts))

if __name__=='__main__':
    main()
