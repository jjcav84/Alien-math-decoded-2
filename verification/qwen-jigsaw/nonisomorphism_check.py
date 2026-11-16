# Finite-domain check: Z/144Z vs Z/12Z x Z/12Z as additive groups.
# Evidence class: computationally verified within declared finite domain.
# Not a kernel proof. Lean formalization is pending.
from math import gcd

N = 144
G1 = list(range(N))                                   # Z/144Z
G2 = [(a, b) for a in range(12) for b in range(12)]   # Z/12Z x Z/12Z

def order_mod144(x):
    k = 1
    while (x * k) % N != 0:
        k += 1
    return k

def order_prod(p):
    a, b = p
    ka = 1
    while (a * ka) % 12 != 0:
        ka += 1
    kb = 1
    while (b * kb) % 12 != 0:
        kb += 1
    return ka * kb // gcd(ka, kb)  # lcm

ord1 = {x: order_mod144(x) for x in G1}
ord2 = {p: order_prod(p) for p in G2}

print("|Z/144Z| =", len(G1), " |Z/12Z x Z/12Z| =", len(G2))
print("max element order in Z/144Z        =", max(ord1.values()))
print("max element order in Z/12Z x Z/12Z =", max(ord2.values()))
print("elements of order 144 in Z/144Z   =", sum(1 for v in ord1.values() if v == 144))
print("elements of order 144 in product  =", sum(1 for v in ord2.values() if v == 144))
print("exponent of product (max order)   =", max(ord2.values()))

# Every hom Z/144 -> G2 is f_x(k) = k*x with 144*x = 0 (all x qualify since exponent 12 | 144).
# Check: for each candidate x, is f_x injective?
hom_count = 0
injective_count = 0
for x in G2:
    if (144 * x[0]) % 12 == 0 and (144 * x[1]) % 12 == 0:
        hom_count += 1
        image = {((k * x[0]) % 12, (k * x[1]) % 12) for k in range(N)}
        if len(image) == N:
            injective_count += 1
print("homomorphisms Z/144 -> product    =", hom_count)
print("injective homomorphisms            =", injective_count)
print("isomorphism exists                 =", injective_count > 0)
