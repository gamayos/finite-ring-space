"""
a_shell.py — block A: the shell theorem and the exact shell arithmetic (EXACT, integer-pinned)
=============================================================================================
Master ledger row 00:D11 (the shell theorem, 20-rh Thm. hp). Paper-local predicates:

  A1  Thm. zeroslot     zero-slot: Σ_{x∈F_p^×} x^k = 0 for every nonterminal k, = −1 on the terminal slot
  A2  Thm. compl        slot complementarity: Φ(k) = −g^k bijects the nonterminal slots onto F_p^× \ {−1}
  A3  Lem. K            Hermitian phase calculus on F_{p²} = F_p(η), η² = ν a non-residue: |U_{p+1}| = p+1,
                        Frobenius = inversion on U_{p+1}, i = √−1 Frobenius-fixed and off the circle (N(i) = −1)
  A4  Prop. critical    the finite critical line: Tr z = 1 exactly on z = 2⁻¹ + bη; |L_{1/2}| = p;
                        N(z) = ¼ − νb²; 2⁻¹ = 2κ+1 = −π (capacity-first)
  A5  Thm. agree        the Klein four-group ⟨φ, ρ⟩ and its fixed loci F_p, L_{1/2}, {2⁻¹}; F_p ∩ L_{1/2} = {2⁻¹}
  A6  §1.3 (register)   the Subject constants: π = 2κ, 2π ≡ −1, i = g^{−κ}, i² ≡ −1, e = g^i on the odd
                        representative, g^π ≡ −1, e^{iπ} ≡ −1  (F_13: g = 2, κ = 3, i = 5, e = 6)
  A7  Thm. hp (i),(iii) the spectral content of v = Λ: constant mode carries the mean, nontrivial complex
                        characters carry v − v̄·1 (Rem. parseval); the scale-shift has the modes as eigenvectors
                        in both readings — S x^k = g^k x^k in F_p, S χ_j = ω^j χ_j on ℓ²(F_p^×) — and
                        Tr S^r = (p−1)·[(p−1) | r] (§10.2: the shell's trace carries no prime data)
  A8  Thm. hp (iv)      self-adjointness is free: any real multiset is the spectrum of a real-symmetric
                        tridiagonal matrix (Def. jacobi), checked on the first ten heights
  A9  Prop. ground      flat ground state: the Ramanujan sum c_p(n) = −1 for every n ≢ 0 (mod p)
  A10 Def. shells       the shared structure of two shells is the quarter-turn core Q₄ (4 | p−1, 4 | Ω−1);
                        on the laboratory pair (13, 233) the cycle projection C_{Ω−1} → C_{p−1} does not
                        exist (12 ∤ 232) — the negative check behind the round-02 chronon paragraph

Shells: p = 13, 17, 29, 37, 41 in full (all p² points of F_{p²}); 173 for A1, A4, A6.
"""
import math, cmath
import numpy as np
from rhcommon import check, jacobi_from_points, HEIGHTS

SHELLS = [13, 17, 29, 37, 41]
BIG = 173

def prime_factors(n):
    f, d = set(), 2
    while d * d <= n:
        while n % d == 0:
            f.add(d); n //= d
        d += 1
    if n > 1: f.add(n)
    return f

def generator(p):
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in prime_factors(p - 1)):
            return g

def nonresidue(p):
    sq = {(x * x) % p for x in range(1, p)}
    return next(v for v in range(2, p) if v not in sq)

# F_{p^2} = F_p(η), η² = ν: elements (a, b) = a + bη
def mul(z, w, nu, p):
    return ((z[0] * w[0] + nu * z[1] * w[1]) % p, (z[0] * w[1] + z[1] * w[0]) % p)
def frob(z, p):            # z ↦ z^p : a + bη ↦ a − bη
    return (z[0], (-z[1]) % p)
def trace(z, p): return (2 * z[0]) % p
def norm(z, nu, p): return (z[0] * z[0] - nu * z[1] * z[1]) % p
def zpow(z, k, nu, p):
    r, b = (1, 0), z
    while k:
        if k & 1: r = mul(r, b, nu, p)
        b = mul(b, b, nu, p); k >>= 1
    return r

def run():
    print("\n== block A: the shell theorem (00:D11) ==")
    for p in SHELLS + [BIG]:
        g, nu = generator(p), nonresidue(p)
        kappa = (p - 1) // 4; assert 4 * kappa + 1 == p
        # A1 zero-slot
        ok = all(sum(pow(x, k, p) for x in range(1, p)) % p == 0 for k in range(1, p - 1)) \
             and sum(pow(x, p - 1, p) for x in range(1, p)) % p == p - 1
        check("A1", f"zero-slot on F_{p}", ok, f"Σx^k=0 for k=1..{p-2}; = -1 at k={p-1}")
        # A6 the Subject constants, capacity-first
        pi_ = 2 * kappa
        i_ = pow(g, p - 1 - kappa, p)                       # g^{-κ}
        assert i_ == (-pow(g, kappa, p)) % p
        i_odd = i_ if i_ % 2 == 1 else i_ + p               # the odd integer representative of i
        e_ = pow(g, i_odd, p)
        ok = ((2 * pi_) % p == p - 1 and (i_ * i_) % p == p - 1 and pow(g, pi_, p) == p - 1
              and pow(e_, i_odd * pi_, p) == p - 1 and (2 * (2 * kappa + 1)) % p == 1
              and (2 * kappa + 1) % p == (-pi_) % p)
        check("A6", f"Subject constants on F_{p}: π=2κ, i=g^-κ, e=g^i (odd rep.)", ok,
              f"g={g} κ={kappa} π={pi_} i={i_} e={e_}: 2π≡-1, i²≡-1, g^π≡-1, e^(iπ)≡-1, 2⁻¹=2κ+1=-π")
        # A4 the finite critical line
        inv2 = (2 * kappa + 1) % p
        line = [(inv2, b) for b in range(p)]
        ok = all(trace(z, p) == 1 for z in line) and len(set(line)) == p \
             and all(norm(z, nu, p) == (pow(4, p - 2, p) - nu * z[1] * z[1]) % p for z in line)
        if p != BIG:   # the converse on the full plane: Tr z = 1 only on the line
            ok = ok and all(((2 * a) % p == 1) == (a == inv2) for a in range(p))
        check("A4", f"finite critical line on F_{p}: Tr z = 1 ⟺ z = 2⁻¹ + bη, |L| = p, N = ¼ − νb²", ok,
              f"ν={nu}, 2⁻¹={inv2}")
        if p == BIG:
            continue
        # A2 slot complementarity
        image = {(-pow(g, k, p)) % p for k in range(1, p - 1)}
        check("A2", f"Φ(k) = −g^k bijects the nonterminal slots onto F_{p}^× \\ {{−1}}", image == set(range(1, p - 1)),
              f"|image| = {len(image)} = p−2")
        # A3 Hermitian phase calculus
        K = [(a, b) for a in range(p) for b in range(p)]
        U = [z for z in K if norm(z, nu, p) == 1]
        inv_ok = all(frob(z, p) == zpow(z, p, nu, p) and mul(z, frob(z, p), nu, p) == (1, 0) for z in U)
        i2 = [(a, 0) for a in range(p) if (a * a) % p == p - 1]
        ok = len(U) == p + 1 and inv_ok and len(i2) == 2 and all(frob(z, p) == z and norm(z, nu, p) == p - 1 for z in i2)
        check("A3", f"F_{p}²: |U_(p+1)| = p+1, Frobenius = inversion on it, i Frobenius-fixed with N(i) = −1", ok)
        # A5 Klein four-group
        phi = lambda z: frob(z, p)
        rho = lambda z: ((1 - z[0]) % p, (-z[1]) % p)
        sig = lambda z: rho(phi(z))
        fix_phi = {z for z in K if phi(z) == z}; fix_rho = {z for z in K if rho(z) == z}; fix_sig = {z for z in K if sig(z) == z}
        ok = (all(phi(phi(z)) == z and rho(rho(z)) == z and phi(rho(z)) == rho(phi(z)) for z in K)
              and fix_phi == {(a, 0) for a in range(p)} and fix_sig == set(line) and fix_rho == {(inv2, 0)}
              and fix_phi & fix_sig == {(inv2, 0)})
        check("A5", f"Klein four-group on F_{p}²: Fix φ = F_p, Fix σ = L_1/2, Fix ρ = {{2⁻¹}}, F_p ∩ L_1/2 = {{2⁻¹}}", ok)
        # A9 flat ground state
        cp = [round(sum(math.cos(2 * math.pi * a * n / p) for a in range(1, p))) for n in range(1, p)]
        check("A9", f"c_{p}(n) = −1 for n ≠ 0", all(c == -1 for c in cp))
        # A7 spectral content and the two readings of the characters
        lam = {}
        for n in range(1, p):
            m, q = n, None
            for d in range(2, n + 1):
                if n % d == 0:
                    q = d; break
            if q is None: lam[n] = 0.0; continue
            while m % q == 0: m //= q
            lam[n] = math.log(q) if m == 1 else 0.0
        v = np.array([lam[n] for n in range(1, p)])
        dlog = {pow(g, m, p): m for m in range(p - 1)}
        w = cmath.exp(2j * math.pi / (p - 1))
        chi = np.array([[w ** (j * dlog[n]) for n in range(1, p)] for j in range(p - 1)])
        coef = chi.conj() @ v / (p - 1)
        mean = v.mean()
        recon_nontriv = (coef[1:] @ chi[1:]).real
        ok_mean = abs(coef[0].real - mean) < 1e-12 and np.allclose(recon_nontriv, v - mean, atol=1e-10) \
                  and np.allclose((coef @ chi).real, v, atol=1e-10)
        gram = chi.conj() @ chi.T / (p - 1)
        ok_orth = np.allclose(gram, np.eye(p - 1), atol=1e-10)
        # S f(x) = f(g x): power characters in F_p, complex characters on ℓ²
        ok_fp = all(pow((g * x) % p, k, p) == (pow(g, k, p) * pow(x, k, p)) % p for k in range(p - 1) for x in range(1, p))
        shifted = lambda j: np.array([w ** (j * dlog[(g * n) % p]) for n in range(1, p)])   # (S χ_j)(n) = χ_j(g n)
        ok_c = all(np.allclose(shifted(j), w ** j * chi[j]) for j in range(p - 1))
        tr = [sum(1 for x in range(1, p) if (pow(g, r, p) * x) % p == x) for r in range(1, p)]
        ok_tr = all(tr[r - 1] == ((p - 1) if r % (p - 1) == 0 else 0) for r in range(1, p))
        check("A7", f"F_{p}: mean v̄ = ψ(p−1)/(p−1) on the trivial mode, v − v̄·1 on the nontrivial characters; "
                    f"S x^k = g^k x^k in F_p and Sχ_j = ω^j χ_j on ℓ²; Tr S^r = (p−1)[(p−1)|r]",
              ok_mean and ok_orth and ok_fp and ok_c and ok_tr, f"v̄ = {mean:.6f} (= log 27720/12 at p = 13)" if p == 13 else "")
        # A10 the shared quarter-turn core; no cycle projection onto (13, 233)
        Om = 233
        q4 = {pow(i_, a, p) for a in range(4)}
        ok = q4 == {1, i_, p - 1, (-i_) % p} and (p - 1) % 4 == 0 and (Om - 1) % 4 == 0
        if p == 13:
            ok = ok and (Om - 1) % (p - 1) != 0
            check("A10", "Q₄ ⊂ both cycles; C_232 ↠ C_12 does not exist (12 ∤ 232) on the pair (13, 233)", ok, "the shells share the core, not a clock")
        else:
            check("A10", f"Q₄ = {{1, i, −1, −i}} ⊂ F_{p}^×, 4 | p−1", ok)
    # A8 self-adjointness is free
    J = jacobi_from_points(HEIGHTS[:10])
    ev = np.sort(np.linalg.eigvalsh(J))
    ok = np.allclose(J, J.T) and np.max(np.abs(np.triu(J, 2))) == 0 and np.max(np.abs(ev - HEIGHTS[:10])) < 1e-11
    check("A8", "any real multiset is the spectrum of a real-symmetric tridiagonal matrix (Lanczos on ten heights)", ok,
          f"max|eig(J) − height| = {np.max(np.abs(ev - HEIGHTS[:10])):.1e}")

if __name__ == "__main__":
    from rhcommon import summary
    run(); summary(write=False)
