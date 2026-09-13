"""The nonlinear completion (Theorem: no self-sourcing, exponential reading).

Validates the two exact arguments determining the nonlinear completion:

(A) Ward identity / exact Gauss law: in the full SINE-coupled (nonlinear) static
    model on Z^3, the synchronisation flux through every closed surface equals the
    enclosed source demand exactly -- for one source, for two sources, and at
    strong gradients -- and the deviation of the nonlinear potential from the
    linear one scales as the CUBE of the source (field-strength corrections,
    (r_*/r)^4 type), never as the square (no u^2 self-sourcing).

(B) The reading characterisation (symbolic): isotropic Schwarzschild is the
    exponential reading of the self-sourced potential psi = 2 artanh(U/2)
    (series identity verified), psi is not harmonic (Laplacian ~ (Gm)^3/r^5),
    while the exponential branch reads the harmonic u; and the exponential is
    the unique solution of the composition law R(a+b) = R(a)R(b), which the
    Schwarzschild reading violates.
"""
import numpy as np
import sympy as sp

ok = True

# ---------- (A) exact Gauss law in the nonlinear sine model ----------
N = 31                                     # lattice [0,N)^3, sources interior
def solve(sources, sine=True, iters=30000, tol=1e-13):
    """Relax kappa * sum_y sin(u_y - u_x) + m_x = 0 with u = 0 on the boundary."""
    u = np.zeros((N, N, N))
    m = np.zeros((N, N, N))
    for (pos, mass) in sources:
        m[pos] = mass
    for it in range(iters):
        nb = (np.roll(u, 1, 0), np.roll(u, -1, 0), np.roll(u, 1, 1),
              np.roll(u, -1, 1), np.roll(u, 1, 2), np.roll(u, -1, 2))
        if sine:
            drive = sum(np.sin(v - u) for v in nb) + m
        else:
            drive = sum(v - u for v in nb) + m
        drive[0, :, :] = drive[-1, :, :] = 0   # Dirichlet boundary
        drive[:, 0, :] = drive[:, -1, :] = 0
        drive[:, :, 0] = drive[:, :, -1] = 0
        u += 0.15*drive
        if it % 500 == 0 and np.max(np.abs(drive)) < tol:
            break
    return u, np.max(np.abs(drive))

def flux_box(u, c, R, sine=True):
    """Outward sine-flux through the surface of the cube of half-size R about c."""
    F = 0.0
    lo = [ci - R for ci in c]; hi = [ci + R for ci in c]
    couple = np.sin if sine else (lambda x: x)
    for ax in range(3):
        for face, outw in ((lo[ax], -1), (hi[ax], +1)):
            sl_in = [slice(lo[a], hi[a] + 1) for a in range(3)]
            sl_out = list(sl_in)
            sl_in[ax] = face
            sl_out[ax] = face + outw
            F += np.sum(couple(u[tuple(sl_in)] - u[tuple(sl_out)]))
    return F

c = (N//2, N//2, N//2)
m0 = 4.0                                    # strong: sin argument ~ 0.55 at first shell
u1, res = solve([(c, m0)])
print(f"  (A) single source m={m0}, solver residual {res:.1e}")
for R in (2, 4, 6, 9):
    F = flux_box(u1, c, R)
    print(f"      flux through box R={R}: {F:.10f}  (demand {m0})")
    if abs(F - m0) > 1e-6: ok = False

c2 = (N//2 + 5, N//2, N//2)
u2, _ = solve([(c, m0), (c2, 2.0)])
F2 = flux_box(u2, (N//2 + 2, N//2, N//2), 12)
print(f"      two sources, enclosing box: flux = {F2:.10f}  (demand {m0 + 2.0})")
if abs(F2 - (m0 + 2.0)) > 1e-6: ok = False

# no u^2 self-sourcing: ||u_sine - u_linear|| scales as m^3 (arcsin x = x + x^3/6 + ...)
devs = []
for mm in (1.0, 2.0):
    us, _ = solve([(c, mm)])
    ul, _ = solve([(c, mm)], sine=False)
    devs.append(np.max(np.abs(us - ul)))
p = np.log(devs[1]/devs[0])/np.log(2.0)
print(f"      nonlinear deviation scaling: ||u_sin - u_lin|| ~ m^{p:.2f}  (target 3: cubic, no m^2 term)")
if abs(p - 3) > 0.25: ok = False

# ---------- (B) symbolic characterisation of the two readings ----------
U = sp.symbols('U', positive=True)
psi = 2*sp.atanh(U/2)
schw = ((1 - U/2)/(1 + U/2))**2
ident = sp.simplify(sp.powsimp(sp.expand(sp.exp(-2*psi.rewrite(sp.log)))) - schw)
print(f"  (B) g00(Schwarzschild isotropic) == exp(-2 psi), psi = 2 artanh(U/2): residual {ident}")
if ident != 0: ok = False

r, Gm = sp.symbols('r Gm', positive=True)
psi_r = (Gm/r) + (Gm/r)**3/12               # psi to the order that decides
lap = sp.simplify(sp.diff(r**2*sp.diff(psi_r, r), r)/r**2)
print(f"      Laplacian(psi) = {lap}  (nonzero: psi is self-sourced; u = Gm/r is harmonic)")
if sp.simplify(lap) == 0: ok = False

a, b = sp.symbols('a b', positive=True)
expo_ok = sp.simplify(sp.exp(-(a + b)) - sp.exp(-a)*sp.exp(-b)) == 0
f = lambda x: (1 - x/2)/(1 + x/2)
schw_viol = sp.simplify(f(a + b) - f(a)*f(b))
print(f"      composition law: exponential satisfies R(a+b)=R(a)R(b): {expo_ok}; "
      f"Schwarzschild reading violates it (mismatch {sp.expand(schw_viol)} != 0)")
if not expo_ok or sp.simplify(schw_viol) == 0: ok = False

print("PASS" if ok else "FAIL", "- branch decision (Ward identity + composition law)")
