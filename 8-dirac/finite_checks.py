#!/usr/bin/env python3
"""Exact finite checks for the FRC Schrodinger-Dirac manuscript.

This script reproduces the p=13 computations stated in the manuscript:
1. image counts and loss factors for power maps on F_p^x,
2. the Cayley admissibility set and propagator orders for the Euclidean Schrodinger example,
3. the Clifford relations, transported gamma formulas, and explicit boost covariance for the Dirac example.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import gcd


P = 13
NU = 2


def mod_inv(a: int, p: int = P) -> int:
    return pow(a % p, -1, p)


def find_square_root(value: int, p: int = P) -> int:
    value %= p
    for x in range(p):
        if (x * x) % p == value:
            return x
    raise ValueError(f"no square root of {value} in F_{p}")


G = 2  # the frame's drive multiplier, F_13(t;0,1,2); nu = g is canonical
KAP = (P - 1) // 4
IT = pow(pow(G, P - 2, P), KAP, P)  # derived orientation i = g^{-kappa} = 5
assert IT == 5 and (IT * IT) % P == P - 1


@dataclass(frozen=True)
class Fp2:
    a: int
    b: int

    def __post_init__(self) -> None:
        object.__setattr__(self, "a", self.a % P)
        object.__setattr__(self, "b", self.b % P)

    def __add__(self, other: "Fp2") -> "Fp2":
        return Fp2(self.a + other.a, self.b + other.b)

    def __sub__(self, other: "Fp2") -> "Fp2":
        return Fp2(self.a - other.a, self.b - other.b)

    def __neg__(self) -> "Fp2":
        return Fp2(-self.a, -self.b)

    def __mul__(self, other: "Fp2") -> "Fp2":
        return Fp2(self.a * other.a + NU * self.b * other.b, self.a * other.b + self.b * other.a)

    def conj(self) -> "Fp2":
        return Fp2(self.a, -self.b)

    def norm(self) -> int:
        return (self.a * self.a - NU * self.b * self.b) % P

    def inv(self) -> "Fp2":
        n = self.norm()
        ninv = mod_inv(n, P)
        z = self.conj()
        return Fp2(z.a * ninv, z.b * ninv)

    def __truediv__(self, other: "Fp2") -> "Fp2":
        return self * other.inv()

    def __pow__(self, exponent: int) -> "Fp2":
        if exponent < 0:
            return (self.inv()) ** (-exponent)
        result = ONE
        base = self
        e = exponent
        while e:
            if e & 1:
                result = result * base
            base = base * base
            e >>= 1
        return result

    def is_zero(self) -> bool:
        return self.a == 0 and self.b == 0

    def __repr__(self) -> str:
        return f"Fp2({self.a},{self.b})"


ZERO = Fp2(0, 0)
ONE = Fp2(1, 0)
C = Fp2(0, 1)
I_T = Fp2(IT, 0)


def scalar(x: int) -> Fp2:
    return Fp2(x, 0)


def zero_matrix(n: int, m: int) -> list[list[Fp2]]:
    return [[ZERO for _ in range(m)] for _ in range(n)]


def identity(n: int) -> list[list[Fp2]]:
    out = zero_matrix(n, n)
    for i in range(n):
        out[i][i] = ONE
    return out


def mat_add(a: list[list[Fp2]], b: list[list[Fp2]]) -> list[list[Fp2]]:
    return [[a[i][j] + b[i][j] for j in range(len(a[0]))] for i in range(len(a))]


def mat_sub(a: list[list[Fp2]], b: list[list[Fp2]]) -> list[list[Fp2]]:
    return [[a[i][j] - b[i][j] for j in range(len(a[0]))] for i in range(len(a))]


def scalar_mul(s: Fp2, a: list[list[Fp2]]) -> list[list[Fp2]]:
    return [[s * a[i][j] for j in range(len(a[0]))] for i in range(len(a))]


def mat_mul(a: list[list[Fp2]], b: list[list[Fp2]]) -> list[list[Fp2]]:
    n = len(a)
    m = len(b[0])
    k = len(b)
    out = zero_matrix(n, m)
    for i in range(n):
        for j in range(m):
            total = ZERO
            for t in range(k):
                total = total + a[i][t] * b[t][j]
            out[i][j] = total
    return out


def mat_pow(a: list[list[Fp2]], exponent: int) -> list[list[Fp2]]:
    result = identity(len(a))
    base = a
    e = exponent
    while e:
        if e & 1:
            result = mat_mul(result, base)
        base = mat_mul(base, base)
        e >>= 1
    return result


def mat_eq(a: list[list[Fp2]], b: list[list[Fp2]]) -> bool:
    return all(a[i][j] == b[i][j] for i in range(len(a)) for j in range(len(a[0])))


def mat_inv(a: list[list[Fp2]]) -> list[list[Fp2]]:
    n = len(a)
    aug = [row[:] + eye_row[:] for row, eye_row in zip(a, identity(n))]
    for col in range(n):
        pivot = None
        for row in range(col, n):
            if not aug[row][col].is_zero():
                pivot = row
                break
        if pivot is None:
            raise ValueError("matrix is singular")
        aug[col], aug[pivot] = aug[pivot], aug[col]
        inv_pivot = aug[col][col].inv()
        aug[col] = [inv_pivot * entry for entry in aug[col]]
        for row in range(n):
            if row == col:
                continue
            factor = aug[row][col]
            if factor.is_zero():
                continue
            aug[row] = [aug[row][j] - factor * aug[col][j] for j in range(2 * n)]
    return [row[n:] for row in aug]


def block_matrix(a: list[list[Fp2]], b: list[list[Fp2]], c: list[list[Fp2]], d: list[list[Fp2]]) -> list[list[Fp2]]:
    top = [ra + rb for ra, rb in zip(a, b)]
    bottom = [rc + rd for rc, rd in zip(c, d)]
    return top + bottom


def vec_zero(n: int) -> list[Fp2]:
    return [ZERO for _ in range(n)]


def vec_add(a: list[Fp2], b: list[Fp2]) -> list[Fp2]:
    return [x + y for x, y in zip(a, b)]


def vec_sub(a: list[Fp2], b: list[Fp2]) -> list[Fp2]:
    return [x - y for x, y in zip(a, b)]


def vec_is_zero(v: list[Fp2]) -> bool:
    return all(x.is_zero() for x in v)


def mat_vec_mul(a: list[list[Fp2]], v: list[Fp2]) -> list[Fp2]:
    out = vec_zero(len(a))
    for i in range(len(a)):
        total = ZERO
        for j in range(len(v)):
            total = total + a[i][j] * v[j]
        out[i] = total
    return out


def point_add(x: tuple[int, int, int, int], y: tuple[int, int, int, int]) -> tuple[int, int, int, int]:
    return tuple((x[i] + y[i]) % P for i in range(4))


def point_sub(x: tuple[int, int, int, int], y: tuple[int, int, int, int]) -> tuple[int, int, int, int]:
    return tuple((x[i] - y[i]) % P for i in range(4))


def int_mat_point_mul(a: list[list[int]], x: tuple[int, int, int, int]) -> tuple[int, int, int, int]:
    out: list[int] = []
    for row in a:
        total = 0
        for coeff, value in zip(row, x):
            total += coeff * value
        out.append(total % P)
    return tuple(out)  # type: ignore[return-value]


def canonical_field(field: dict[tuple[int, int, int, int], list[Fp2]]) -> dict[tuple[int, int, int, int], list[Fp2]]:
    return {point: value for point, value in field.items() if not vec_is_zero(value)}


def field_add(a: dict[tuple[int, int, int, int], list[Fp2]], b: dict[tuple[int, int, int, int], list[Fp2]]) -> dict[tuple[int, int, int, int], list[Fp2]]:
    out = {point: value[:] for point, value in a.items()}
    for point, value in b.items():
        out[point] = vec_add(out.get(point, vec_zero(4)), value)
    return canonical_field(out)


def diff_apply(field: dict[tuple[int, int, int, int], list[Fp2]], shift: tuple[int, int, int, int]) -> dict[tuple[int, int, int, int], list[Fp2]]:
    support = set(field)
    candidates = support | {point_sub(point, shift) for point in support}
    out: dict[tuple[int, int, int, int], list[Fp2]] = {}
    for point in candidates:
        forward = field.get(point_add(point, shift), vec_zero(4))
        current = field.get(point, vec_zero(4))
        out[point] = vec_sub(forward, current)
    return canonical_field(out)


def dirac_apply(
    field: dict[tuple[int, int, int, int], list[Fp2]],
    gamma_family: list[list[list[Fp2]]],
    frame: list[tuple[int, int, int, int]],
) -> dict[tuple[int, int, int, int], list[Fp2]]:
    out: dict[tuple[int, int, int, int], list[Fp2]] = {}
    for gamma, shift in zip(gamma_family, frame):
        diff = diff_apply(field, shift)
        transformed = {point: mat_vec_mul(gamma, value) for point, value in diff.items()}
        out = field_add(out, transformed)
    return canonical_field(out)


def transport_apply(
    field: dict[tuple[int, int, int, int], list[Fp2]],
    lambda_matrix: list[list[int]],
    spin_matrix: list[list[Fp2]],
) -> dict[tuple[int, int, int, int], list[Fp2]]:
    out: dict[tuple[int, int, int, int], list[Fp2]] = {}
    for point, value in field.items():
        target = int_mat_point_mul(lambda_matrix, point)
        out[target] = mat_vec_mul(spin_matrix, value)
    return canonical_field(out)


def field_eq(
    a: dict[tuple[int, int, int, int], list[Fp2]],
    b: dict[tuple[int, int, int, int], list[Fp2]],
) -> bool:
    return canonical_field(a) == canonical_field(b)


def power_map_counts() -> None:
    print("Power map counts on F_p^x")
    for epsilon in [1, 2, 3, 4, 6, 12]:
        image = {pow(x, epsilon, P) for x in range(1, P)}
        loss = (P - 1) / len(image)
        print(
            f"  epsilon={epsilon:2d}: image_size={len(image):2d}, "
            f"formula={(P - 1) // gcd(epsilon, P - 1):2d}, loss_factor={int(loss):2d}"
        )


def schrodinger_check() -> None:
    n = P
    eye = identity(n)
    shift = zero_matrix(n, n)
    shift_inv = zero_matrix(n, n)
    for j in range(n):
        shift[(j - 1) % n][j] = ONE
        shift_inv[(j + 1) % n][j] = ONE
    delta = mat_sub(mat_add(shift, shift_inv), scalar_mul(scalar(2), eye))
    hamiltonian = scalar_mul(scalar(-1), delta)
    left = mat_sub(eye, scalar_mul(C, hamiltonian))
    right = mat_add(eye, scalar_mul(C, hamiltonian))
    cayley = mat_mul(mat_inv(left), right)
    u13 = mat_pow(cayley, 13)
    print("Schrodinger check")
    print(f"  det-denominator-invertible = {True}")
    print(f"  U^13 = I                 = {mat_eq(u13, eye)}")
    print("  admissible alpha=k*c and exact orders")

    def cayley_for(k: int) -> list[list[Fp2]]:
        alpha = Fp2(0, k)
        left_k = mat_sub(eye, scalar_mul(alpha, hamiltonian))
        right_k = mat_add(eye, scalar_mul(alpha, hamiltonian))
        return mat_mul(mat_inv(left_k), right_k)

    def matrix_order(matrix: list[list[Fp2]], bound: int = 5000) -> int:
        current = identity(len(matrix))
        for exponent in range(1, bound + 1):
            current = mat_mul(current, matrix)
            if mat_eq(current, eye):
                return exponent
        raise ValueError("order search failed")

    for k in range(P):
        try:
            u_k = cayley_for(k)
            print(f"    k={k:2d}: admissible=True, order={matrix_order(u_k)}")
        except ValueError:
            print(f"    k={k:2d}: admissible=False, order=NA")


def gamma_matrices() -> tuple[list[list[Fp2]], list[list[Fp2]], list[list[Fp2]], list[list[Fp2]]]:
    i2 = [[ONE, ZERO], [ZERO, ONE]]
    sigma1 = [[ZERO, ONE], [ONE, ZERO]]
    sigma2 = [[ZERO, -I_T], [I_T, ZERO]]
    sigma3 = [[ONE, ZERO], [ZERO, -ONE]]
    zero2 = [[ZERO, ZERO], [ZERO, ZERO]]
    beta = block_matrix(zero2, i2, i2, zero2)
    rho1 = block_matrix(zero2, sigma1, scalar_mul(Fp2(-1, 0), sigma1), zero2)
    rho2 = block_matrix(zero2, sigma2, scalar_mul(Fp2(-1, 0), sigma2), zero2)
    rho3 = block_matrix(zero2, sigma3, scalar_mul(Fp2(-1, 0), sigma3), zero2)
    gamma0 = scalar_mul(I_T * C, beta)
    gamma1 = scalar_mul(I_T, rho1)
    gamma2 = scalar_mul(I_T, rho2)
    gamma3 = scalar_mul(I_T, rho3)
    return gamma0, gamma1, gamma2, gamma3


def anticommutator(a: list[list[Fp2]], b: list[list[Fp2]]) -> list[list[Fp2]]:
    return mat_add(mat_mul(a, b), mat_mul(b, a))


def dirac_check() -> None:
    gamma0, gamma1, gamma2, gamma3 = gamma_matrices()
    eta = [-NU, 1, 1, 1]
    gammas = [gamma0, gamma1, gamma2, gamma3]
    ok = True
    for mu in range(4):
        for nu in range(4):
            lhs = anticommutator(gammas[mu], gammas[nu])
            rhs = zero_matrix(4, 4)
            coeff = scalar(2 * eta[mu] if mu == nu else 0)
            for i in range(4):
                rhs[i][i] = coeff
            ok = ok and mat_eq(lhs, rhs)

    x = scalar(1)
    y = scalar(1)
    delta = scalar(1 - NU)
    delta_inv = delta.inv()
    m = mat_mul(gamma0, gamma1)
    s = mat_add(identity(4), m)
    s_inv = scalar_mul(delta_inv, mat_sub(identity(4), m))

    a_coeff = scalar(1 + NU) / scalar(1 - NU)
    b_coeff = scalar(-2) / scalar(1 - NU)

    lhs0 = mat_mul(mat_mul(s_inv, gamma0), s)
    rhs0 = mat_add(scalar_mul(a_coeff, gamma0), scalar_mul(scalar(NU) * b_coeff, gamma1))

    lhs1 = mat_mul(mat_mul(s_inv, gamma1), s)
    rhs1 = mat_add(scalar_mul(b_coeff, gamma0), scalar_mul(a_coeff, gamma1))

    transported0 = mat_mul(mat_mul(s, gamma0), s_inv)
    transported1 = mat_mul(mat_mul(s, gamma1), s_inv)
    rhs0_transport = mat_add(scalar_mul(a_coeff, gamma0), scalar_mul(-scalar(NU) * b_coeff, gamma1))
    rhs1_transport = mat_add(scalar_mul(-b_coeff, gamma0), scalar_mul(a_coeff, gamma1))

    a_int = a_coeff.a
    b_int = b_coeff.a
    lambda_matrix = [
        [a_int, b_int, 0, 0],
        [(NU * b_int) % P, a_int, 0, 0],
        [0, 0, 1, 0],
        [0, 0, 0, 1],
    ]
    boosted_frame = [
        (a_int, (NU * b_int) % P, 0, 0),
        (b_int, a_int, 0, 0),
        (0, 0, 1, 0),
        (0, 0, 0, 1),
    ]
    sample_field = {
        (0, 0, 0, 0): [ONE, C, ZERO, scalar(2)],
        (1, 2, 0, 0): [scalar(3), ZERO, I_T, ONE],
        (5, 0, 1, 0): [ZERO, scalar(4), C, scalar(7)],
    }
    transported_gammas = [transported0, transported1, gamma2, gamma3]
    standard_frame = [
        (1, 0, 0, 0),
        (0, 1, 0, 0),
        (0, 0, 1, 0),
        (0, 0, 0, 1),
    ]
    lhs_covariance = dirac_apply(
        transport_apply(sample_field, lambda_matrix, s),
        transported_gammas,
        boosted_frame,
    )
    rhs_covariance = transport_apply(
        dirac_apply(sample_field, gammas, standard_frame),
        lambda_matrix,
        s,
    )

    print("Dirac check")
    print(f"  Clifford relations       = {ok}")
    print(f"  boost formula gamma^0    = {mat_eq(lhs0, rhs0)}")
    print(f"  boost formula gamma^1    = {mat_eq(lhs1, rhs1)}")
    print(f"  transported gamma^0      = {mat_eq(transported0, rhs0_transport)}")
    print(f"  transported gamma^1      = {mat_eq(transported1, rhs1_transport)}")
    print(f"  covariance sample check  = {field_eq(lhs_covariance, rhs_covariance)}")
    print(f"  A coefficient            = {a_coeff}")
    print(f"  B coefficient            = {b_coeff}")


def main() -> None:
    print(f"Using p={P}, nu={NU}, i={IT}, c^2={NU}")
    power_map_counts()
    schrodinger_check()
    dirac_check()


if __name__ == "__main__":
    main()
