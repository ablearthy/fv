import math

from sympy.solvers.diophantine.diophantine import diop_DN

# def chakravala(n):
#     nsqrt = math.isqrt(n)
#     assert nsqrt**2 != n

#     def step(m, k, sign, a, b):
#         m = nsqrt - (nsqrt + m) % k
#         return m, (n - m * m) // k, not sign, (a * m + n * b) // k, (a + b * m) // k

#     m, k, sign, a, b = step(1, 1, False, 1, 0)
#     while k != 1 or sign:
#         m, k, sign, a, b = step(m, k, sign, a, b)
#     return a, b

def spawn(n, nsqrt):
    def f(m, k, sign, a, b):
        m = nsqrt - (nsqrt + m) % k
        assert 0 < m <= nsqrt < m + k
        assert 0 < k <= nsqrt + m
        assert b <= (a + b * m) // k
        return m, (n - m * m) // k, not sign, (a * m + n * b) // k, (a + b * m) // k
    
    def p(m, k, sign):
        m = nsqrt - (nsqrt + m) % k
        return m, (n - m * m) // k, not sign

    def step_inverse(m, k, sign):
        k = (n - m*m) // k
        return nsqrt - (nsqrt + m) % k, k, not sign
    
    def invariant(m, k, sign, a, b):
        assert not sign or (n*b*b - a*a== k)
        assert sign or (a*a - n*b*b == k)
        assert 0 < m <= nsqrt < m + k
        assert (m**2 - n) % k == 0
        assert 0 < k <= nsqrt + m
        assert 0 < m <= nsqrt

    return f, p, step_inverse, invariant

def chakravala(n):
    nsqrt = math.isqrt(n)
    if nsqrt**2 == n:
        return 1, 0

    step, step1, step_inverse, invariant = spawn(n, nsqrt)
    m, k, sign, a, b = step(nsqrt, 1, False, 1, 0)

    while k != 1 or sign:
        invariant(m, k, sign, a, b)
        assert step_inverse(*step1(m, k, sign)) == (m, k, sign), f"expected: { (m,k, sign) = }, got: { step_inverse(*step1(m, k, sign)) = }"

        m, k, sign, a, b = step(m, k, sign, a, b)
    
    invariant(m, k, sign, a, b)
        
    assert 0 < m <= nsqrt < m + k
    
    return a, b

def main():
    for n in range(1, 1_000_000):
        if n % 1_000 == 0:
            print(n)
        a, b = chakravala(n)
        assert a*a - n*b*b == 1, f"chakravala({n}) produced wrong result"
        assert math.isqrt(n)**2 == n or (b > 0), f"chakravala returned trivial solution"

        a1, b1 = diop_DN(n, 1)[0]
        assert a == a1
        assert b == b1
  


if __name__ == '__main__':
    main()