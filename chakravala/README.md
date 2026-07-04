# chakravala

The algorithm described in [this article](https://www.isibang.ac.in/~sury/chakravala.pdf) [^1]
was verified using [mathcomp](https://github.com/math-comp/math-comp).

[^1]:
    In this implementation, at each step `m` is chosen such that `m² < N` and `N - m²` is minimal.
    The algorithm could be slightly modified to choose `m` such that `|m² - N|` is minimal,
    but this does not seem to make a significant difference.

The main theorem that was proved is that `chakravala` is *correct*:
the function returns a solution to Pell's equation, and if `n` is not a perfect square the solution is non‑trivial.
Along the way, *termination* of the algorithm was also proved.

```
Theorem chakravala_correct (n : nat) :
  let: (a, b) := chakravala n in
  (a ^ 2 - n * (b ^ 2) = 1)
  /\ ((isqrt n) ^ 2 != n -> b != 0).
```

The complete code is in the file `Main.v`.
It is not polished yet, but it works!
Extraction to OCaml also works (note that it uses `int`, so it will fail for large `n`; you could use `Z` from `zarith` instead).

```
utop # #use ".generated/chakravala.ml";;
utop # chakravala 5;;
- : (int, int) prod = Pair (9, 4)
utop # chakravala 61;;
- : (int, int) prod = Pair (1766319049, 226153980)
utop # chakravala 5;;
- : (int, int) prod = Pair (158070671986249, 15140424455100)
```

There was also an unsuccessful attempt to prove the algorithm in Dafny.

## Details

The algorithm looks like this:

```python
def chakravala(n):
    nsqrt = math.isqrt(n)
    assert nsqrt**2 != n

    def step(m, k, sign, a, b):
        m = nsqrt - (nsqrt + m) % k
        return m, (n - m * m) // k, not sign, (a * m + n * b) // k, (a + b * m) // k

    m, k, sign, a, b = step(1, 1, False, 1, 0)
    while k != 1 or sign:
        m, k, sign, a, b = step(m, k, sign, a, b)
    return a, b
```

All numbers in the algorithm are natural numbers. The `sign` indicates the sign of `k`:
the signed value `k_signed` is `-k` when `sign = true`, and `k` when `sign = false`.

### Termination

The values of `a` and `b` do not affect termination,
so temporarily ignore them and consider only the `state (m, k, sign)`.

Take the initial state to be `initial = (nsqrt, 1, false)`.
Also assume that `(m, k, sign) = iter n step initial` for some `n`.

- `(m, k, sign)` is finite, because of `0 < m ≤ nsqrt` and `0 < k ≤ 2 nsqrt`.
- `step` is injective.

This implies that there exists `o = order initial > 0`, s.t. `iter o step initial = initial`.
`o` is the length of the cycle.
This means in `[initial, step initial, step (step initial), ... iter o step initial]`
the first and last values are the same.

Now, for any state `s` that occurs before returning to initial,
let `i` be the number of steps needed to reach `s` from `initial` (so `iter (i+1) step_state initial = s`).
Define the distance of `s` to the cycle’s end as `distance s = o - i`.
We have `distance (step s) = distance s - 1` whenever `s ≠ initial`.
Thus the distance strictly decreases with each step,
and it eventually reaches 0, which corresponds to the state `initial`.
So, termination is guaranteed.

### Correctness

The correctness proof maintains two invariants:
- `a² - n·b² = k_signed`
- `k` divides both `a * m + n * b` and `a + b * m`

If `n` is not perfect square, then we get non-trivial solution (i.e. `b != 0`).
That's because initially `b = 1` and only grows.

If `n` is not a perfect square, the solution is non‑trivial (`b ≠ 0`).
Initially `b = 1`, and b` never decreases; the final b is therefore non‑zero.
