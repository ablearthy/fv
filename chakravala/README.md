# chakravala

This work verifies that `chakravala` is *correct* and that it *terminates*.
Correctness means that the function always returns a solution to Pell’s equation,
and that solution is non‑trivial whenever `n` is not a perfect square.
Extraction to OCaml also works (see [chakravala_autogen](./chakravala_autogen/)).

The algorithm is described in [this article](https://www.isibang.ac.in/~sury/chakravala.pdf) [^1];
verification was done using [mathcomp](https://github.com/math-comp/math-comp).

[^1]:
    In this implementation, at each step `m` is chosen such that `m² < N` and `N - m²` is minimal.
    The algorithm could be slightly modified to choose `m` such that `|m² - N|` is minimal,
    but this does not seem to make a significant difference.

```coq
Theorem chakravala_correct (n : nat) :
  let: (a, b) := chakravala n in
  (a ^ 2 - n * (b ^ 2) = 1)
  /\ ((isqrt n) ^ 2 != n -> b != 0).
```

The complete code is in the file [Main.v](./Main.v).
It is not polished yet, but it works!
Extraction to OCaml also works (note that it uses `Z` from `zarith`, so it works with arbitrarily large numbers):

```
$ cd chakravala_autogen
$ dune runtest
Testing `test/test_chakravala_autogen.ml'.
...

  [OK]          chakravala          0   chakravala(9).
  [OK]          chakravala          1   chakravala(61).
  [OK]          chakravala          2   chakravala(109).
  [OK]          chakravala          3   chakravala(277).
  [OK]          chakravala          4   chakravala(1000009).
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

If `n` is not a perfect square, the solution is non‑trivial (`b ≠ 0`).
Initially `b = 1`, and `b` never decreases; the final `b` is therefore non‑zero.

## Dependencies

```
depends: [
  "coq" {>= "9.1" & < "9.2"}
  "coq-mathcomp-ssreflect" {>= "2.5"}
  "coq-equations" {>= "1.3"}
]
``` 