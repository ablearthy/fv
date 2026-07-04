# chakravala

This work verifies that `chakravala` is *correct* and that it *terminates*.
Correctness means that the function always returns a solution to Pell’s equation,
and that solution is non‑trivial whenever `n` is not a perfect square.

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
Extraction to OCaml also works (note that it uses `Z` from `zarith`, so it works with arbitrarily large numbers).

```
utop # #require "zarith.top";;
utop # #use ".generated/chakravala.ml";;
utop # chakravala (Z.of_int 5);;
- : (_, _) prod = Pair (9, 4)
utop # chakravala (Z.of_int 61);;
- : (_, _) prod = Pair (1766319049, 226153980)
utop # chakravala (Z.of_int 109);;
- : (_, _) prod = Pair (158070671986249, 15140424455100)
utop # chakravala (Z.of_int 277);;
- : (_, _) prod = Pair (159150073798980475849, 9562401173878027020)
utop # chakravala (Z.of_int 1000009);;
- : (_, _) prod = Pair (34706925223672496396789809927814813815307765776963912856922509178647365274946328856407826521920491865660582103497045793402988418037705962679307516988505857876964390789558730780088848581453893846075669374573656921026839180916242377075342011402917146015852682699643694594521692616917296211888386796207200484355565921942779593021239153250932809367343375306250588622693124202931000391929407993601886299493814178942425631794780981545112173083461897885890779629690403494883738597641652917389724861468861469060128752039214278919083448307372522896674145269801641612725196313356823206167066547560333716182268096405320538158647200126606167706547010458018009033824143516472297284824174466682086255090825908721205685918329895160170359359541818230928080001, 34706769043563204817615938466784230858119036719914610867129324392925738526512646213785832715329681367248946602644343421877859817327781343614538702667930152411016404960881017771621965574391031343731238815220037249448645150167643648488359111706099575340085599833464932489530592941852398352647763741219231356986717464767146604783118127002612419369396607552480492308143248522852027870248725714005484166452197968386596861102923438701377595311367632199661408531472355598498743358126746584102775815426888606250847779632676887118401736771105478532550725211917773966815311086920905216271710591615953790772633925947916231119806574068418059971313238146903541413316033808493986563768694877735717590066508656479298709462864726895041842361647825781606800)
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
