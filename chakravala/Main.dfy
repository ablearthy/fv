import Std.Arithmetic.DivMod

function {:transparent} sqr(n: nat): nat {
    n * n
}

function {:opaque} isqrt(n: nat): nat
    decreases n
    ensures sqr(isqrt(n)) <= n < sqr(isqrt(n) + 1)
{
    if n == 0 then 0
    else
        var i := isqrt(n - 1);
        if sqr(i + 1) <= n then
            assert n <= sqr(i + 1);
            i + 1
        else
            i
}

lemma SqrLte(a: nat, b: nat)
    decreases a, b
    requires a <= b
    ensures a*a <= b * b
{
    if a < b {
        SqrLte(a, b - 1);
    }
}

lemma MulDistR(a: nat, b: nat, c: nat)
    requires b <= c
    ensures a * b <= a * c
{}

lemma DivR(a: nat, b: nat, c: nat)
    requires a * b > c
    ensures a > c / b
{}

function {:transparent} calc_s(n: nat, m: nat, k: nat): nat
    requires 0 < k
{
    (isqrt(n) + m) % k
}

function {:transparent} calc_m'(n: nat, m: nat, k: nat): nat
    requires 0 < k <= isqrt(n) + m
    requires m <= isqrt(n)
{
    isqrt(n) - calc_s(n, m, k)
}

function {:transparent} calc_k'(n: nat, m': nat, k: nat): nat
    requires 0 < k
    requires m' <= isqrt(n)
{
    SqrLte(m', isqrt(n));
    (n - sqr(m')) / k
}

function {:transparent} calc_a'(n: nat, m': nat, k: nat, a: nat, b: nat): nat
    requires 0 < k
{
    (a * m' + n * b) / k
}

function {:transparent} calc_b'(n: nat, m': nat, k: nat, a: nat, b: nat): nat
    requires 0 < k
{
    (a + b * m') / k
}

lemma {:induction false} m'_bounds(n: nat, m: nat, k: nat)
    requires 0 < k <= isqrt(n) + m
    requires m <= isqrt(n)
    ensures var m' := calc_m'(n, m, k); 0 < m' <= isqrt(n) < m' + k
{}

lemma m'_div_helper1(n: nat, m: nat, k: nat)
    requires 0 < k <= isqrt(n) + m
    requires m <= isqrt(n)
    ensures var m' := calc_m'(n, m, k); (m + m') % k == 0
{
    Std.Arithmetic.DivMod.LemmaSubModNoopRight(isqrt(n) + m, isqrt(n) + m, k);
}

// lemma m'_div_helper(n: nat, m: nat, k: nat)
//     requires 0 < k <= isqrt(n) + m
//     requires m <= isqrt(n)
//     ensures var m' := calc_m'(n, m, k); sqr(m) % k == sqr(m') % k
// {
//     var m' := calc_m'(n, m, k);
//     Std.Arithmetic.DivMod.LemmaMulModNoopGeneral(m, m, k);
//     Std.Arithmetic.DivMod.LemmaSubModNoopRight(isqrt(n) + m, isqrt(n) + m, k);
//     Std.Arithmetic.DivMod.LemmaModEquivalence(m, -(m' as int), k); 
//     Std.Arithmetic.DivMod.LemmaMulModNoopGeneral(-(m' as int), -(m' as int), k);
//     assert sqr((-m') % k) % k == sqr(m') % k;
//     assert sqr(m) % k == sqr(m') % k;
// }

// TODO: replace
lemma {:axiom} m'_div_helper(n: nat, m: nat, k: nat)
    requires 0 < k <= isqrt(n) + m
    requires m <= isqrt(n)
    ensures var m' := calc_m'(n, m, k); sqr(m) % k == sqr(m') % k

lemma m'_div(n: nat, m: nat, k: nat)
    requires 0 < k <= isqrt(n) + m
    requires m <= isqrt(n)
    ensures var m' := calc_m'(n, m, k); (n - sqr(m)) % k == (n - sqr(m')) % k
{
    var m' := calc_m'(n, m, k);

    calc {
        (n - sqr(m)) % k;
        { Std.Arithmetic.DivMod.LemmaSubModNoop(n, sqr(m), k); }
        ((n % k) - sqr(m) % k) % k;
        { m'_div_helper(n, m, k); }
        ((n % k) - sqr(m') % k) % k;
        { Std.Arithmetic.DivMod.LemmaSubModNoop(n, sqr(m'), k); }
        (n - sqr(m')) % k;
    }
}

lemma {:induction false} k'_min_bounds(n: nat, m': nat, k: nat)
    requires sqr(isqrt(n)) != n
    requires 0 < k
    requires 0 < m' <= isqrt(n) < m' + k
    requires (n - sqr(m')) % k == 0
    ensures var k' := calc_k'(n, m', k); 0 < k'
{
    SqrLte(m', isqrt(n));
}


lemma {:induction false} k'_max_bounds(n: nat, m': nat, k: nat)
    requires isqrt(n) - m' < k
    requires 0 < k
    requires 0 < m' <= isqrt(n)
    ensures var k' := calc_k'(n, m', k); k'<= isqrt(n) + m'
{
    MulDistR(isqrt(n) + m' + 1, 1, k - (isqrt(n) - m'));
    assert k * (isqrt(n) + m' + 1) > n - sqr(m');
    SqrLte(m', isqrt(n));
    DivR(isqrt(n) + m' + 1, k, n - sqr(m'));
}

lemma obv_eq(n: nat, m': nat, k: nat, a: nat, b: nat)
    ensures sqr(a) * (n - sqr(m')) - n * sqr(b) * (n - sqr(m')) == n * sqr(a + b * m') - sqr(a * m' + n * b)
{}

lemma LemmaDivAdditionDivisible(a: int, b: int, c: nat)
    requires c > 0
    requires a % c == 0 && b % c == 0
    ensures (a + b) / c == (a / c) + (b / c)
{
    Std.Arithmetic.DivMod.LemmaDivMultiplesVanish((a / c) + (b / c), c);  
}

lemma LemmaDivSubtractDivisible(a: int, b: int, c: nat)
    requires c > 0
    requires a % c == 0 && b % c == 0
    ensures (a - b) / c == (a / c) - (b / c)
{
    Std.Arithmetic.DivMod.LemmaDivMultiplesVanish((a / c) - (b / c), c);  
}

lemma LemmaSquareOfQuotient(a: nat, b: nat)
    requires b > 0 && a % b == 0
    ensures sqr(a / b) == sqr(a) / sqr(b)
{
    assert a == b * (a / b);
    Std.Arithmetic.DivMod.LemmaDivMultiplesVanish(sqr(a / b), sqr(b));
}
lemma LemmaSquareDivisibleBy(a: nat, b: nat)
    requires b > 0 && a % b == 0
    ensures sqr(a) % b == 0
{
    Std.Arithmetic.DivMod.LemmaMulModNoop(a, a, b);
}

lemma LemmaMulDivCancelFactor(a: int, b: int, c: nat)
    requires c > 0 && b % c == 0
    ensures (a * b) / c == a * (b / c)
{
    assert b == c * (b / c);
    Std.Arithmetic.DivMod.LemmaDivMultiplesVanish(a * (b / c), c);
    assert (a * b) / c == a * (b / c);
}

lemma LemmaSquareDivisibleBySquare(a: nat, b: nat)
    requires b > 0
    requires a % b == 0
    ensures sqr(a) % sqr(b) == 0
{
    Std.Arithmetic.DivMod.LemmaModBreakdown(sqr(a), b, b);
    LemmaSquareDivisibleBy(a, b);
    LemmaMulDivCancelFactor(a, a, b);
    Std.Arithmetic.DivMod.LemmaMulModNoopGeneral(a, a / b, b);
}

lemma a_is_divisble1_helper1(n: nat, m': nat, a: nat, b: nat)
    ensures var neg_m' := -(m' as int); neg_m' * (a * m' + n * b) + n * (a + b * m') == a * (neg_m' * m' + n)
{}

lemma a_is_divisble1_helper2(n: nat, m': nat, k: nat, a: nat, b: nat)
    requires sqr(isqrt(n)) != n
    requires m' <= isqrt(n)
    requires 0 < k
    requires (n - sqr(m')) % k == 0
    requires (a * m' + n * b) % k == 0 && (a + b * m') % k == 0
    ensures
        var neg_m' := -(m' as int);
        var k' := calc_k'(n, m', k);
        var a' := calc_a'(n, m', k, a, b);
        var b' := calc_b'(n, m', k, a, b);
        a' * neg_m' + n * b' == a * k'
{
    var neg_m' := -(m' as int);
    var k' := calc_k'(n, m', k);
    var a' := calc_a'(n, m', k, a, b);
    var b' := calc_b'(n, m', k, a, b);

    calc {
        a' * neg_m' + n * b';
        ((a * m' + n * b) / k) * neg_m' + n * ((a + b * m') / k);
    == { assert (a * m' + n * b) % k == 0; LemmaMulDivCancelFactor(neg_m', a * m' + n * b, k); assert (a + b * m') % k == 0; LemmaMulDivCancelFactor(n, a + b * m', k); }
        (neg_m' * (a * m' + n * b)) / k + (n * (a + b * m')) / k;
    == {
        Std.Arithmetic.DivMod.LemmaMulModNoopRight(neg_m', a * m' + n * b, k);
        assert (neg_m' * (a * m' + n * b)) % k == 0;
        Std.Arithmetic.DivMod.LemmaMulModNoopRight(n, a + b * m', k);
        assert (n * (a + b * m')) % k == 0;
        LemmaDivAdditionDivisible(neg_m' * (a * m' + n * b), n * (a + b * m'), k); }
        (neg_m' * (a * m' + n * b) + n * (a + b * m')) / k;
    == { a_is_divisble1_helper1(n, m', a, b); }
        (a * (neg_m' * m' + n)) / k;
    == { assert neg_m' * m' + n == n - sqr(m'); }
        (a * (n - sqr(m'))) / k;
    == { assert (n - sqr(m')) % k == 0; LemmaMulDivCancelFactor(a, n - sqr(m'), k); }
        a * ((n - sqr(m')) / k);
    == { assert k' == (n - sqr(m')) / k; }
        a * k';
    }
}

ghost predicate AIsDivisibleByK(n: nat, m: nat, k: nat, a: nat, b: nat)
    requires sqr(isqrt(n)) != n
    requires 0 < k <= isqrt(n) + m
    requires m <= isqrt(n)
    requires (n - sqr(m)) % k == 0
{
    var m' := calc_m'(n, m, k);
    var k', a', b' := calc_k'(n, m', k), calc_a'(n, m', k, a, b), calc_b'(n, m', k, a, b);
    var neg_m' := -(m' as int);

    assert (n - sqr(m')) % k == 0 by { m'_div(n, m, k); }
    assert k' > 0 by { k'_min_bounds(n, m', k); } 

    (a' * neg_m' + n * b') % k' == 0
}

ghost predicate A'IsDivisibleByK'(n: nat, m: nat, k: nat, a: nat, b: nat)
    requires sqr(isqrt(n)) != n
    requires 0 < k <= isqrt(n) + m
    requires m <= isqrt(n)
    requires (n - sqr(m)) % k == 0
{
    var m' := calc_m'(n, m, k);
    var k', a', b' := calc_k'(n, m', k), calc_a'(n, m', k, a, b), calc_b'(n, m', k, a, b);
    var neg_m' := -(m' as int);

    m'_div(n, m, k);
    k'_min_bounds(n, m', k);
    k'_max_bounds(n, m', k);
    var m'' := calc_m'(n, m', k');

    (a' * m'' + n * b') % k' == 0
}

lemma a_is_divisible1(n: nat, m: nat, k: nat, a: nat, b: nat)
    requires sqr(isqrt(n)) != n
    requires 0 < k <= isqrt(n) + m
    requires m <= isqrt(n)
    requires (n - sqr(m)) % k == 0
    requires var m' := calc_m'(n, m, k); (a * m' + n * b) % k == 0 && (a + b * m') % k == 0
    ensures AIsDivisibleByK(n, m, k, a, b)
{
    var m' := calc_m'(n, m, k);
    var k', a', b' := calc_k'(n, m', k), calc_a'(n, m', k, a, b), calc_b'(n, m', k, a, b);
    var neg_m' := -(m' as int);

    assert (n - sqr(m')) % k == 0 by { m'_div(n, m, k); }
    assert k' > 0 by { k'_min_bounds(n, m', k); } 
    assert a' * neg_m' + n * b' == a * k' by { a_is_divisble1_helper2(n, m', k, a, b); }
    assert k' % k' == 0;
    Std.Arithmetic.DivMod.LemmaMulModNoopRight(a, k', k');
    assert (a * k') % k' == 0;
    assert (a' * neg_m' + n * b') % k' == 0;
    assert AIsDivisibleByK(n, m, k, a, b);
}

lemma a_is_divisible(n: nat, m: nat, k: nat, a: nat, b: nat)
    requires sqr(isqrt(n)) != n
    requires 0 < k <= isqrt(n) + m
    requires m <= isqrt(n)
    requires (n - sqr(m)) % k == 0
    requires var m' := calc_m'(n, m, k); (a * m' + n * b) % k == 0 && (a + b * m') % k == 0
    // ensures A'IsDivisibleByK'(n, m, k, a, b)
    // ensures var m' := calc_m'(n, m, k); (a * m' + n * b) % k == 0
{
    // var m' := calc_m'(n, m, k);
    // var k', a', b' := calc_k'(n, m', k), calc_a'(n, m', k, a, b), calc_b'(n, m', k, a, b);
    // var neg_m' := -(m' as int);

    // a_is_divisible1(n, m, k, a, b);

    // assert (a' * neg_m' + n * b') % k' == 0;



    // var m' := calc_m'(n, m, k);
    // var neg_m := -(m as int);
    // var k', a', b' := calc_k'(n, m', k), calc_a'(n, m', k, a, b), calc_b'(n, m', k, a, b);

    // m'_div_helper1(n, m, k);
    // assert (m + m') % k == 0;
    // Std.Arithmetic.DivMod.LemmaMulModNoopRight(a, (m + m'), k);
    // assert (a * (m + m')) % k == 0;
    
    // assert (m' - neg_m) == (m + m');
    // assert ((a * m' + n * b) - (a * neg_m + n * b)) % k == 0;
    // Std.Arithmetic.DivMod.LemmaModEquivalence(a * m' + n * b, a * neg_m + n * b, k);
}

// lemma main_inv(n: nat, m: nat, k: nat, a: nat, b: nat)
//     requires sqr(a) - n * sqr(b) == k
//     requires 0 < k <= isqrt(n) + m
//     requires m <= isqrt(n)
//     requires var m' := calc_m'(n, m, k); (a * m' + n * b) % k == 0 && (a + b * m') % k == 0 && (n - sqr(m')) % k == 0
//     // 
//     // ensures
//     //     var m' := calc_m'(n, m, k);
//     //     var k' := calc_k'(n, m', k);
//     //     var a' := calc_a'(n, m', k, a, b);
//     //     var b' := calc_b'(n, m', k, a, b);
//     //     n * sqr(b') - sqr(a') == k'
// {
//     var m' := calc_m'(n, m, k);
//     var k' := calc_k'(n, m', k);
//     var a' := calc_a'(n, m', k, a, b);
//     var b' := calc_b'(n, m', k, a, b);

//     LemmaSquareDivisibleBySquare(a + b * m', k);
//     // assert sqr(a + b * m') % k == 0;

//     calc {
//         n * sqr(b') - sqr(a');
//     ==
//         n * sqr((a + b * m') / k) - sqr((a * m' + n * b) / k);
//     == { LemmaSquareOfQuotient(a + b * m', k); LemmaSquareOfQuotient(a * m' + n * b, k); }
//         n * (sqr(a + b * m') / sqr(k)) - sqr(a * m' + n * b) / sqr(k);
//     == { LemmaMulDivCancelFactor(n, sqr(a + b * m'), sqr(k)); }
//         (n * sqr(a + b * m')) / sqr(k) - sqr(a * m' + n * b) / sqr(k);
//     }

//     //  Std.Arithmetic.DivMod.LemmaMulModNoopGeneral(a * m' + n * b, a * m' + n * b, k);
//     //     assert sqr(a * m' + n * b) % k == 0;
    
//     // Std.Arithmetic.DivMod.LemmaMulModNoopGeneral(a + b * m', a + b * m', k);
//     // assert (sqr(a + b * m')) % k == 0;
//     // Std.Arithmetic.DivMod.LemmaMulModNoopGeneral(n, sqr(a + b * m'), k);
//     // assert (n * sqr(a + b * m')) % k == 0;

//     // Std.Arithmetic.DivMod.LemmaSubModNoop(n * sqr(a + b * m'), sqr(a * m' + n * b), k);
//     // assert (n * sqr(a + b * m') - sqr(a * m' + n * b)) % k == 0;

//     // calc {
//     //     (n * sqr(a + b * m')) / k - sqr(a * m' + n * b) / k;
//     //     == { LemmaDivSubtractDivisible(n * sqr(a + b * m'), sqr(a * m' + n * b), k); }
//     //     (n * sqr(a + b * m') - sqr(a * m' + n * b)) / k;
//     //     == { assert (n * sqr(a + b * m') - sqr(a * m' + n * b)) / k == n - sqr(m'); }
//     //     n - sqr(m');
//     // }

//     // obv_eq(n, m', k, a, b);
//     // assert n * sqr(a + b * m') - sqr(a * m' + n * b) == k * (n - sqr(m'));
//     // assert (n * sqr(a + b * m') - sqr(a * m' + n * b)) / k == n - sqr(m');
    
//     // assert (n * sqr(a + b * m')) / k - sqr(a * m' + n * b) / k == n - sqr(m') by {
//     //     LemmaDivSubtractDivisible(n * sqr(a + b * m'), sqr(a * m' + n * b), k);
//     // }
    
//     // Std.Arithmetic.DivMod.LemmaDivDenominator(n * sqr(a + b * m') - sqr(a * m' + n * b), k, k);
//     // assert ((n * sqr(a + b * m') - sqr(a * m' + n * b)) / k) / k == (n - sqr(m')) / k;
//     // assert (n * sqr(a + b * m') - sqr(a * m' + n * b)) / sqr(k) == (n - sqr(m')) / k;


//     // assert n * sqr(a + b * m') % sqr(k) == 0;
//     // LemmaDivSubtractDivisible(n * sqr(a + b * m'), sqr(a * m' + n * b), sqr(k));
//     // assert n * sqr(a + b * m') / sqr(k) - sqr(a * m' + n * b) / sqr(k) == (n - sqr(m')) / k;

   
// }

// method DoStep(n: nat, nsqrt: nat, m: nat, k: nat, sign: bool, a: nat, b: nat)
//     returns (m': nat, k': nat, a': nat, sign': bool, b': nat)
//     requires nsqrt == isqrt(n)
//     requires sqr(isqrt(n)) != n
//     //
//     requires 0 < k <= isqrt(n) + m
//     requires 0 < m <= isqrt(n)
//     requires (n - sqr(m)) % k == 0
//     // requires (if sign then n*sqr(b)-sqr(a) == k else sqr(a) - n * sqr(b) == k)
//     //
//     ensures 0 < k' <= isqrt(n) + m'
//     ensures 0 < m' <= isqrt(n)
//     ensures (n - sqr(m')) % k' == 0
//     ensures sign' == !sign
// {
//     m' := calc_m'(n, m, k);
//     k' := calc_k'(n, m', k);
//     a' := calc_a'(n, m', k, a, b);
//     b' := calc_b'(n, m', k, a, b);
//     sign' := !sign;

//     m'_div(n, m, k);
//     k'_min_bounds(n, m', k);
//     k'_max_bounds(n, m', k);
//     // assert k' == (n - sqr(m')) / k;
//     assert k' * k == (n - sqr(m'));
//     assert (k' * k) % k' == (n - sqr(m')) % k';
//     Std.Arithmetic.DivMod.LemmaModMultiplesBasic(k, k');
// }

// method Chakravala(n: nat)
//     returns (a: nat, b: nat)
//     decreases *
// {
//     var nsqrt := isqrt(n);
//     if sqr(nsqrt) == n {
//         a, b := 1, 0;
//         return;
//     }

//     var m, k, sign := 1, 1, false;
//     a, b := 1, 0;

//     m, k, a, b := DoStep(n, nsqrt, m, k, a, b);

//     while k != 1 || sign
//         decreases *
//         invariant 0 < k <= isqrt(n) + m
//         invariant 0 < m <= isqrt(n)
//         invariant (n - sqr(m)) % k == 0
//     {
//         m, k, a, b := DoStep(n, nsqrt, m, k, a, b);
//         sign := !sign;
//     }
// }