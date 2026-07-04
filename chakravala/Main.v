From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div choice fintype fingraph.
From HB Require Import structures.
From Stdlib Require Import Logic.EqdepFacts Arith.Wf_nat.
From Equations Require Import Equations.

From Stdlib Require Extraction.
Extraction Language OCaml.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Fixpoint isqrt (n: nat): nat :=
    match n with
    | 0 => 0
    | n'.+1 => let i := isqrt n' in if (i + 1) ^ 2  <= n then (i + 1) else i
    end.

Lemma isqrt_min_bounds (n: nat) : (isqrt n) ^ 2 <= n. 
Proof.
    elim: n=> [|n IH] //=.
    case: (leqP ((isqrt n + 1) ^ 2) n.+1) => hab //=.
    apply: leq_trans.
    by exact: IH.
    by exact: leqnSn.
Qed.

Lemma isqrt_max_bounds (n: nat) : n < (isqrt n + 1) ^ 2.
Proof.
    elim: n=> [|n IH] //=.
    case: (leqP ((isqrt n + 1) ^ 2) n.+1) => hab //=.
    rewrite sqrnD muln1 -[1 ^ 2]mulnn muln1 addn1.
    rewrite -(leq_add2r 1) addn1 in IH.
    apply: (leq_trans IH).
    rewrite [(isqrt n + 1) ^ 2 + 1] addn1.
    by apply: ltn_addr.
Qed.

Lemma mod_between (a b : nat) (H1 : 0 < b) (H : b <= a < b.*2) : a %% b = a - b.
Proof.
    move/andP: H => [Hl Hr].
    apply/eqP.
    rewrite -(eqn_add2r b) subnK //.
    rewrite -{2}[b]mul1n.
    have -> : 1 = a %/ b. apply/eqP. rewrite eqn_leq. apply/andP. constructor ; first by rewrite divn_gt0. by rewrite -ltnS ltn_divLR // mul2n.
    by rewrite addnC -divn_eq.
Qed.

Lemma square_div (a b : nat) (H : b %| a) : (a %/ b) ^ 2 = (a ^ 2) %/ (b ^ 2).
Proof.
    by rewrite -mulnn divn_mulAC // ; rewrite muln_divA // ; rewrite -divnMA.
Qed.

Section Def.

Variable (N: nat).

Definition nsqrt := isqrt N.
Hypothesis NSQRT : nsqrt ^ 2 != N.

Lemma sqr_nsqrt_ltn_N : nsqrt ^ 2 < N.
Proof.
 rewrite ltn_neqAle. apply/andP. constructor=> //. by apply: isqrt_min_bounds.
Qed.

Lemma DNSQRT : forall (x : nat), (x * x) != N.
Proof.
  move => x. rewrite mulnn neq_ltn.
  case: (leqP x nsqrt). rewrite -leq_sqr=> H.
  by move: (leq_ltn_trans H sqr_nsqrt_ltn_N)=> ->.
  rewrite -leq_sqr -addn1=> H.
  move: (leq_trans (isqrt_max_bounds N) H)=> -> /=.
  by exact: orbT.
Qed.

Lemma nsqrt_is_positive : nsqrt > 0.
Proof.
  case H1: nsqrt=> //=.
  move: (isqrt_max_bounds N). rewrite -/nsqrt H1 add0n exp1n.
  case H2: N=> //= _. rewrite ltnn.
  move: (DNSQRT 0). by rewrite H2.
Qed.

Definition calc_m' (m k : nat) := nsqrt - ((nsqrt + m) %% k).
Definition calc_k' (m' k : nat) := (N - m' ^ 2) %/ k.
Definition calc_a' (m' k a b : nat) := (a * m' + N * b) %/ k.
Definition calc_b' (m' k a b : nat) := (a + b * m') %/ k.

Section BasicInvariants.

Variables (m k a b : nat).
Hypothesis k_is_bounded : 0 < k <= nsqrt + m.
Hypothesis m_is_bounded : 0 < m <= nsqrt.
Hypothesis nsqrt_is_bounded : nsqrt < m + k.
Hypothesis m_divisible  : k %| (N - m ^ 2).

Let m' := calc_m' m k.
Let k' := calc_k' m' k.

Lemma helper1 : (nsqrt + m) %% k < nsqrt.
Proof.
  move/andP: k_is_bounded=> [Hkl Hkr].
  move/andP: m_is_bounded=> [_ Hmr].
  case: (leqP k nsqrt) => H1. (* first by *) apply: leq_trans. by apply: ltn_pmod. by [].
  rewrite mod_between //. rewrite ltn_subCl //. rewrite addKn. by apply: (leq_ltn_trans Hmr).
  by exact: leq_addr.
  apply/andP. constructor=> //=.
  rewrite -addnS -addnn. apply: leq_add. by apply: ltnW. by apply: (leq_ltn_trans Hmr).
Qed.

Lemma helper2 : k <= nsqrt + m'.
Proof.
  move/andP: k_is_bounded=> [Hkl Hkr]. move/andP: m_is_bounded=> [Hml Hmr].
  rewrite /m' /calc_m' -{2}[nsqrt](addnK m) {1}(divn_eq (nsqrt + m) k) -subnDA subnDr addnBCA //.
  rewrite -{1}[k]addn0 leq_add //.
  rewrite -{1}[k]mul1n leq_pmul2r //. rewrite divn_gt0 //.
  rewrite -(leq_add2r ((nsqrt + m) %% k)) -divn_eq {2}[nsqrt + m]addnC leq_add2l.
  apply: ltnW. by exact: helper1.
Qed.

Lemma m'_is_positive : m' > 0.
Proof. rewrite subn_gt0. by exact: helper1. Qed. 

Lemma m'_has_upper_bound : m' <= nsqrt.
Proof. exact: leq_subr. Qed.

Lemma m_sqr_leq_N : m ^ 2 <= N.
Proof.
  apply: leq_trans ; last by apply: isqrt_min_bounds.
  rewrite leq_sqr. 
  by move/andP: m_is_bounded ; case.
Qed.

Lemma m_sqr_ltn_N : m ^ 2 < N.
Proof.
  rewrite ltn_neqAle. apply/andP. constructor ; last by exact: m_sqr_leq_N.
  by apply: (DNSQRT m).
Qed.

Lemma m'_sqr_leq_N : m' ^ 2 <= N.
Proof.
  apply: leq_trans ; last by apply: isqrt_min_bounds.
  rewrite leq_sqr. by exact: m'_has_upper_bound.
Qed.

Lemma m'_sqr_ltn_N : m' ^ 2 < N.
Proof.
  rewrite ltn_neqAle. apply/andP. constructor ; last by exact: m'_sqr_leq_N.
  by apply: (DNSQRT m').
Qed.

Lemma m'_is_bounded : 0 < m' <= nsqrt.
Proof.
    apply/andP. constructor. exact: m'_is_positive. exact: m'_has_upper_bound.
Qed.

Lemma m'_divisible_k' : k %| (m + m').
Proof.
    rewrite /m' /calc_m' addnBA addnC /dvdn. rewrite modnB. by rewrite modn_mod addnK ltnn.
    - by move/andP: k_is_bounded=> [Htemp _].
    - by exact: leq_mod.
    - apply: ltnW. rewrite addnC. by exact: helper1.
Qed.

Lemma m'_divisible_k : k %| (N - m' ^ 2).
Proof.
  case: (leqP m m')=> H1. 
  - rewrite -[N - _](addnK (m ^ 2)) addBnA //. rewrite subnAC.
    apply: dvdn_sub=> //. rewrite subn_sqr dvdn_mull //. rewrite addnC. by exact: m'_divisible_k'.
    by exact: m'_sqr_leq_N.
    by rewrite leq_sqr.
  - rewrite -[N - _](addKn (m ^ 2)) addnABC. rewrite addnC -addnCBA.
    apply: dvdn_add=> //. rewrite subn_sqr dvdn_mull //. by exact: m'_divisible_k'.
    by exact: m_sqr_leq_N.
    by rewrite leq_sqr ; apply: ltnW.
    by exact: m'_sqr_leq_N. 
Qed.

Lemma m'_divisible_k'_2 : k' %| (N - m' ^ 2).
Proof.
  apply: dvdn_div. by exact: m'_divisible_k.
Qed.

Lemma k'_is_positive : 0 < k'.
Proof.
  rewrite ltn_divRL. rewrite mul0n subn_gt0. by exact: m'_sqr_ltn_N .
  by exact: m'_divisible_k.
Qed.

Lemma k'_has_upper_bound : k' <= nsqrt + m'.
Proof.
  have helper2 : nsqrt - m' < k.
    rewrite subKn. rewrite ltn_mod. by move/andP: k_is_bounded ; case. apply: ltnW. by exact: helper1.
  rewrite -(leq_add2r 1) addn1.
  rewrite ltn_divLR . rewrite mulnDl mul1n. rewrite -[N - _](addKn (nsqrt ^ 2)) addnBCA.
  rewrite subDnCA. rewrite -ltn_subRL. rewrite subn_sqr [_ + k]addnC -addnBA [_ * k]mulnC.
  rewrite -mulnBl.
  have H : N - nsqrt ^ 2 < 2 * nsqrt + 1.
    rewrite ltn_subLR.
    rewrite [_ + 1]addnC -{2}(exp1n 2) -{2}[nsqrt]muln1 addnA -sqrnD.
    by apply: isqrt_max_bounds.
    by apply: isqrt_min_bounds.
  apply: (leq_trans H).
  rewrite [_ + 1]addnC.
  rewrite -{1}[k](addnK (nsqrt - m')).
  rewrite subDnCA. rewrite -addnA -mulnS.
  have -> : 1 + 2 * nsqrt = nsqrt - m' + 1 * (nsqrt + m').+1.
    rewrite mul1n addnS [nsqrt + m']addnC addnA subnK.
    by rewrite mul2n add1n addnn.
    by exact: m'_has_upper_bound.
  rewrite leq_add2l leq_pmul2r. rewrite subn_gt0 //.
  by exact: ltn0Sn.
  by apply: ltnW.
  rewrite leq_pmul2r ; first by apply: ltnW. apply: ltn_addl. by exact: m'_is_positive.
  by exact: isqrt_min_bounds.
  rewrite leq_sqr. by move/andP: m'_is_bounded ; case.
  by exact: m'_sqr_leq_N.
  by move/andP: k_is_bounded ; case.
Qed.

Lemma k'_is_bounded : 0 < k' <= nsqrt + m'.
Proof.
  apply/andP. constructor. by exact: k'_is_positive. by exact: k'_has_upper_bound.
Qed.

Lemma nsqrt_is_bounded' : nsqrt < m' + k'.
Proof.
  move: m'_divisible_k=> H1.
  rewrite -ltn_psubLR /k' /calc_k' ltn_divRL //.
  have H : nsqrt ^ 2 - m' ^ 2 < N - m' ^ 2.
    rewrite ltn_sub2rE. by exact: sqr_nsqrt_ltn_N. rewrite leq_sqr. by exact: m'_has_upper_bound.
  apply: leq_ltn_trans ; last by exact: H.
  rewrite subn_sqr leq_mul2l. apply/orP. constructor 2. by exact: helper2.
  
  rewrite mul0n subn_gt0. by exact: m'_sqr_ltn_N.
Qed.

Lemma cancel_calc_k' : calc_k' m (calc_k' m k) = k.
Proof.
  rewrite /calc_k' divnA. rewrite mulKn //.
  rewrite subn_gt0. by exact: m_sqr_ltn_N.
  by exact: m_divisible.
Qed.

Lemma cancel_calc_m' : calc_m' (calc_m' m k) k = m.
Proof.
   rewrite /calc_m'.
   rewrite {1}[nsqrt + _]addnC -{4}[nsqrt](addnK m) addnBA.
   rewrite {2}(divn_eq (nsqrt + m) k) [_ + (nsqrt + m) %% k]addnC addnA subnK.
   rewrite -addnCBA. rewrite modnMDl.
   move: modn_small nsqrt_is_bounded. rewrite -ltn_psubLR. move => /[apply] ->.
   rewrite subKn //.
   by move/andP: m_is_bounded ; case.
   by move/andP: k_is_bounded ; case.
   by move/andP: m_is_bounded ; case.
   apply: ltnW. by apply: helper1.
   by exact: leq_addl.
Qed. 

End BasicInvariants.

Section AB_invariants.

Variables (m k a b : nat).
Hypothesis k_is_bounded : 0 < k <= nsqrt + m.
Hypothesis m_is_bounded : 0 < m <= nsqrt.
Hypothesis nsqrt_is_bounded : nsqrt < m + k.
Hypothesis m_divisible  : k %| (N - m ^ 2).

Let m' := calc_m' m k.
Let k' := calc_k' m' k.
Let a' := calc_a' m' k a b.
Let b' := calc_b' m' k a b.

Let m'' := calc_m' m' k'.

Hypothesis a_invariant : k %| (a * m' + N * b).
Hypothesis b_invariant : k %| (a + b * m').

Lemma first_main_invariant (main_invariant : (a ^ 2) - N * (b ^ 2) = k) : N * (b' ^ 2) - (a' ^ 2) = k'.
Proof.
    rewrite square_div //. rewrite square_div //.
    rewrite muln_divA.
    rewrite -divnBr.
    rewrite !sqrnD.
    rewrite mulnDr.
    have -> : N * (2 * (a * (b * m'))) = 2 * (a * m' * (N * b)). rewrite mulnA [N * 2]mulnC mulnACA -mulnA. congr (2 * _). rewrite mulnA [b * m']mulnC mulnACA. by congr (_ * _).
    rewrite subnDr mulnDr subnDA -addnCBA.  
    have -> : N * a ^ 2 - (a * m') ^ 2 = a^2 * (N - m' ^ 2) by rewrite [a * m']mulnC expnMn -mulnBl {1}mulnC.
    rewrite -subnCBA.
    have -> : (N * b) ^ 2 - N * (b * m') ^ 2 = N * b ^ 2 * (N - m' ^ 2) by rewrite expnMn expnMn mulnA -{1}mulnn mulnAC -mulnBr.
    rewrite -mulnBl main_invariant divnMl //.
    - by move/andP: k_is_bounded=> [Htemp _].
    - rewrite expnMn expnMn mulnA -(mulnn N) [N * N * _]mulnAC.
      apply: leq_mul ; first by [].
      apply: leq_trans.
      by move: (m'_has_upper_bound m k) ; rewrite -leq_sqr=> Htemp ; exact: Htemp. by exact: isqrt_min_bounds.
    - rewrite expnMn [N * _]mulnC. apply: leq_mul ; first by [].
      apply: leq_trans. by move: (m'_has_upper_bound m k) ; rewrite -leq_sqr=> Htemp ; exact: Htemp. by exact: isqrt_min_bounds.  
    - by apply: dvdn_mul.
    - by apply: dvdn_mul.
Qed.

Lemma second_main_invariant (main_invariant : N * (b ^ 2) - (a ^ 2) = k) : (a' ^ 2) - N * (b' ^ 2) = k'.
Proof.
    rewrite square_div //. rewrite square_div //.
    rewrite muln_divA.
    rewrite -divnBr.
    rewrite !sqrnD.
    rewrite mulnDr.
    have -> : N * (2 * (a * (b * m'))) = 2 * (a * m' * (N * b)). rewrite mulnA [N * 2]mulnC mulnACA -mulnA. congr (2 * _). rewrite mulnA [b * m']mulnC mulnACA. by congr (_ * _).
    rewrite subnDr mulnDr subnDAC -addBnAC.
    have -> : (N * b) ^ 2 - N * (b * m') ^ 2 = N * b ^ 2 * (N - m' ^ 2) by rewrite expnMn expnMn mulnA -{1}mulnn mulnAC -mulnBr.
    rewrite -subnBA.
    have -> : N * a ^ 2 - (a * m') ^ 2 = a^2 * (N - m' ^ 2) by rewrite [a * m']mulnC expnMn -mulnBl {1}mulnC.
    rewrite -mulnBl main_invariant divnMl. by [].
    - by move/andP: k_is_bounded=> [Htemp _].
    - rewrite expnMn [N * _]mulnC. apply: leq_mul ; first by [].
      apply: leq_trans. by move: (m'_has_upper_bound m k) ; rewrite -leq_sqr=> Htemp ; exact: Htemp. by exact: isqrt_min_bounds.  
    - rewrite expnMn expnMn mulnA -(mulnn N) [N * N * _]mulnAC.
      apply: leq_mul ; first by [].
      apply: leq_trans. by move: (m'_has_upper_bound m k) ; rewrite -leq_sqr=> Htemp ; exact: Htemp. by exact: isqrt_min_bounds.
    - by apply: dvdn_mull ; apply: dvdn_mul.
    - by apply: dvdn_mul.
Qed.

Lemma a'_invariant : k' %| (a' * m'' + N * b').
Proof.
  have H1 : k' %| (m' + m''). apply: m'_divisible_k'. by apply: k'_is_bounded. by apply: m'_is_bounded.
  rewrite divn_mulAC // muln_divA // -divnDr. rewrite mulnDl mulnDr addnACA mulnA -mulnDr.
  have -> : a * m' * m'' + N * a + N * b * (m'' + m') = a * (N - m' ^ 2) + (a * m' + N * b) * (m' + m'').
    apply/eqP.
    rewrite [m'' + m']addnC [(a * m' + N * b) * (m' + m'')]mulnDl addnA eqn_add2r.
    rewrite addnC mulnDr addnA eqn_add2r mulnBr [N * a]mulnC -mulnA mulnn subnK //.
    apply: leq_mul=> //. by apply: m'_sqr_leq_N.
  rewrite divnDl.
  apply: dvdn_add.
  rewrite -muln_divA. rewrite dvdn_mull //. by exact: m'_divisible_k.
  rewrite -divn_mulAC //. rewrite dvdn_mull //.
  rewrite dvdn_mull //. by exact: m'_divisible_k.
  rewrite dvdn_mull //.
Qed.

Lemma b'_invariant : k' %| (a' + b' * m'').
Proof.
  have H1 : k' %| (m' + m''). apply: m'_divisible_k'. by apply: k'_is_bounded. by apply: m'_is_bounded.
  Search ((_ + _) %% _).
  rewrite divn_mulAC // -divnDl // mulnDl addnACA -mulnDr.
  have -> : a * (m' + m'') + (N * b + b * m' * m'') = (a + b * m') * (m' + m'') + b * (N - m' ^ 2).
    apply/eqP.
    rewrite [(a + b * m') * (m' + m'')]mulnDl -addnA eqn_add2l {1}addnC [m' + m'']addnC mulnDr -addnA eqn_add2l -mulnA mulnn mulnBr subnKC mulnC //.
    rewrite mulnC. apply: leq_mul=> //. by apply: m'_sqr_leq_N.
  rewrite divnDl. rewrite -divn_mulAC // -muln_divA.
  by apply: dvdn_add ; rewrite dvdn_mull.
  by apply: m'_divisible_k.
  by rewrite dvdn_mulr.
Qed.

End AB_invariants.

Record base : Set := mkBase { m: nat; k: nat; sign: bool; }.

Definition base_eqn (b1 b2 : base) := 
  [ && b1.(m) == b2.(m)
     , b1.(k) == b2.(k)
     & b1.(sign) == b2.(sign)
  ].

Lemma base_eqnP : Equality.axiom base_eqn.
Proof.
  move=> [m1 k1 sign1] [m2 k2 sign2]. rewrite /base_eqn /=.
  by apply: (iffP and3P)=> [[/eqP -> /eqP -> /eqP ->] | [-> -> ->]].
Qed.

HB.instance Definition _ := hasDecEq.Build base base_eqnP.

Lemma base_eq : forall (b1 b2 : base),
  b1.(m) = b2.(m) ->
  b1.(k) = b2.(k) ->
  b1.(sign) = b2.(sign) ->
  b1 = b2.
Proof.
  by move=> [m1 k1 s1] [m2 k2 s2] /= -> -> ->.
Qed.

Definition start_base : base := {| m := nsqrt; k := 1; sign := false |}.

Definition validBase (b : base) : bool :=
  [ && 0 < b.(k) <= nsqrt + b.(m)
     , 0 < b.(m) <= nsqrt
     , nsqrt < b.(m) + b.(k)
     & b.(k) %| (N - b.(m) ^ 2)
  ].

Inductive vbase : predArgType := VBase t of validBase t. 

Coercion base_of_vbase b := let: VBase t _ := b in t.

HB.instance Definition _ := [isSub of vbase for base_of_vbase].

Lemma start_base_is_valid : validBase start_base.
Proof.
  apply/and4P=> //=. constructor.
  rewrite ltn_addr //. by exact: nsqrt_is_positive.
  apply/andP ; constructor=> //=. by exact: nsqrt_is_positive.
  by rewrite addn1.
  by [].
Qed.

Definition start_vbase : vbase := VBase start_base_is_valid.

Definition donor : Type := (ordinal nsqrt) * (ordinal nsqrt.*2) * bool.
Check (Finite.class donor).

Definition donor2vbase (d : donor) : option vbase :=
  let: ((m, k), sign) := d in
  insub (mkBase (m.+1) (k.+1) sign).

Lemma vbase2donor_k (vb : vbase) : (val vb).(k).-1 < nsqrt.*2.
Proof.
  move: vb=> [b H]=> /=.
  rewrite -addnn.
  case H1: (k b)=> //=. apply: ltn_addr. by exact: nsqrt_is_positive.
  move: H=> /and4P [/andP [_ H2] /andP [_ H3] _ _].
  rewrite -H1.
  apply: (leq_trans H2). apply: leq_add=> //.
Qed.

Lemma vbase2donor_m  (vb : vbase) : (val vb).(m).-1 < nsqrt.
Proof.
  move: vb=> [b H]=> /=.
  case H1: b.(m)=> //=. by exact: nsqrt_is_positive.
  move: H=> /and4P [_ /andP [_ H2] _ _].
  by rewrite -H1.
Qed.

Definition vbase2donor (vb : vbase) : donor := 
  ((Ordinal (vbase2donor_m vb), Ordinal (vbase2donor_k vb)), (val vb).(sign)).

Lemma pcancel_donor : pcancel vbase2donor donor2vbase.
Proof.
  move=> [b H] /= . rewrite !prednK //=.
  have -> : {| m := m b; k := k b; sign := sign b |} = b by apply: base_eq=> //=.
  apply: insubT.
  by move: H=> /and4P [/andP [H _] _ _ _].
  by move: H=> /and4P [_ /andP [H _] _ _].
Qed.

HB.instance Definition _ := Equality.copy vbase (pcan_type pcancel_donor).
HB.instance Definition _ := Choice.copy vbase (pcan_type pcancel_donor).
HB.instance Definition _ := Countable.copy vbase (pcan_type pcancel_donor).
HB.instance Definition _ := Finite.copy vbase (pcan_type pcancel_donor).

HB.about vbase.

Definition step (b : base) : base :=
  let m' := calc_m' b.(m) b.(k)
  in {| m := m'; k := calc_k' m' b.(k); sign := negb b.(sign) |}.

Lemma step_vbase_prf (b : vbase) : validBase (step (val b)).
Proof.
  move: b => [b /[dup] /and4P [H1 H2 H3 H4] VB].
  apply/and4P ; split ; rewrite /step /=.
  - by apply: k'_is_bounded.
  - by apply: m'_is_bounded.
  - by apply: nsqrt_is_bounded'.
  - by apply: m'_divisible_k'_2.
Qed.

Definition vstep (b : vbase) : vbase := VBase (step_vbase_prf b).

Definition step_inv (b : base) : base :=
  let k_inv := calc_k' b.(m) b.(k)
  in {| m := calc_m' b.(m) k_inv; k := k_inv; sign := negb b.(sign) |}.

Lemma step_cancel_relax (b : vbase) : step_inv (val (vstep b)) = val b.
Proof.
  move: b => [b /[dup] /and4P [H1 H2 H3 H4] VB] /=. 
  set m' := calc_m' b.(m) b.(k).
  rewrite /step /step_inv /=.
  apply: base_eq=> /=. 
  rewrite cancel_calc_k' //. rewrite cancel_calc_m' //.
  by apply: m'_is_bounded. by exact: m'_divisible_k.
  rewrite cancel_calc_k' //. by apply: m'_is_bounded. by exact: m'_divisible_k.
  by case: (sign b).
Qed.

Lemma vstep_inj : injective vstep.
Proof.
  move=> b1 b2 H. apply: val_inj. by rewrite -step_cancel_relax H step_cancel_relax.
Qed.

Definition is_in_orbit (vb : vbase) := exists n, iter n vstep start_vbase = vb.

Lemma helper3 (i : nat) (x : vbase) : iter i (iter (order vstep x) vstep) x = x.
Proof.
  elim: i=> [|i IH] //=.
  rewrite IH. by exact: (iter_order vstep_inj).
Qed.

Definition terminates (vb : vbase) := { i | (i < (order vstep start_vbase)) /\ (iter i vstep (vstep start_vbase) == vb) }.

Record state : Type := mkState { 
  s_vbase : vbase;
  s_a : nat;
  s_b : nat;
  s_ab_invariant : [ /\ (s_vbase.(k) %| (s_a * calc_m' s_vbase.(m) s_vbase.(k) + N * s_b))
                      , (s_vbase.(k) %| (s_a + s_b * calc_m' s_vbase.(m) s_vbase.(k)))
                      , ~~ s_vbase.(sign) \/ N * (s_b ^ 2) - (s_a ^ 2) = s_vbase.(k)
                      , s_vbase.(sign) \/ (s_a ^ 2) - N * (s_b ^ 2) = s_vbase.(k)
                      & s_b != 0
                   ];               
  s_terminates : terminates s_vbase
 }.


Lemma terminates_initial_state_prf : (0 < (order vstep start_vbase)) /\ (iter 0 vstep (vstep start_vbase) == (vstep start_vbase)).
Proof. constructor=> //. Qed.

Definition terminates_initial_state : terminates (vstep start_vbase) := exist _ 0 terminates_initial_state_prf.

Lemma initial_ab_invariant :
  let vb := step start_vbase in
  let a := nsqrt in
  let b := 1 in
  [ /\ (vb.(k) %| (a * calc_m' vb.(m) vb.(k) + N * b))
    , (vb.(k) %| (a + b * calc_m' vb.(m) vb.(k)))
    , ~~ vb.(sign) \/ N * (b ^ 2) - (a ^ 2) = vb.(k)
    , vb.(sign) \/ (a ^ 2) - N * (b ^ 2) = vb.(k)
    & b != 0
  ].
Proof.
  have Hnsqrt1 : nsqrt + nsqrt - (nsqrt + nsqrt) %% (N - nsqrt ^ 2) = (nsqrt + nsqrt) %/ (N - nsqrt ^ 2) * (N - nsqrt ^ 2) by rewrite {1}(divn_eq (nsqrt + nsqrt) (N - nsqrt ^ 2)) -{2}[_ %% _]add0n subnDr subn0.
  have Hnsqrt2 : (nsqrt + nsqrt) %% (N - nsqrt ^ 2) <= nsqrt.
    case: (leqP (N - nsqrt ^ 2) nsqrt).
    apply: leq_trans. apply: ltnW. apply: ltn_pmod. rewrite subn_gt0. by exact: sqr_nsqrt_ltn_N.
    have H : N - nsqrt ^ 2 <= nsqrt.*2 by move: (isqrt_max_bounds N) ; rewrite sqrnD muln1 exp1n mul2n addn1 addSn ltnS -leq_subLR.
    rewrite addnn=> H2. rewrite mod_between. rewrite leq_subCl -addnn addnK. by apply: ltnW.
    apply: leq_ltn_trans ; first by apply: ltnW nsqrt_is_positive. by [].
    apply/andP. constructor=> //. by rewrite ltn_double.
  move=> /=. rewrite /calc_m' /calc_k' /= divn1 modn1 subn0 muln1 mul1n. constructor.
  rewrite -{3}[N](subnK (isqrt_min_bounds N)) addnA addnAC [_ + nsqrt ^ 2]addnC -{2}mulnn -mulnDr [nsqrt + _]addnBA //. 
  rewrite Hnsqrt1 mulnA -mulSnr. by apply: dvdn_mull.
  rewrite addnBA // Hnsqrt1. by apply: dvdn_mull.
  by constructor 2.
  by constructor 1.
  by [].
Qed.

Definition initial_state : state := {| s_vbase := vstep start_vbase; s_a := nsqrt; s_b := 1; s_ab_invariant := initial_ab_invariant; s_terminates := terminates_initial_state;  |}.

Definition distance (s : state) : nat := (order vstep start_vbase) - sval (s_terminates s).

Lemma helper4' (s : state) (H1 : s_vbase s != start_vbase) : 
  let i := sval (s_terminates s) in
  (i.+1 < (order vstep start_vbase)) /\ (iter i.+1 vstep (vstep start_vbase) == vstep (s_vbase s)).
Proof.
  move: (s_terminates s)=> [i [Hlt /eqP Hiter]] /=.
  constructor=> /=.
  rewrite ltn_neqAle. apply/andP. constructor=> //.
  apply/eqP=> H. move/eqP: H1=> H1. apply: H1.
  move: Hiter. by rewrite -iterSr H (iter_order vstep_inj)=> ->.
  apply/eqP. by rewrite Hiter.
Qed.

Definition helper4 (s : state) (H1 : s_vbase s != start_vbase) : terminates (vstep (s_vbase s)) := 
  exist _ (sval (s_terminates s)).+1 (helper4' H1).

Lemma helper5 (s : state) : 
  let vb' := vstep (s_vbase s) in
  let a' := calc_a' vb'.(m) (s_vbase s).(k) s.(s_a) s.(s_b) in
  let b' := calc_b' vb'.(m) (s_vbase s).(k) s.(s_a) s.(s_b) in
  [ /\ (vb'.(k) %| (a' * calc_m' vb'.(m) vb'.(k) + N * b'))
     , (vb'.(k) %| (a' + b' * calc_m' vb'.(m) vb'.(k)))
     , ~~ vb'.(sign) \/ N * (b' ^ 2) - (a' ^ 2) = vb'.(k)
     , vb'.(sign) \/ (a' ^ 2) - N * (b' ^ 2) = vb'.(k)
     & b' != 0
  ].
Proof.
  move: (s_vbase s) (s_ab_invariant s) => [b H] /= [H5 H6 H7 H8]. move: H=> /and4P [H1 H2 H3 H4].
  constructor.
  - apply: a'_invariant=> //=.
  - apply: b'_invariant=> //=.
  - move: H8. case: (sign b)=> /= ; first by constructor 1.
    constructor 2. apply: first_main_invariant=> //=.
    by case: H8=> //.
  - move: H7. case: (sign b)=> /= ; last by constructor 1.
    constructor 2. apply: second_main_invariant=> //=.
    by case: H7=> //.
  - rewrite /calc_b' -lt0n => /=. rewrite ltn_divRL // mul0n. apply: ltn_addl. rewrite muln_gt0. apply/andP. constructor.
      by rewrite lt0n.
      by apply: m'_is_positive.
Qed.

Definition next_step (s : state) (Hneq : s_vbase s != start_vbase) :=
  let vb' := vstep (s_vbase s) in
  let a' := calc_a' vb'.(m) (s_vbase s).(k) s.(s_a) s.(s_b) in
  let b' := calc_b' vb'.(m) (s_vbase s).(k) s.(s_a) s.(s_b) in
  {| s_vbase := vb'; s_a := a'; s_b := b'; s_ab_invariant := helper5 s; s_terminates := helper4 Hneq; |}
  .

Remark chakravala_oblig (s : state) (Hneq : s_vbase s != start_vbase) :
  distance (next_step Hneq) < distance s.
Proof.
  rewrite /distance /=. move: (s_terminates s)=> [i [Hltn Hiter]] /=.
  rewrite ltn_sub2lE //.
Qed.

Definition eqVneq' (s : state) :=
  match eqVneq s.(s_vbase) start_vbase with
  | NeqNotEq h => left h
  | EqNotNeq h => right h
  end.

Equations? chakravala_inner s : state by wf (distance s) lt :=
chakravala_inner s := if eqVneq' s is left Hneq
  then chakravala_inner (next_step Hneq)
  else s.
Proof. apply/ltP. by apply: chakravala_oblig. Qed.

Lemma chakravala_inner_non_trivial (s : state) : (chakravala_inner s).(s_b) != 0.
Proof.
  elim/chakravala_inner_elim: (chakravala_inner s)=> /=.
  move=> s' IH.
  case: (eqVneq' s').
  by exact: IH.
  move: IH=>_ _.
  by move: (s_ab_invariant s')=> [_ _ _ _ H].
Qed.

Lemma chakravala_inner_correct (s : state) :
  let s' := chakravala_inner s in 
  (s'.(s_a) ^ 2) - N * (s'.(s_b) ^ 2) = 1.
Proof.
  elim/chakravala_inner_elim: (chakravala_inner s)=> /=.
  move=> s' IH.
  case: (eqVneq' s').
  by exact: IH.
  move: IH=> _.
  move: (s_ab_invariant s')=> [_ _ _ H _].
  move: H=> /[swap] -> /=.
  case=> //=.
Qed.

End Def.

Check chakravala_inner.

Definition chakravala (n: nat) := 
  if eqVneq ((isqrt n) ^ 2) n is NeqNotEq H
  then let s := chakravala_inner (initial_state H) in (s.(s_a), s.(s_b))
  else (1, 0).

Theorem chakravala_correct (n : nat) :
  let: (a, b) := chakravala n in
  (a ^ 2 - n * (b ^ 2) = 1) /\ ((isqrt n) ^ 2 != n -> b != 0).
Proof.
  move H: (chakravala n)=> [a b].
  constructor.
  move: H. rewrite /chakravala.
  case: (eqVneq ((isqrt n) ^ 2) n).
  move=> _. case=> <- <-. by rewrite exp1n exp0n // muln0 subn0.
  move=> Hneq. case=> <- <-. by apply: chakravala_inner_correct.
  move: H. rewrite /chakravala.
  case: (eqVneq ((isqrt n) ^ 2) n)=> //=.
  move=> Hneq [_ <-] _. by exact: chakravala_inner_non_trivial.
Qed.


Extract Inductive unit => "unit" [ "()" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive alt_spec => "bool" [ "true" "false" ].

Extract Inductive nat => "Z.t" [ "Z.zero" "Z.succ" ] "(fun fO fS n -> if n=0 then fO () else fS (Z.pred n))".

Check modn.
Extract Constant minus => "fun x y -> Z.max (Z.sub x y) Z.zero".
Extract Constant double => "fun x -> Z.add x x".
Extract Constant plus => "Z.add".
Extract Constant predn => "Z.pred".
Extract Constant mult => "Z.mul".
Extract Constant divn => "Z.ediv".
Extract Constant modn => "Z.erem".
Extract Constant odd => "Z.is_odd".
Extract Constant isqrt => "Z.sqrt".
Extract Constant expn => "fun x y -> Z.pow x (Z.to_int y)".
Extract Constant eqb => "( = )".
Extract Constant eqn => "( = )".

Set Extraction Output Directory ".generated".
Extraction "chakravala.ml" chakravala.
