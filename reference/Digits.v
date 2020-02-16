Require Import ZArith Lia.
Require Import Flocq.Core.Digits Flocq.Core.Core.
Require Import Zaux.

(** * auxiliary definitions for binary lengths of numbers *)
Open Scope Z.

(* binary length of an int ignoring the sign *)
Definition digits2_Z (m : Z) := Z.log2 (Z.abs m) + 1.

Lemma digits2_Z_Zdigits (m : Z) :
  m <> 0 ->
  digits2_Z m = Zdigits radix2 m.
Proof.
  intros.
  rewrite <-Zdigits2_Zdigits.
  unfold digits2_Z, Zdigits2.
  destruct m; try omega;
    simpl Z.abs; rewrite Zlog2_log_inf.
  all: induction p; simpl;
         try rewrite Pos2Z.inj_succ, <-IHp; try discriminate.
  all: reflexivity.
Qed.

Lemma digits2_mul_pow2 (m : Z) (d : positive) :
  m <> 0 ->
  digits2_Z (m * two_power_pos d) = digits2_Z m + Z.pos d.
Proof.
  intro.
  rewrite two_power_pos_equiv.
  unfold digits2_Z.
  rewrite Z.abs_mul, Z.abs_pow.
  replace (Z.abs 2) with 2 by reflexivity.
  remember (Z.abs m) as pm; remember (Z.pos d) as pd.
  rewrite Z.log2_mul_pow2.
  all: lia.
Qed.

Lemma digits2_div_pow2 (m : Z) (d : positive) :
  m <> 0 ->
  m mod two_power_pos d = 0 ->
  digits2_Z (m / two_power_pos d) = digits2_Z m - Z.pos d.
Proof.
  intros M H.
  unfold digits2_Z.
  rewrite Zabs_div_exact.
  rewrite two_power_pos_equiv in *.
  rewrite Z.abs_pow.
  remember (Z.abs m) as pm; remember (Z.pos d) as pd.
  apply Zmod_divides in H; destruct H.
  subst m.
  rewrite Z.abs_mul, Z.abs_pow in Heqpm.
  replace (Z.abs 2) with 2 in * by reflexivity.
  subst pm.
  remember (Z.abs x) as px.
  rewrite Z.mul_comm.
  rewrite Z.div_mul.
  rewrite Z.log2_mul_pow2.
  all: subst.
  all: try lia.
  destruct (Z.eq_dec x 0); subst; lia.
  destruct (Z.eq_dec (2 ^ Z.pos d) 0); [ rewrite e in M; lia | assumption ].
  assert (m mod 2 ^ Z.pos d < 2 ^ Z.pos d); try lia.
  apply Zmod_pos_bound.
  apply Z.pow_pos_nonneg; lia.
  rewrite two_power_pos_equiv; generalize (Z.pow_pos_nonneg 2 (Z.pos d)); lia.
Qed.
