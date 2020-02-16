Require Import ZArith Lia.

(** * general auxiliary lemmas about Z *)
Open Scope Z.

Lemma Zpow_divide (b p1 p2 : Z) :
  0 < b ->
  0 <= p1 <= p2 ->
  (b ^ p1 | b ^ p2).
Proof.
  intros B P.
  rewrite <-Z.mod_divide by (apply Z.pow_nonzero; lia).
  replace p2 with ((p2 - p1) + p1) by lia.
  rewrite Z.pow_add_r by lia.
  apply Z_mod_mult.
Qed.

Lemma Zabs_div_exact (a b : Z) :
  b <> 0 ->
  a mod b = 0 ->
  Z.abs (a / b) = Z.abs a / Z.abs b.
Proof.
  intros B AMB.
  apply Zmod_divides in AMB; [| assumption ].
  destruct AMB as [c AMB].
  rewrite AMB at 1.
  apply f_equal with (f := Z.abs) in AMB.
  rewrite Z.abs_mul in AMB.
  rewrite AMB.
  rewrite Z.mul_comm. rewrite Z.div_mul.
  rewrite Z.mul_comm. rewrite Z.div_mul.
  all: lia.
Qed.
