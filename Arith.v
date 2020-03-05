From FloatCohorts Require Import Tactics.
Require Export ZArith PArith Lia Floats.SpecFloat.

Open Scope Z.

Definition div2_opt (p : positive) : option positive :=
  match p with
  | xO p' => Some p'
  | _ => None
  end.

Lemma div2_opt_correct (p d : positive) :
  div2_opt p = Some d <-> p = (d * 2)%positive.
Proof.
  split; intros.
  - destruct p; inversion H.
    cbn.
    rewrite Pos.mul_comm.
    reflexivity.
  -
    rewrite H.
    cbn.
    rewrite Pos.mul_comm.
    reflexivity.
Qed.

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

Lemma digits2_pos_redundant (p : positive) :
  digits2_pos p = Pos.size p.
Proof. reflexivity. Qed.

Lemma pos_size_Z_log2 (p : positive) :
  Z.pos (Pos.size p) = Z.log2 (Z.pos p) + 1.
Proof.
  destruct p; cbn; lia.
Qed.

Lemma pos_size_mul_pow_two (p q : positive) :
  Pos.size (p * 2 ^ q) = (Pos.size p + q)%positive.
Proof.
  enough (Z.pos (Pos.size (p * 2 ^ q)) = (Z.pos (Pos.size p)) + (Z.pos q)) by lia.
  repeat rewrite pos_size_Z_log2.
  rewrite Pos2Z.inj_mul, Pos2Z.inj_pow.
  remember (Z.pos p) as zp.
  remember (Z.pos q) as zq.
  rewrite Z.log2_mul_pow2; lia.
Qed.

Lemma pos_size_monotone (p1 p2 : positive) :
  (p1 <= p2)%positive ->
  (Pos.size p1 <= Pos.size p2)%positive.
Proof.
  generalize dependent p2.
  induction p1; cbn in *; [ | | lia].
  all: intros.
  all: destruct p2; cbn in *; [ | | lia].
  all: assert (p1 <= p2)%positive by lia.
  all: apply IHp1 in H0.
  all: lia.
Qed.

Lemma pos_size_monotone_inv (p1 p2 : positive) :
  (Pos.size p1 < Pos.size p2)%positive ->
  (p1 < p2)%positive.
Proof.
  intros.
  apply Pos.lt_nle.
  intros C.
  apply pos_size_monotone in C.
  lia.
Qed.
