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
