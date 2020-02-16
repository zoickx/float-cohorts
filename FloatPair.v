Require Export ZArith PArith Lia.
Require Export Relations Classes.EquivDec.

Open Scope Z.

(* simple binary float: no zero, no special values *)
Record float_pair : Set := FPair { FPnum : positive; FPexp : Z}.

Definition fp_equiv_def : relation float_pair :=
  fun fp1 fp2 =>
    let '(m1, e1) := (FPnum fp1, FPexp fp1) in
    let '(m2, e2) := (FPnum fp2, FPexp fp2) in
    or
      ((e2 <= e1) /\ (Z.pos m2 = (Z.pos m1) * 2 ^ (e1 - e2)))
      ((e1 <= e2) /\ (Z.pos m1 = (Z.pos m2) * 2 ^ (e2 - e1))).

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

Instance fp_equiv : Equivalence fp_equiv_def.
Proof.
  unfold fp_equiv_def.
  constructor.
  -
    constructor.
    split.
    reflexivity.
    rewrite Z.sub_diag, Z.pow_0_r, Z.mul_1_r.
    reflexivity.
  -
    unfold Symmetric; intros.
    destruct H; auto.
  -
    intros fp1 fp2 fp3 EQ12 EQ23.
    destruct fp1 as [mp1 e1], fp2 as [mp2 e2], fp3 as [mp3 e3].
    unfold FPnum, FPexp in *.
    remember (Z.pos mp1) as m1; clear Heqm1 mp1.
    remember (Z.pos mp2) as m2; clear Heqm2 mp2.
    remember (Z.pos mp3) as m3; clear Heqm3 mp3.
    destruct EQ12 as [EQ12 | EQ12], EQ23 as [EQ23 | EQ23].
    all: destruct EQ12 as [E12 M12], EQ23 as [E23 M23]; subst.
    + left; split; [lia |].
      rewrite <-Z.mul_assoc.
      rewrite <-Z.pow_add_r; try lia.
      replace (e1 - e2 + (e2 - e3)) with (e1 - e3) by lia.
      reflexivity.
    + destruct (Z.eq_dec e1 e3); subst.
      * (* e1 = e3 *)
        apply Z.mul_reg_r in M23.
        subst; left; split; [lia |].
        rewrite Z.sub_diag; lia.
        pose proof (Z.pow_pos_nonneg 2 (e3 - e2)).
        lia.
      * destruct (Z_lt_le_dec e1 e3).
        -- (* e1 < e3 *)
          assert (E123 : e2 <= e1 < e3) by lia; clear E12 E23 n l.
          right; split; [lia |].
          apply f_equal with (f := fun x => Z.div x (2 ^ (e1 - e2))) in M23.

          rewrite Z_div_mult in M23;
            [| generalize (Z.pow_pos_nonneg 2 (e1 - e2)); lia].
          subst.
          rewrite Z.divide_div_mul_exact;
            [| apply Z.pow_nonzero; lia | apply Zpow_divide; lia].
          replace (e3 - e2) with ((e3 - e1) + (e1 - e2)) by lia.
          rewrite Z.pow_add_r by lia.
          rewrite Z.div_mul by (apply Z.pow_nonzero; lia).
          reflexivity.
        -- (* e3 < e1 *)
          assert (E123: e2 <= e3 < e1) by lia; clear E12 E23 n l.
          left; split; [lia |].
          apply f_equal with (f := fun x => Z.div x (2 ^ (e3 - e2))) in M23.
          rewrite Z_div_mult in M23;
            [| generalize (Z.pow_pos_nonneg 2 (e3 - e2)); lia].
          subst.
          rewrite Z.divide_div_mul_exact;
            [| apply Z.pow_nonzero; lia | apply Zpow_divide; lia].
          replace (e1 - e2) with ((e1 - e3) + (e3 - e2)) by lia.
          rewrite Z.pow_add_r by lia.
          rewrite Z.div_mul by (apply Z.pow_nonzero; lia).
          reflexivity.
    + destruct (Z.eq_dec e1 e3); subst.
      * (* e1 = e3 *)
        left; split; [lia |].
        rewrite Z.sub_diag; lia.
      * destruct (Z_lt_le_dec e1 e3).
        -- (* e1 < e3 *)
          assert (E123 : e1 < e3 <= e2) by lia; clear E12 E23 n l.
          right; split; [lia |].
          rewrite <-Z.mul_assoc.
          rewrite <-Z.pow_add_r by lia.
          replace (e2 - e3 + (e3 - e1)) with (e2 - e1) by lia.
          reflexivity.
        -- (* e3 < e1 *)
          assert (H: e3 < e1 <= e2) by lia; clear E12 E23 n l.
          left; split; [lia |].
          rewrite <-Z.mul_assoc.
          rewrite <-Z.pow_add_r by lia.
          replace (e2 - e1 + (e1 - e3)) with (e2 - e3) by lia.
          reflexivity.
    + right; split; [lia |].
      rewrite <-Z.mul_assoc.
      rewrite <-Z.pow_add_r; try lia.
      replace (e3 - e2 + (e2 - e1)) with (e3 - e1) by lia.
      reflexivity.
Qed.

Instance fp_equiv_dec : DecidableEquivalence fp_equiv.
Proof.
  unfold DecidableEquivalence, Decidable.decidable.
  intros fp1 fp2.
  unfold equiv, fp_equiv_def.
  destruct fp1 as [mp1 e1], fp2 as [mp2 e2].
  unfold FPnum, FPexp in *.
  destruct (Z_le_dec e1 e2),
           (Z_le_dec e2 e1),
           (Z.eq_dec (Z.pos mp2) (Z.pos mp1 * 2 ^ (e1 - e2))),
           (Z.eq_dec (Z.pos mp1) (Z.pos mp2 * 2 ^ (e2 - e1))).
  all: auto.
  all: right.
  all: intros C.
  all: destruct C; destruct H.
  all: auto.
Qed.
