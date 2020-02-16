Require Import ZArith Lia.
From Flocq Require Import Core Zaux.
Require Import Tactics Zaux.

(** * equality on floats without jumps to R *)
Open Scope Z.

Definition float_eqb {r : radix} (f1 f2 : float r) : bool :=
  let '(m1, e1) := (Fnum f1, Fexp f1) in
  let '(m2, e2) := (Fnum f2, Fexp f2) in
  orb
    ((e2 <=? e1) && (m2 =? m1 * r ^ (e1 - e2)))
    ((e1 <=? e2) && (m1 =? m2 * r ^ (e2 - e1))).

Lemma float_eqb_refl {r : radix} (f : float r) :
  float_eqb f f = true.
Proof.
  unfold float_eqb.
  debool. left. split.
  reflexivity.
  rewrite Z.sub_diag, Z.pow_0_r, Z.mul_1_r.
  reflexivity.
Qed.

Lemma float_eqb_sym {r : radix} (f1 f2 : float r) :
  float_eqb f1 f2 = true ->
  float_eqb f2 f1 = true.
Proof.
  unfold float_eqb.
  intros; debool; destruct H; auto.
Qed.

Lemma float_eqb_trans {r : radix} (f1 f2 f3 : float r) :
  float_eqb f1 f2 = true ->
  float_eqb f2 f3 = true ->
  float_eqb f1 f3 = true.
Proof.
  pose proof (radix_gt_1 r) as RPOS.
  destruct f1 as [m1 e1], f2 as [m2 e2], f3 as [m3 e3].
  unfold float_eqb.
  simpl; debool.
  intros EQ12 EQ23.
  destruct EQ12 as [EQ12 | EQ12]; destruct EQ23 as [EQ23 | EQ23].
  all: destruct EQ12 as [E12 M12]; destruct EQ23 as [E23 M23]; subst.
  - left; split; [lia |].
    rewrite <-Z.mul_assoc.
    rewrite <-Z.pow_add_r; try lia.
    replace (e1 - e2 + (e2 - e3)) with (e1 - e3) by lia.
    reflexivity.
  - destruct (Z.eq_dec e1 e3); subst.
    + (* e1 = e3 *)
      apply Z.mul_reg_r in M23.
      subst; left; split; [lia |].
      rewrite Z.sub_diag; lia.
      pose proof (Z.pow_pos_nonneg r (e3 - e2)).
      lia.
    + destruct (Z_lt_le_dec e1 e3).
      * (* e1 < e3 *)
        assert (E123 : e2 <= e1 < e3) by lia; clear E12 E23 n l.
        right; split; [lia |].
        apply f_equal with (f := fun x => Z.div x (r ^ (e1 - e2))) in M23.
        rewrite Z_div_mult in M23;
          [| generalize (Z.pow_pos_nonneg r (e1 - e2)); lia].
        subst.
        rewrite Z.divide_div_mul_exact;
          [| apply Z.pow_nonzero; lia | apply Zpow_divide; lia].
        replace (e3 - e2) with ((e3 - e1) + (e1 - e2)) by lia.
        rewrite Z.pow_add_r by lia.
        rewrite Z.div_mul by (apply Z.pow_nonzero; lia).
        reflexivity.
      * (* e3 < e1 *)
        assert (E123: e2 <= e3 < e1) by lia; clear E12 E23 n l.
        left; split; [lia |].
        apply f_equal with (f := fun x => Z.div x (r ^ (e3 - e2))) in M23.
        rewrite Z_div_mult in M23;
          [| generalize (Z.pow_pos_nonneg r (e3 - e2)); lia].
        subst.
        rewrite Z.divide_div_mul_exact;
          [| apply Z.pow_nonzero; lia | apply Zpow_divide; lia].
        replace (e1 - e2) with ((e1 - e3) + (e3 - e2)) by lia.
        rewrite Z.pow_add_r by lia.
        rewrite Z.div_mul by (apply Z.pow_nonzero; lia).
        reflexivity.
  - destruct (Z.eq_dec e1 e3); subst.
    + (* e1 = e3 *)
      left; split; [lia |].
      rewrite Z.sub_diag; lia.
    + destruct (Z_lt_le_dec e1 e3).
      * (* e1 < e3 *)
        assert (E123 : e1 < e3 <= e2) by lia; clear E12 E23 n l.
        right; split; [lia |].
        rewrite <-Z.mul_assoc.
        rewrite <-Z.pow_add_r by lia.
        replace (e2 - e3 + (e3 - e1)) with (e2 - e1) by lia.
        reflexivity.
      * (* e3 < e1 *)
        assert (H: e3 < e1 <= e2) by lia; clear E12 E23 n l.
        left; split; [lia |].
        rewrite <-Z.mul_assoc.
        rewrite <-Z.pow_add_r by lia.
        replace (e2 - e1 + (e1 - e3)) with (e2 - e3) by lia.
        reflexivity.
  - right; split; [lia |].
    rewrite <-Z.mul_assoc.
    rewrite <-Z.pow_add_r; try lia.
    replace (e3 - e2 + (e2 - e1)) with (e3 - e1) by lia.
    reflexivity.
Qed.
