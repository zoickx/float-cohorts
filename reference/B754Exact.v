Require Import ZArith Lia.
From Flocq Require Import Core IEEE754.Binary Digits.
Require Import BinaryCohorts Digits FloatEqb Tactics.

Open Scope Z.

(** * normalizing an arbitrary float *)

Section float_normalization.

  Variable prec emax : Z.
  Hypothesis prec_gt_0 : FLX.Prec_gt_0 prec.
  Hypothesis Hmax : prec < emax.
  
  (* can [f] be represented in IEEE754 format given by [prec] [emax] *)
  Definition valid_float (f : bfloat) :=
    match (Fnum f) with
    | Z0 => true
    | Z.pos m => bounded prec emax m (Fexp f)
    | Z.neg m => bounded prec emax m (Fexp f)
    end.
  
  (** ** normalization *)
  Definition normalize_float (f : bfloat)
    : option bfloat :=
    let emin := 3 - emax - prec in
    match set_e f emin with
      | None => None
      | Some f1 => if digits2_Z (Fnum f1) <=? prec
                   then Some f1
                   else match set_digits_m f prec with
                       | None => None
                       | Some f2 => if andb
                                         (emin <=? Fexp f2)
                                         (Fexp f2 <=? emax - prec)
                                    then Some f2
                                    else None
                       end
    end.

  (* [valid_float] unfolded to basic arithmetic statements *)
  Lemma valid_float_arithmetic (f : bfloat) :
    let emin := 3 - emax - prec in
    let '(m, e) := (Fnum f, Fexp f) in
      valid_float f = true
      <->
      m = 0 \/
      (digits2_Z m < prec /\ e = emin) \/
      (digits2_Z m = prec /\ emin <= e <= emax - prec).
  Proof.
    intros.
    unfold Prec_gt_0 in *.
    subst emin.
    destruct f as [m e].
    unfold valid_float, bounded, canonical_mantissa, FLT.FLT_exp in *.
    unfold Fexp, Fnum in *.
    break_match; [split; auto | |]; debool.
    all: try rewrite ->digits2_Z_Zdigits by discriminate.
    all: try rewrite ->Zpos_digits2_pos.
    all: destruct (Z_lt_le_dec (Zdigits radix2 (Zpos p) + e - prec)
                               (3 - emax - prec)).
    all: try rewrite Z.max_r in * by lia.
    all: try rewrite Z.max_l in * by lia.
    all: split; intros.
    all: rewrite <-Zeq_is_eq_bool in *.
    all: unfold Zdigits in *.
    all: lia.
  Qed.

  Lemma zero_eq (f1 f2 : bfloat) :
    Fnum f1 = 0 ->
    float_eqb f1 f2 = true ->
    Fnum f2 = 0.
  Proof.
    unfold float_eqb; debool.
    destruct f1 as [m1 e1], f2 as [m2 e2]; simpl.
    intros Z1 H.
    destruct H; destruct H as [H1 H2]; subst.
    - reflexivity.
    - assert (0 < 2 ^ (e2 - e1)) by (apply Z.pow_pos_nonneg; lia).
      nia.
  Qed.

  Lemma not_zero_eq (f1 f2 : bfloat) :
    Fnum f1 <> 0 ->
    float_eqb f1 f2 = true ->
    Fnum f2 <> 0.
  Proof.
    unfold float_eqb; debool.
    destruct f1 as [m1 e1], f2 as [m2 e2]; simpl.
    intros NZ1 H.
    destruct H; destruct H as [H1 H2]; subst.
    - assert (0 < 2 ^ (e1 - e2)) by (apply Z.pow_pos_nonneg; lia).
      apply Z.neq_mul_0.
      lia.
    - intros H; contradict NZ1.
      subst; reflexivity.
  Qed.

  (* normalization does not change the float's value *)
  Lemma normalize_eq (f nf : bfloat) :
    normalize_float f = Some nf ->
    float_eqb f nf = true.
  Proof.
    intros.
    unfold normalize_float in H.
    repeat break_match; inversion H; subst.
    apply set_e_eq with (e := 3 - emax - prec).
    assumption.
    apply set_digits_m_eq with (dm := prec).
    assumption.
  Qed.
 
  (* normalization can only result in a valid float *)
  Lemma normalize_valid(f nf : bfloat) :
    normalize_float f = Some nf ->
    valid_float nf = true.
  Proof.
    intros H.
    unfold Prec_gt_0 in *.
    destruct (Z.eq_dec (Fnum f) 0) as [Z | NZ].
    - pose proof normalize_eq f nf H.
      apply zero_eq with (f2 := nf) in Z.
      unfold valid_float; rewrite Z; reflexivity.
      assumption.
    - unfold normalize_float in H.
      repeat break_match; inversion H; clear H; subst.
      + rewrite set_e_correct in Heqo; destruct Heqo as [EQ FEXP].
        apply valid_float_arithmetic; try assumption.
        debool; lia.
      + rewrite set_digits_m_correct in Heqo0 by assumption;
          destruct Heqo0 as [EQ FNUM].
        apply valid_float_arithmetic; try assumption.
        debool; lia.
  Qed.

  (* two equal valid floats are exactly the same *)
  Lemma valid_unique (nf nf' : bfloat) :
    Fnum nf <> 0 ->
      valid_float nf = true -> valid_float nf' = true ->
      float_eqb nf nf' = true -> nf = nf'.
  Proof.
    intros NZ V V' EQ; pose proof (not_zero_eq nf nf' NZ EQ) as NZ'.
    unfold Prec_gt_0 in *.
    apply valid_float_arithmetic in V; try assumption.
    apply valid_float_arithmetic in V'; try assumption.
    destruct nf as [m e], nf' as [m' e'];
      unfold Fnum, Fexp in *.
    destruct (Z.eq_dec e e');
      [apply exponent_unique; assumption |].
    destruct (Z.eq_dec (digits2_Z m) (digits2_Z m'));
      [apply digits_m_unique; assumption |].
    split_logic;
      try (assert (e < e') by lia);
      try (assert (e' < e) by lia);
      try lia.
    all: unfold float_eqb in *; debool.
    all: unfold Fnum, Fexp in *.
    all: split_logic; try lia.
    all: apply Zcompare_Gt in H4;
           apply Zcompare_Gt_spec in H4;
           destruct H4 as [de H4].
    - contradict H; rewrite <-H1; subst m'.
      replace (e - e') with (Z.pos de) by lia.
      simpl.
      rewrite <-two_power_pos_correct, digits2_mul_pow2; lia.
    - contradict H2; rewrite <-H; subst m.
      replace (e' - e) with (Z.pos de) by lia.
      simpl.
      rewrite <-two_power_pos_correct, digits2_mul_pow2; lia.
  Qed.

  (* if normalization does not succeed,
     no equal normal float exists *)
  Lemma normalize_impossible (f f' : bfloat) :
    normalize_float f = None ->
    float_eqb f f' = true -> valid_float f' = false.
  Proof.
    intros N EQ.
    destruct (Z.eq_dec (Fnum f) 0) as [Z | NZ].
    {
      exfalso.
      unfold Prec_gt_0 in *.
      clear f' EQ Hmax.
      unfold normalize_float in N.
      repeat break_match; try discriminate; clear N; debool.
      - apply set_e_correct in Heqo.
        destruct Heqo.
        apply zero_eq in H; try assumption.
        rewrite H in Heqb0; cbn in Heqb0.
        lia.
      - apply set_e_correct in Heqo.
        destruct Heqo.
        apply zero_eq in H; try assumption.
        rewrite H in Heqb0; cbn in Heqb0.
        lia.
      - unfold set_e, shift_e, inc_e, dec_e in Heqo.
        repeat break_match; try discriminate; debool.
        rewrite Z in Heqb.
        cbn in Heqb.
        congruence.
    }
    apply Bool.not_true_iff_false; intros V'.
    apply valid_float_arithmetic in V'; try assumption.
    split_logic;
      [apply not_zero_eq in EQ; congruence | |].
    - unfold normalize_float in N.
      repeat break_match; try discriminate; clear N; debool.
      all: replace (set_e f (3 - emax - prec))
             with (Some f')
             in *
             by (symmetry; apply set_e_correct; split; assumption).
      all: inversion Heqo; subst.
      all: lia.
    - unfold normalize_float in N;
        repeat break_match; try discriminate;
        clear N; debool.
      + rewrite <-H in Heqo0.
        replace (set_digits_m f (digits2_Z (Fnum f')))
             with (Some f')
             in *
             by (symmetry; apply set_digits_m_correct; auto).
        inversion Heqo0; subst.
        lia.
      + rewrite <-H in Heqo0.
        replace (set_digits_m f (digits2_Z (Fnum f')))
             with (Some f')
             in *
             by (symmetry; apply set_digits_m_correct; auto).
        inversion Heqo0.
      + unfold set_e, shift_e, inc_e, dec_e in Heqo.
        repeat break_match; try discriminate; clear Heqo; debool.
        unfold float_eqb in EQ; debool.
        split_logic.
        lia.
        rewrite H3 in Heqb.
        replace (Fexp f' - Fexp f)
          with (Fexp f' - 3 + emax + prec + Z.pos p)
          in Heqb
          by lia.
        rewrite Z.pow_add_r in Heqb; try lia.
        replace (radix2 ^ Z.pos p)
          with (two_power_pos p)
          in *
          by (rewrite two_power_pos_equiv; reflexivity).
        rewrite Z.mul_assoc in Heqb.
        rewrite Z.mod_mul in Heqb.
        auto.
        rewrite two_power_pos_equiv;
          generalize (Z.pow_pos_nonneg 2 (Z.pos p)); lia.
  Qed.

  (** ** declarative [normalize_float *)
  Theorem normalize_correct (f nf : bfloat) :
    Fnum f <> 0 ->
      normalize_float f = Some nf <->
      (float_eqb f nf = true) /\ (valid_float nf = true).
  Proof.
    intro NZ.
    split.
    - intros; split.
      apply normalize_eq; assumption.
      apply (normalize_valid f); assumption.
    - intros T; destruct T as [EQ V].
      destruct normalize_float as [nf' |] eqn:NF'.
      + assert (EQ' : float_eqb f nf' = true)
          by (apply normalize_eq; assumption).
        assert (V' : valid_float nf' = true)
          by (apply normalize_valid with (f := f); assumption).
        f_equal.
        apply valid_unique; try assumption.
        apply not_zero_eq with (f1 := f); assumption.
        apply float_eqb_trans with (f2 := f);
          [apply float_eqb_sym; assumption | assumption].
      + exfalso.
        apply normalize_impossible with (f' := nf) in NF'; try assumption.
        congruence.
  Qed.

  Corollary normalize_correct' (f : bfloat) :
    Fnum f <> 0 ->
      normalize_float f = None
      <->
      forall nf, not ((float_eqb f nf = true) /\ (valid_float nf = true)).
  Proof.
    intro NZ; split.
    - intros.
      intro NF; contradict H.
      apply normalize_correct in NF; try assumption.
      congruence.
    - intros.
      destruct normalize_float eqn:NF; try reflexivity.
      apply normalize_correct in NF; try assumption.
      specialize H with (nf := b).
      congruence.
  Qed.

  (** ** conversion from an arbitrary float to a valid B754-formated one *)
  Definition B754_of_bfloat (f : bfloat) : option (binary_float prec emax).
    destruct (Z.eq_dec (Fnum f) 0); [exact None |].
    destruct (normalize_float f) as [nf |] eqn:NF; [| exact None].
    apply normalize_correct in NF; [destruct NF | assumption].

    destruct (Fnum nf) eqn:MNF.
    - apply not_zero_eq in H; congruence.
    - unfold valid_float in H0.
      rewrite MNF in H0.
      exact (Some (B754_finite prec emax false p (Fexp nf) H0)).
    - unfold valid_float in H0.
      rewrite MNF in H0.
      exact (Some (B754_finite prec emax true p (Fexp nf) H0)).
  Defined.

End float_normalization.
