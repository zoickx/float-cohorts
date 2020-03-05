Require Import Morphisms Coq.Floats.SpecFloat.
From FloatCohorts Require Import Option Arith FloatPair Cohorts Tactics.

Open Scope Z.

Section natural_normalization.
  
  Fixpoint maximize_e' (m : positive) (e : Z) {struct m} : (positive * Z) :=
    match m with
    | (m'~0)%positive => maximize_e' m' (e + 1)
    | _ => (m, e)
    end.
  
  (** maximize exponent [same as] minimize mantissa [same as] make mantissa odd **)
  Definition maximize_e (fp : float_pair) :=
    let '(m, e) := (FPnum fp, FPexp fp) in
    let '(m', e') := maximize_e' m e in
    FPair m' e'.
  
  Lemma maximize_e_is_inc_e_by (fp : float_pair) :
    maximize_e fp = fp \/ exists de, inc_e_by fp de = Some (maximize_e fp).
  Proof.
    destruct fp as (m, e).
    generalize dependent e.
    induction m; auto.
    intros.
    right.
    specialize (IHm (e + 1)).
    destruct IHm.
    -
      exists 1%positive.
      cbn in *.
      congruence.
    -
      destruct H as [de H].
      exists (de + 1)%positive.
      cbn in *.
      rewrite <-H.
      clear.
      unfold inc_e_by.
      rewrite Pos.iter_add.
      reflexivity.
  Qed.
  
  Lemma maximize_e_equiv (fp : float_pair) :
    maximize_e fp === fp.
  Proof.
    pose proof maximize_e_is_inc_e_by fp.
    destruct H.
    rewrite H; reflexivity.
    destruct H.
    enough (T : Some (maximize_e fp) === Some fp)
      by (inversion T; congruence).
    rewrite <-H.
    apply inc_e_by_equiv.
    rewrite H.
    constructor.
  Qed.
  
  Instance maximize_e_proper :
    Proper (equiv ==> equiv) maximize_e.
  Proof.
    intros fp1 fp2 EQ.
    repeat rewrite maximize_e_equiv.
    assumption.
  Qed.

End natural_normalization.

Section IEEE754_normalization.

  Variable prec emax : Z.
  Let emin := emin emax prec.
  Hypothesis prec_gt_0 : 0 < prec.
  Hypothesis Hmax : prec < emax.

  Definition normal_pair (fp : float_pair) :=
    let '(m, e) := (FPnum fp, FPexp fp) in
    bounded prec emax m e.

  Lemma bounded_arithmetic (m : positive) (e : Z) :
      bounded prec emax m e = true
      <->
      (Z.pos (Pos.size m) < prec /\ e = emin) \/
      (Z.pos (Pos.size m) = prec /\ emin <= e <= emax - prec).
  Proof.
    intros.
    unfold bounded, canonical_mantissa, fexp, emin, SpecFloat.emin.
    destruct (Z_lt_le_dec (Z.pos (digits2_pos m) + e - prec)
                               (3 - emax - prec)).
    all: try rewrite Z.max_r in * by lia.
    all: try rewrite Z.max_l in * by lia.
    all: split; intros.
    all: rewrite Bool.andb_true_iff in *.
    all: rewrite <-Zeq_is_eq_bool in *.
    all: replace (digits2_pos m) with (Pos.size m) in * by reflexivity.
    all: rewrite Z.leb_le in *.
    all: lia.
  Qed.

  (** ** normalization *)
  (* first try to satisfy the left side of [bounded_arithmetic],
     then try the right side if that doesn't work *)
  Definition normalize_pair (fp : float_pair)
    : option float_pair :=
    match set_e fp emin with
    | None => None
    | Some f1 => if Z.pos (Pos.size (FPnum f1)) <=? prec
                then Some f1
                else match set_digits_m fp (Z.to_pos prec) with
                     | None => None
                     | Some f2 => if andb
                                      (emin <=? FPexp f2)
                                      (FPexp f2 <=? emax - prec)
                                 then Some f2
                                 else None
                     end
    end.

  Lemma normalize_pair_equiv (fp : float_pair) :
    is_Some (normalize_pair fp) ->
    normalize_pair fp === Some fp.
  Proof.
    unfold normalize_pair.
    intros.
    repeat break_match; try (inversion H; fail).
    -
      rewrite <-Heqo.
      apply set_e_equiv.
      rewrite Heqo; constructor.
    -
      rewrite <-Heqo0.
      apply set_digits_m_equiv.
      rewrite Heqo0; constructor.
  Qed.

  Lemma normal_pair_unique (fp1 fp2 : float_pair) :
    normal_pair fp1 = true ->
    normal_pair fp2 = true ->
    fp1 === fp2 ->
    fp1 = fp2.
  Proof.
    intros.
    destruct fp1 as (m1, e1), fp2 as (m2, e2).
    unfold normal_pair in *.
    rewrite bounded_arithmetic in *.
    cbn in H, H0.
    destruct H as [[M1 E1] | [M1 E1]],
             H0 as [[M2 E2] | [M2 E2]].
    -
      apply exponent_unique; try assumption.
      subst; reflexivity.
    -
      subst.
      apply equiv_neq_m_digits in H1; [| cbn; lia].
      cbn in *; lia.
    -
      subst.
      symmetry in H1.
      apply equiv_neq_m_digits in H1; [| cbn; lia].
      cbn in *; lia.
    -
      apply digits_m_unique; try assumption.
      cbn.
      congruence.
  Qed.

  Lemma normalize_pair_normal (fp : float_pair) :
    forall fp', normalize_pair fp = Some fp' ->
    normal_pair fp' = true.
  Proof.
    intros.
    unfold normal_pair.
    apply bounded_arithmetic.
    unfold normalize_pair in H.
    repeat break_match; inversion H; subst; clear H.
    -
      apply Z.leb_le in Heqb.
      apply set_e_res in Heqo.
      rewrite Heqo; clear Heqo.
      unfold emin, SpecFloat.emin.
      lia.
    -
      clear Heqo Heqb.
      apply andb_prop in Heqb0.
      destruct Heqb0.
      rewrite Z.leb_le in *.
      apply set_digits_m_res in Heqo0.
      unfold digits_m in Heqo0.
      rewrite Heqo0; clear Heqo0.
      unfold emin, SpecFloat.emin in *.
      rewrite Z2Pos.id by assumption.
      lia.
  Qed.
    
  Theorem normalize_pair_None_inv (fp : float_pair) :
    normalize_pair fp = None
    ->
    forall fp', fp' === fp -> normal_pair fp' = false.
  Proof.
    intros.
    destruct (normal_pair fp') eqn:NP'; [| reflexivity].
    exfalso.
    unfold normal_pair in NP'.
    apply bounded_arithmetic in NP'.
    unfold normalize_pair in H.
    repeat break_match; inversion_clear H.
    -
      rewrite Bool.andb_false_iff in *.
      apply set_e_spec in Heqo; destruct Heqo.
      apply set_digits_m_spec in Heqo0; destruct Heqo0.

      (* cleanup *)
      replace (Pos.size (FPnum f))
        with (digits_m f)
        in *
        by reflexivity. (* poor man's fold 1 *)
      replace (Pos.size (FPnum fp'))
        with (digits_m fp')
        in *
        by reflexivity. (* poor man's fold 2 *)
      rename f into f1, f0 into f2, fp' into f.
      assert (EQ1 : f === f1) by (rewrite H, H0; reflexivity).
      assert (EQ2 : f === f2) by (rewrite H0, H2; reflexivity).
      clear H H2 H0 fp.
      move f before f1; move f2 before f1.
      rename H1 into E1, Heqb into M1, H3 into M2.
      
      destruct Heqb0 as [E2 | E2]; rewrite Z.leb_gt in *.
      +
        destruct NP' as [[M E] | [M E]].
        *
          clear - EQ1 M1 E1 M E.
          enough (FPexp f > FPexp f1) by lia.
          eapply equiv_neq_m_digits.
          assumption.
          lia.
        *
          clear - EQ2 M2 E2 M E.
          enough (digits_m f2 > digits_m f)%positive
            by (rewrite <-M, Pos2Z.id in M2; lia).
          eapply equiv_neq_e_digits.
          symmetry; assumption.
          lia.
      +
        destruct NP' as [[M E] | [M E]].
        *
          clear - EQ1 M1 E1 M E.
          enough (FPexp f > FPexp f1) by lia.
          eapply equiv_neq_m_digits.
          assumption.
          lia.
        *
          clear - EQ2 M2 E2 M E.
          enough (digits_m f > digits_m f2)%positive
            by (rewrite <-M, Pos2Z.id in M2; lia).
          eapply equiv_neq_e_digits.
          assumption.
          lia.
    -
      rewrite Z.leb_gt in *.
      apply set_e_spec in Heqo; destruct Heqo.
      apply set_digits_m_None_inv with (fp':=fp') in Heqo0; [ |assumption].
      unfold digits_m in *.
      destruct NP' as [[M E] | [M E]].
      +
        replace fp' with f in *.
        lia.
        apply exponent_unique.
        lia.
        rewrite H, H0; reflexivity.
      +
        rewrite <-M in Heqo0.
        rewrite Pos2Z.id in Heqo0.
        lia.
    -
      apply set_e_None_inv with (fp':=fp') in Heqo;
        [lia | assumption].
  Qed.

  Theorem normalize_pair_spec (fp nfp : float_pair) :
    normalize_pair fp = Some nfp
    <->
    (fp === nfp /\ normal_pair nfp = true).
  Proof.
    split; intros.
    -
      split.
      +
        assert (SN : is_Some (normalize_pair fp)) by (rewrite H; constructor).
        apply normalize_pair_equiv in SN.
        rewrite H in SN.
        inversion SN.
        symmetry; assumption.
      +
        eapply normalize_pair_normal.
        eassumption.
    -
      destruct H as [EQ N].
      destruct normalize_pair eqn:NP.
      +
        assert (SN : is_Some (normalize_pair fp)) by (rewrite NP; constructor).
        apply normalize_pair_equiv in SN.
        rewrite NP in SN.
        apply normalize_pair_normal in NP.
        f_equal.
        apply normal_pair_unique.
        assumption.
        assumption.
        rewrite <-EQ.
        inversion SN.
        assumption.
      +
        exfalso.
        apply normalize_pair_None_inv with (fp':=nfp) in NP.
        congruence.
        symmetry; assumption.
  Qed.
  
End IEEE754_normalization.

