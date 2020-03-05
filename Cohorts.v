Require Import Morphisms.
From FloatCohorts Require Import Tactics Option Arith FloatPair.

Definition digits_m (fp : float_pair) : positive :=
  Pos.size (FPnum fp).

Definition dec_e (fp : float_pair) : float_pair :=
  let '(m, e) := (FPnum fp, FPexp fp) in
  FPair (m * 2) (e - 1).

Definition inc_e (fp : float_pair) : option float_pair :=
  let '(m, e) := (FPnum fp, FPexp fp) in
  match div2_opt m with
  | Some m' => Some (FPair m' (e + 1))
  | None => None
  end.

Definition dec_e_by (fp : float_pair) (de : positive) : float_pair :=
  Pos.iter dec_e fp de.

Definition inc_e_by (fp : float_pair) (de : positive) : option float_pair :=
  Pos.iter (RingMicromega.map_option inc_e) (Some fp) de.

Definition shift_e (fp : float_pair) (de : Z) : option float_pair :=
  match de with
  | 0 => Some fp
  | Z.pos d => inc_e_by fp d
  | Z.neg d => Some (dec_e_by fp d)
  end.

Definition set_e (fp : float_pair) (e : Z) : option float_pair :=
  shift_e fp (e - FPexp fp).

Lemma dec_e_equiv (fp : float_pair) :
  dec_e fp === fp.
Proof.
  destruct fp as [m e].
  cbn.
  right.
  split; [lia |].
  replace (e - (e - 1)) with 1 by lia.
  rewrite Z.pow_1_r.
  reflexivity.
Qed.

Lemma inc_e_equiv (fp : float_pair) :
  is_Some (inc_e fp) ->
  inc_e fp === Some fp.
Proof.
  intros.
  destruct fp as [m e].
  cbn in *.
  destruct div2_opt as [d|] eqn:D in H;
    inversion H; clear H.
  subst.
  rewrite D.
  constructor.
  left.
  cbn.
  split; [lia |].
  replace (e + 1 - e) with 1 by lia.
  rewrite Z.pow_1_r.
  apply div2_opt_correct in D.
  rewrite D.
  reflexivity.
Qed.

Lemma dec_e_by_equiv (fp : float_pair) (de : positive) :
  dec_e_by fp de === fp.
Proof.
  unfold dec_e_by.
  apply Pos.iter_invariant; [| reflexivity].
  intros.
  rewrite <-H.
  apply dec_e_equiv.
Qed.

Lemma inc_e_by_equiv (fp : float_pair) (de : positive) :
  is_Some (inc_e_by fp de) ->
  inc_e_by fp de === Some fp.
Proof.
  unfold inc_e_by.
  apply Pos.iter_invariant; [| reflexivity].
  intros.
  destruct x; [| inversion H0].
  unfold RingMicromega.map_option in *.
  apply inc_e_equiv in H0.
  rewrite H0.
  apply H.
  constructor.
Qed.

Lemma shift_e_equiv (fp : float_pair) (de : Z) :
  is_Some (shift_e fp de) ->
  shift_e fp de === Some fp.
Proof.
  unfold shift_e.
  intros.
  destruct de.
  - reflexivity.
  - apply inc_e_by_equiv. assumption.
  - rewrite dec_e_by_equiv. reflexivity.
Qed.

Lemma set_e_equiv (fp : float_pair) (e : Z) :
  is_Some (set_e fp e) ->
  set_e fp e === Some fp.
Proof.
  apply shift_e_equiv.
Qed.



Definition inc_digits_m := dec_e.

Definition dec_digits_m := inc_e.

Definition inc_digits_m_by := dec_e_by.

Definition dec_digits_m_by := inc_e_by.

Definition shift_digits_m (fp : float_pair) (ddm : Z) : option float_pair :=
  shift_e fp (- ddm).

Definition set_digits_m (fp : float_pair) (dm : positive) :=
  shift_digits_m fp (Z.pos dm - Z.pos (digits_m fp)).

Lemma inc_digits_m_equiv (fp : float_pair) :
  inc_digits_m fp === fp.
Proof. apply dec_e_equiv. Qed.

Lemma dec_digits_m_equiv (fp : float_pair) :
  is_Some (dec_digits_m fp) ->
  dec_digits_m fp === Some fp.
Proof. apply inc_e_equiv. Qed.

Lemma inc_digits_m_by_equiv (fp : float_pair) (ddm : positive) :
  inc_digits_m_by fp ddm === fp.
Proof. apply dec_e_by_equiv. Qed.

Lemma dec_digits_m_by_equiv (fp : float_pair) (ddm : positive) :
  is_Some (dec_digits_m_by fp ddm) ->
  dec_digits_m_by fp ddm === Some fp.
Proof. apply inc_e_by_equiv. Qed.

Lemma shift_digits_m_equiv (fp : float_pair) (ddm : Z) :
  is_Some (shift_digits_m fp ddm) ->
  shift_digits_m fp ddm === Some fp.
Proof. apply shift_e_equiv. Qed.

Lemma set_digits_m_equiv (fp : float_pair) (dm : positive) :
  is_Some (set_digits_m fp dm) ->
  set_digits_m fp dm === Some fp.
Proof. apply shift_e_equiv. Qed.





Lemma exponent_unique (fp1 fp2 : float_pair) :
  FPexp fp1 = FPexp fp2 ->
  fp1 === fp2 ->
  fp1 = fp2.
Proof.
  destruct fp1 as [m1 e1], fp2 as [m2 e2].
  cbn.
  intros H E.
  subst.
  rewrite Z.sub_diag in *.
  cbn in *.
  repeat rewrite Pos.mul_1_r in *.
  destruct E as [[H1 H2] | [H1 H2]].
  all: inversion H2; subst; reflexivity.
Qed.

Lemma digits_m_unique (fp1 fp2 : float_pair) :
  digits_m fp1 = digits_m fp2 ->
  fp1 === fp2 ->
  fp1 = fp2.
Proof.
  intros.
  destruct (Z.eq_dec (FPexp fp1) (FPexp fp2)) as [| NE];
    [apply exponent_unique; assumption |].
  destruct fp1 as [m1 e1], fp2 as [m2 e2].
  cbn in *.
  destruct H0 as [[E M] | [E M]].
  -
    remember (e1 - e2) as ed.
    destruct ed; try lia.
    replace e1 with (e2 + Z.pos p) in * by lia.
    clear Heqed E NE.

    break_match; inversion M; clear M.
    rewrite <-Pos2Z.inj_pow in Heqz.
    inversion Heqz; clear Heqz.
    rewrite <-H2 in H1.
    rewrite H1 in H.
    rewrite pos_size_mul_pow_two in H.
    lia.
  -
    remember (e2 - e1) as ed.
    destruct ed; try lia.
    replace e2 with (e1 + Z.pos p) in * by lia.
    clear Heqed E NE.
    
    break_match; inversion M; clear M.
    rewrite <-Pos2Z.inj_pow in Heqz.
    inversion Heqz; clear Heqz.
    rewrite <-H2 in H1.
    rewrite H1 in H.
    rewrite pos_size_mul_pow_two in H.
    lia.
Qed.

Lemma mantissa_unique (fp1 fp2 : float_pair) :
  FPnum fp1 = FPnum fp2 ->
  fp1 === fp2 ->
  fp1 = fp2.
Proof.
  intros.
  apply digits_m_unique.
  unfold digits_m.
  rewrite H; reflexivity.
  assumption.
Qed.

Lemma equiv_neq_m (fp1 fp2 : float_pair) :
  fp1 === fp2 ->
  (FPnum fp1 < FPnum fp2)%positive ->
  FPexp fp1 > FPexp fp2.
Proof.
  intros.
  destruct fp1 as (m1, e1), fp2 as (m2, e2).
  cbn in *.
  destruct H as [[E M] | [E M]].
  -
    break_match; inversion M.
    destruct (e1 - e2) eqn:A; lia.
  -
    exfalso.
    break_match; try lia.
    inversion M.
    rewrite H1 in H0.
    clear - H0.
    induction p; lia.
Qed.

Lemma equiv_neq_e (fp1 fp2 : float_pair) :
  fp1 === fp2 ->
  FPexp fp1 < FPexp fp2 ->
  (FPnum fp1 > FPnum fp2)%positive.
Proof.
  intros.
  destruct fp1 as (m1, e1), fp2 as (m2, e2).
  cbn in *.
  destruct H as [[E M] | [E M]].
  -
    break_match; inversion M.
    destruct (e1 - e2) eqn:A; lia.
  -
    break_match; inversion M.
    enough (1 < 2 ^ (e2 - e1)) by nia.
    destruct (e2 - e1) eqn:A; try lia.
    clear.
    rename p0 into p.
    rewrite <-(Z.pow_1_l (Z.pos p)) by lia.
    apply Z.pow_lt_mono_l; lia.
Qed.

Lemma equiv_neq_m_digits (fp1 fp2 : float_pair) :
  fp1 === fp2 ->
  (digits_m fp1 < digits_m fp2)%positive ->
  FPexp fp1 > FPexp fp2.
Proof.
  intros.
  apply pos_size_monotone_inv in H0.
  apply equiv_neq_m; assumption.
Qed.

Lemma equiv_neq_e_digits (fp1 fp2 : float_pair) :
  fp1 === fp2 ->
  FPexp fp1 < FPexp fp2 ->
  (digits_m fp1 > digits_m fp2)%positive.
Proof.
  intros.
  destruct (Pos.eq_dec (digits_m fp1) (digits_m fp2))
    as [EQ | NEQ].
  -
    exfalso.
    apply digits_m_unique in EQ; [| assumption].
    subst.
    lia.
  -
    apply equiv_neq_e in H0; [| assumption].
    apply Pos.gt_lt, Pos.lt_le_incl in H0.
    apply pos_size_monotone in H0.
    unfold digits_m in *.
    lia.
Qed.



Lemma inc_e_res (fp : float_pair) :
  forall fp',
    inc_e fp = Some fp' ->
    FPexp fp' = FPexp fp + 1.
Proof.
  intros.
  unfold inc_e in H.
  break_match; inversion H.
  cbn.
  reflexivity.
Qed.

Lemma dec_e_res (fp : float_pair) :
  FPexp (dec_e fp) = FPexp fp - 1.
Proof.
  reflexivity.
Qed.

Lemma inc_e_by_res (fp : float_pair) (de : positive) :
  forall fp',
    inc_e_by fp de = Some fp' ->
    FPexp fp' = FPexp fp + Z.pos de.
Proof.
  unfold inc_e_by.
  induction de using Pos.peano_ind.
  -
    apply inc_e_res.
  -
    intros.
    rewrite Pos.iter_succ in H.
    destruct (Pos.iter (RingMicromega.map_option inc_e) (Some fp) de);
      try discriminate.
    cbn in H.
    break_match; inversion H.

    assert (T : Some f = Some f) by reflexivity.
    specialize (IHde f T).
    cbn in *; lia.
Qed.

Lemma dec_e_by_res (fp : float_pair) (de : positive) :
  FPexp (dec_e_by fp de) = FPexp fp - Z.pos de.
Proof.
  unfold dec_e_by.
  induction de using Pos.peano_ind.
  -
    apply dec_e_res.
  -
    rewrite Pos.iter_succ.
    rewrite dec_e_res.
    lia.
Qed.

Lemma shift_e_res (fp : float_pair) (de : Z) :
  forall fp',
    shift_e fp de = Some fp' ->
    FPexp fp' = FPexp fp + de.
Proof.
  intros.
  destruct de; cbn in *.
  -
    inversion H.
    lia.
  -
    apply inc_e_by_res.
    assumption.
  -
    inversion H.
    rewrite dec_e_by_res.
    lia.
Qed.
        
Lemma set_e_res (fp : float_pair) (e : Z) :
  forall fp',
    set_e fp e = Some fp' ->
    FPexp fp' = e.
Proof.
  intros.
  unfold set_e in H.
  apply shift_e_res in H.
  lia.
Qed.

Open Scope positive_scope.

Lemma inc_digits_m_res (fp : float_pair) :
  digits_m (inc_digits_m fp) = digits_m fp + 1.
Proof.
  unfold inc_digits_m, dec_e.
  cbn.
  replace 2 with (2 ^ 1) by reflexivity.
  rewrite pos_size_mul_pow_two.
  reflexivity.
Qed.

Lemma dec_digits_m_res (fp : float_pair) :
  forall fp',
    dec_digits_m fp = Some fp' ->
    digits_m fp' + 1 = digits_m fp.
Proof.
  unfold dec_digits_m, inc_e.
  intros.
  break_match; inversion H.
  apply div2_opt_correct in Heqo.
  cbn.
  unfold digits_m.
  rewrite Heqo.
  replace 2 with (2 ^ 1) by reflexivity.
  rewrite pos_size_mul_pow_two.
  lia.
Qed.

Lemma inc_digits_m_by_res (fp : float_pair) (ddm : positive) :
  digits_m (inc_digits_m_by fp ddm) = digits_m fp + ddm.
Proof.
  unfold inc_digits_m_by, dec_e_by.
  fold inc_digits_m.

  induction ddm using Pos.peano_ind.
  -
    apply inc_digits_m_res.
  -
    rewrite Pos.iter_succ.
    rewrite inc_digits_m_res.
    lia.
Qed.

Lemma dec_digits_m_by_res (fp : float_pair) (ddm : positive) :
  forall fp',
    dec_digits_m_by fp ddm = Some fp' ->
    digits_m fp' + ddm = digits_m fp.
Proof.
  unfold dec_digits_m_by, inc_e_by.
  fold dec_digits_m.
  induction ddm using Pos.peano_ind.
  -
    intros.
    cbn in *.
    break_match; inversion H.
    apply div2_opt_correct in Heqo.
    unfold digits_m.
    rewrite Heqo.
    replace 2 with (2 ^ 1) by reflexivity.
    rewrite pos_size_mul_pow_two.
    cbn.
    lia.
  -
    intros.
    rewrite Pos.iter_succ in H.
    destruct (Pos.iter (RingMicromega.map_option dec_digits_m) (Some fp) ddm);
      try discriminate.
    cbn in H.
    break_match; inversion H; clear H H1.

    assert (T : Some f = Some f) by reflexivity.
    specialize (IHddm f T); clear T.
    unfold digits_m in *.
    cbn in *.
    apply div2_opt_correct in Heqo.
    rewrite Heqo in IHddm.
    replace 2 with (2 ^ 1) in IHddm by reflexivity.
    rewrite pos_size_mul_pow_two in IHddm.
    lia.
Qed.

Lemma shift_digits_m_res (fp : float_pair) (ddm : Z) :
  forall fp',
    shift_digits_m fp ddm = Some fp' ->
    Z.pos (digits_m fp') = (Z.pos (digits_m fp) + ddm)%Z.
Proof.
  intros.
  destruct ddm; cbn in *.
  -
    congruence.
  -
    fold inc_digits_m_by in H.
    inversion H.
    rewrite inc_digits_m_by_res.
    lia.
  -
    fold dec_digits_m_by in H.
    apply dec_digits_m_by_res in H.
    rewrite <-Pos2Z.add_pos_neg.
    lia.
Qed.

Lemma set_digits_m_res (fp : float_pair) (dm : positive) :
  forall fp',
    set_digits_m fp dm = Some fp' ->
    digits_m fp' = dm.
Proof.
  intros.
  apply shift_digits_m_res in H.
  lia.
Qed.

Close Scope positive_scope.

Lemma dec_e_exact (fp fp' : float_pair) :
  fp' === fp ->
  FPexp fp' = FPexp fp - 1 ->
  dec_e fp = fp'.
Proof.
  intros.
  cbn.
  apply exponent_unique; [cbn; congruence |].
  rewrite H.
  apply dec_e_equiv.
Qed.

Lemma inc_e_exact (fp fp' : float_pair) :
  fp' === fp ->
  FPexp fp' = FPexp fp + 1 ->
  inc_e fp = Some fp'.
Proof.
  intros.
  cbn.
  break_match.
  +
    f_equal.
    apply exponent_unique.
    cbn; congruence.
    rewrite H.

    destruct fp as [m e].
    cbn.
    left.
    split; [lia |].
    replace (e + 1 - e) with 1 by lia.
    rewrite Z.pow_1_r.
    cbn in Heqo.
    apply div2_opt_correct in Heqo.
    congruence.
  +
    exfalso.
    cbn in H.
    destruct H; try lia.
    rewrite H0 in H.
    replace (FPexp fp + 1 - FPexp fp) with 1 in H by lia.
    cbn in H.
    destruct H.
    inversion H1.
    rewrite H3 in Heqo.
    clear - Heqo.
    rewrite Pos.mul_xO_r in Heqo.
    cbn in Heqo.
    discriminate.
Qed.

Lemma dec_e_by_exact (fp fp' : float_pair) (de : positive) :
  fp' === fp ->
  FPexp fp' = FPexp fp - Z.pos de ->
  dec_e_by fp de = fp'.
Proof.
  (* induction is not actually needed here *)
  (* this is just the fastest way to destruct [de] as [1] or [Pos.succ] *)
  induction de using Pos.peano_ind.
  -
    apply dec_e_exact.
  -
    intros.
    unfold dec_e_by.
    rewrite Pos.iter_succ.
    apply dec_e_exact.
    rewrite H.
    symmetry.
    apply dec_e_by_equiv.
    rewrite dec_e_by_res.
    lia.
Qed.

Lemma inc_e_by_exact (fp fp' : float_pair) (de : positive) :
  fp' === fp ->
  FPexp fp' = FPexp fp + Z.pos de ->
  inc_e_by fp de = Some fp'.
Proof.
  generalize dependent fp'.
  induction de using Pos.peano_ind.
  -
    apply inc_e_exact.
  -
    intros.
    unfold inc_e_by.
    rewrite Pos.iter_succ.
    replace (Pos.iter (RingMicromega.map_option inc_e) (Some fp) de)
      with (inc_e_by fp de)
      by reflexivity.
    erewrite (IHde (dec_e fp')).
    apply inc_e_exact.
    symmetry; apply dec_e_equiv.
    rewrite dec_e_res; lia.
    rewrite <-H; apply dec_e_equiv.
    rewrite dec_e_res; lia.
Qed.

Lemma shift_e_exact (fp fp' : float_pair) (de : Z) :
  fp' === fp ->
  FPexp fp' = FPexp fp + de ->
  shift_e fp de = Some fp'.
Proof.
  destruct de.
  -
    intros.
    cbn.
    f_equal.
    apply exponent_unique.
    lia.
    symmetry; assumption.
  -
    apply inc_e_by_exact.
  -
    intros.
    cbn.
    f_equal.
    apply dec_e_by_exact; assumption.
Qed.

Lemma set_e_exact (fp fp' : float_pair) (e : Z) :
  fp' === fp ->
  FPexp fp' = e ->
  set_e fp e = Some fp'.
Proof.
  intros.
  unfold set_e.
  erewrite shift_e_exact.
  reflexivity.
  assumption.
  lia.
Qed.

Open Scope positive_scope.

Lemma inc_digits_m_exact (fp fp' : float_pair) :
  fp' === fp ->
  digits_m fp' = digits_m fp + 1 ->
  inc_digits_m fp = fp'.
Proof.
  intros.
  apply digits_m_unique.
  rewrite inc_digits_m_res.
  lia.
  rewrite H.
  apply inc_digits_m_equiv.
Qed.

Lemma dec_digits_m_exact (fp fp' : float_pair) :
  fp' === fp ->
  digits_m fp' + 1 = digits_m fp ->
  dec_digits_m fp = Some fp'.
Proof.
  intros.
  unfold dec_digits_m, inc_e.
  break_match.
  -
    f_equal.
    apply digits_m_unique.
    cbn.
    apply div2_opt_correct in Heqo.
    unfold digits_m in *.
    rewrite Heqo in H0.
    replace 2 with (2 ^ 1) in H0 by reflexivity.
    rewrite pos_size_mul_pow_two in H0.
    lia.

    rewrite H; clear H H0.
    destruct fp as [m e].
    cbn.
    left.
    split; [lia |].
    replace (e + 1 - e)%Z with 1%Z by lia.
    rewrite Z.pow_1_r.
    cbn in Heqo.
    apply div2_opt_correct in Heqo.
    congruence.
  -
    symmetry in H0.
    apply inc_digits_m_exact in H0; [| symmetry; assumption].
    unfold inc_digits_m in H0.
    destruct fp as (m, e).
    cbn in H0, Heqo.
    inversion H0; subst.
    unfold div2_opt in Heqo.
    rewrite Pos.mul_xO_r in Heqo.
    discriminate.
Qed.

Lemma inc_digits_m_by_exact (fp fp' : float_pair) (ddm : positive) :
  fp' === fp ->
  digits_m fp' = digits_m fp + ddm ->
  inc_digits_m_by fp ddm = fp'.
Proof.
  induction ddm using Pos.peano_ind.
  -
    apply inc_digits_m_exact.
  -
    intros.
    unfold inc_digits_m_by, dec_e_by.
    rewrite Pos.iter_succ.
    fold inc_digits_m.
    apply inc_digits_m_exact.
    rewrite H.
    symmetry.
    apply inc_digits_m_by_equiv.
    rewrite inc_digits_m_by_res.
    lia.
Qed.

Lemma dec_digits_m_by_exact (fp fp' : float_pair) (ddm : positive) :
  fp' === fp ->
  digits_m fp' + ddm = digits_m fp ->
  dec_digits_m_by fp ddm = Some fp'.
Proof.
  generalize dependent fp'.
  induction ddm using Pos.peano_ind.
  -
    apply dec_digits_m_exact.
  -
    intros.
    unfold dec_digits_m_by, inc_e_by.
    rewrite Pos.iter_succ.
    replace (Pos.iter (RingMicromega.map_option inc_e) (Some fp) ddm)
      with (dec_digits_m_by fp ddm)
      by reflexivity.
    erewrite (IHddm (inc_digits_m fp')).
    apply dec_digits_m_exact.
    symmetry; apply inc_digits_m_equiv.
    rewrite inc_digits_m_res; lia.
    rewrite <-H; apply inc_digits_m_equiv.
    rewrite inc_digits_m_res; lia.
Qed.

Lemma shift_digits_m_exact (fp fp' : float_pair) (ddm : Z) :
  fp' === fp ->
  (Z.pos (digits_m fp') = Z.pos (digits_m fp) + ddm)%Z ->
  shift_digits_m fp ddm = Some fp'.
Proof.
  intros.
  destruct ddm.
  -
    cbn.
    f_equal.
    apply digits_m_unique.
    lia.
    symmetry; assumption.
  -
    cbn.
    f_equal.
    apply inc_digits_m_by_exact.
    assumption.
    lia.
  -
    apply dec_digits_m_by_exact.
    assumption.
    lia.
Qed.

Lemma set_digits_m_exact (fp fp' : float_pair) (dm : positive) :
  fp' === fp ->
  digits_m fp' = dm ->
  set_digits_m fp dm = Some fp'.
Proof.
  intros.
  apply shift_digits_m_exact.
  assumption.
  lia.
Qed.
