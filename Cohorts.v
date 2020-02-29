Require Import Morphisms.
From FloatCohorts Require Import Option Arith FloatPair.

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

Instance dec_e_proper :
  Proper (equiv ==> equiv) dec_e.
Proof.
  intros fp1 fp2 EQ.
  destruct fp1 as [m1 e1], fp2 as [m2 e2].
  cbn in *.
  destruct EQ as [EQ | EQ]; destruct EQ as [E M].
  -
    left.
    split; [lia |].
    replace (e1 - 1 - (e2 - 1)) with (e1 - e2) by lia.
    destruct (2 ^ (e1 - e2)).
    all: lia.
  -
    right.
    split; [lia |].
    replace (e2 - 1 - (e1 - 1)) with (e2 - e1) by lia.
    destruct (2 ^ (e2 - e1)).
    all: lia.
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

Instance inc_e_proper_if_Some :
  Proper (equiv ==> equiv_if_Some) inc_e.
Proof.
  intros fp1 fp2 EQ S1 S2.
  destruct fp1 as [m1 e1], fp2 as [m2 e2].
  destruct EQ as [EQ | EQ]; destruct EQ as [E M].
  -
    cbn in *.
    destruct (div2_opt m1) as [hm1|] eqn:HM1,
             (div2_opt m2) as [hm2|] eqn:HM2.
    all: try apply div2_opt_correct in HM1.
    all: try apply div2_opt_correct in HM2.
    all: subst; cbn in *.
    all: try inversion S1.
    all: try inversion S2.
    constructor.
    left.
    cbn.
    split; [lia |].
    replace (e1 + 1 - (e2 + 1)) with (e1 - e2) by lia.
    destruct (2 ^ (e1 - e2)).
    all: lia.
  -
    cbn in *.
    destruct (div2_opt m1) as [hm1|] eqn:HM1,
             (div2_opt m2) as [hm2|] eqn:HM2.
    all: try apply div2_opt_correct in HM1.
    all: try apply div2_opt_correct in HM2.
    all: subst; cbn in *.
    all: try inversion S1.
    all: try inversion S2.
    constructor.
    right.
    cbn.
    split; [lia |].
    replace (e2 + 1 - (e1 + 1)) with (e2 - e1) by lia.
    destruct (2 ^ (e2 - e1)).
    all: lia.
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

Instance dec_e_by_proper :
  Proper (equiv ==> (fun _ _ => True) ==> equiv) dec_e_by.
Proof.
  intros fp1 fp2 FE d1 d2 DE.
  repeat rewrite dec_e_by_equiv.
  assumption.
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

Instance inc_e_by_proper_if_some :
  Proper (equiv ==> equiv ==> equiv_if_Some) inc_e_by.
Proof.
  intros fp1 fp2 FPE de1 de2 DEE S1 S2.
  repeat rewrite inc_e_by_equiv; try assumption.
  rewrite FPE.
  reflexivity.
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

Instance shift_e_proper_if_Some :
  Proper (equiv ==> equiv ==> equiv_if_Some) shift_e.
Proof.
  intros fp1 fp2 FPE de1 de2 DEE S1 S2.
  repeat rewrite shift_e_equiv; try assumption.
  rewrite FPE.
  reflexivity.
Qed.

Lemma set_e_equiv (fp : float_pair) (e : Z) :
  is_Some (set_e fp e) ->
  set_e fp e === Some fp.
Proof.
  apply shift_e_equiv.
Qed.

Instance set_e_proper_if_Some :
  Proper (equiv ==> equiv ==> equiv_if_Some) set_e.
Proof.
  intros fp1 fp2 FPE de1 de2 DEE S1 S2.
  repeat rewrite set_e_equiv; try assumption.
  rewrite FPE.
  reflexivity.
Qed.



Definition inc_digits_m := dec_e.

Definition dec_digits_m := inc_e.

Definition inc_digits_m_by := dec_e_by.

Definition dec_digits_m_by := inc_e_by.

Definition shift_digits_m (fp : float_pair) (ddm : Z) : option float_pair :=
  shift_e fp (- ddm).

Definition set_digits_m (fp : float_pair) (dm : Z) :=
  shift_digits_m fp (dm - Z.pos (Pos.size (FPnum fp))).

Lemma inc_digits_m_equiv (fp : float_pair) :
  inc_digits_m fp === fp.
Proof. apply dec_e_equiv. Qed.

Lemma inc_digits_m_proper :
  Proper (equiv ==> equiv) inc_digits_m.
Proof. apply dec_e_proper. Qed.

Lemma dec_digits_m_equiv (fp : float_pair) :
  is_Some (dec_digits_m fp) ->
  dec_digits_m fp === Some fp.
Proof. apply inc_e_equiv. Qed.

Instance dec_digits_m_proper_if_Some :
  Proper (equiv ==> equiv_if_Some) dec_digits_m.
Proof. apply inc_e_proper_if_Some. Qed.

Lemma inc_digits_m_by_equiv (fp : float_pair) (ddm : positive) :
  inc_digits_m_by fp ddm === fp.
Proof. apply dec_e_by_equiv. Qed.

Lemma inc_digits_m_by_proper :
  Proper (equiv ==> (fun _ _ => True) ==> equiv) inc_digits_m_by.
Proof. apply dec_e_by_proper. Qed.

Lemma dec_digits_m_by_equiv (fp : float_pair) (ddm : positive) :
  is_Some (dec_digits_m_by fp ddm) ->
  dec_digits_m_by fp ddm === Some fp.
Proof. apply inc_e_by_equiv. Qed.

Instance dec_digits_m_by_proper_if_some :
  Proper (equiv ==> equiv ==> equiv_if_Some) dec_digits_m_by.
Proof. apply inc_e_by_proper_if_some. Qed.

Lemma shift_digits_m_equiv (fp : float_pair) (ddm : Z) :
  is_Some (shift_digits_m fp ddm) ->
  shift_digits_m fp ddm === Some fp.
Proof. apply shift_e_equiv. Qed.

Instance shift_digits_m_proper_if_Some :
  Proper (equiv ==> equiv ==> equiv_if_Some) shift_digits_m.
Proof.
  intros fp1 fp2 FE ddm1 ddm2 DE.
  apply shift_e_proper_if_Some.
  assumption.
  inversion DE; reflexivity.
Qed.
Lemma set_digits_m_equiv (fp : float_pair) (dm : Z) :
  is_Some (set_digits_m fp dm) ->
  set_digits_m fp dm === Some fp.
Proof. apply shift_e_equiv. Qed.

Instance set_digits_m_proper_if_Some :
  Proper (equiv ==> equiv ==> equiv_if_Some) set_digits_m.
Proof.
  intros fp1 fp2 FE dm1 dm2 DE S1 S2.
  unfold set_digits_m.
  repeat rewrite shift_digits_m_equiv; try assumption.
  rewrite FE; reflexivity.
Qed.
