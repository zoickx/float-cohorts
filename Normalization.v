Require Import Morphisms Coq.Floats.SpecFloat.
From FloatCohorts Require Import Option Arith FloatPair Cohorts.

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
  Hypothesis Hmax : prec < emax.
  (*
  Hypothesis prec_gt_0 : FLX.Prec_gt_0 prec.
   *)

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
                else match set_digits_m fp prec with
                     | None => None
                     | Some f2 => if andb
                                      (emin <=? FPexp f2)
                                      (FPexp f2 <=? emax - prec)
                                 then Some f2
                                 else None
                     end
    end.

  (* stolen from StructTact [https://github.com/uwplse/StructTact] *)
  Ltac break_match :=
    match goal with
      | [ H : context [ match ?X with _ => _ end ] |- _] =>
        match type of X with
          | sumbool _ _ => destruct X
          | _ => destruct X eqn:?
        end
      | [ |- context [ match ?X with _ => _ end ] ] =>
        match type of X with
          | sumbool _ _ => destruct X
          | _ => destruct X eqn:?
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

  Instance normalize_pair_proper (fp : float_pair) :
    Proper (equiv ==> equiv_if_Some) normalize_pair.
  Proof.
    intros fp1 fp2 FPE S1 S2.
    repeat rewrite normalize_pair_equiv; try assumption.
    rewrite FPE; reflexivity.
  Qed.

  Lemma normal_pair_unique (fp1 fp2 : float_pair) :
    normal_pair fp1 = true ->
    normal_pair fp2 = true ->
    fp1 === fp2 ->
    fp1 = fp2.
  Admitted.

  Theorem normalize_pair_correct (fp fp' : float_pair) :
    normalize_pair fp = Some fp'
    <->
    (fp === fp' /\ normal_pair fp' = true).
  Admitted.
 
End IEEE754_normalization.
