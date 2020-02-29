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
  
  Lemma maximize_e_proper :
    Proper (equiv ==> equiv) maximize_e.
  Proof.
    intros fp1 fp2 EQ.
    repeat rewrite maximize_e_equiv.
    assumption.
  Qed.

End natural_normalization.
