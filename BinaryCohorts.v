Require Import ZArith Lia.
From Flocq Require Import Core IEEE754.Binary Digits.
Require Import FloatEqb Tactics Zaux Digits.

(** * operations on binary floats which preserve their value **)
Open Scope Z.
  
Definition bfloat := float radix2.
Definition BFloat := Float radix2.

(* increase exponent by [de] *)
Definition inc_e (f : bfloat) (de : positive) : option bfloat :=
  let '(m, e) := (Fnum f, Fexp f) in
  let ddm := two_power_pos de in
  if (Zmod m ddm =? 0)
  then Some (BFloat (m / ddm) (e + Z.pos de))
  else None.

(* decrese exponent by [de] *)
Definition dec_e (f : bfloat) (de : positive) : bfloat :=
  let '(m, e) := (Fnum f, Fexp f) in
  let ddm := two_power_pos de in
  BFloat (m * ddm) (e - Z.pos de).

(* shift (up or down) exponent by [de] *)
Definition shift_e (f : bfloat) (de : Z) : option bfloat :=
  match de with
  | Z0 => Some f
  | Zpos pde => inc_e f pde
  | Zneg nde => Some (dec_e f nde)
  end.

(* set exponent to [e] *)
Definition set_e (f : bfloat) (e : Z) : option bfloat :=
  shift_e f (e - Fexp f).

(* increase binary length of mantissa by [ddm] *)
Definition inc_digits_m (f : bfloat) (ddm : positive) :=
  dec_e f ddm.

(* decrease binary length of mantissa by [ddm] *)
Definition dec_digits_m (f : bfloat) (ddm : positive) :=
  inc_e f ddm.

(* shift (up or down) binary length of mantissa by [ddm] *)
Definition shift_digits_m (f : bfloat) (ddm : Z) :=
  shift_e f (- ddm).

(* set binary length of mantissa to [dm] *)
Definition set_digits_m (f : bfloat) (dm : Z) :=
  shift_digits_m f (dm - digits2_Z (Fnum f)).


(** shifting the exponent results in a shifted exponent as expected *)

Lemma inc_e_res (f1 f2 : bfloat) (de : positive) :
  inc_e f1 de = Some f2 ->
  Fexp f2 = Fexp f1 + Z.pos de.
Proof.
  unfold inc_e.
  intro; break_match; inversion H; clear H.
  reflexivity.
Qed.

Lemma dec_e_res (f : bfloat) (de : positive) :
  Fexp (dec_e f de) = Fexp f - Z.pos de.
Proof.
  reflexivity.
Qed.

Lemma shift_e_res (f1 f2 : bfloat) (de : Z) :
  shift_e f1 de = Some f2 ->
  Fexp f2 = Fexp f1 + de.
Proof.
  unfold shift_e; intro; break_match; inversion H; clear H.
  lia.
  apply inc_e_res; assumption.
  apply dec_e_res.
Qed.

Lemma set_e_res (f1 f2 : bfloat) (e : Z) :
  set_e f1 e = Some f2 ->
  Fexp f2 = e.
Proof.
  unfold set_e.
  intro H.
  apply shift_e_res in H.
  lia.
Qed.



(** shifting the exponent preserves the float's value *)

Lemma inc_e_eq (f1 f2 : bfloat) (de : positive) :
  inc_e f1 de = Some f2 ->
  float_eqb f1 f2 = true.
Proof.
  intros.
  destruct f1 as [m1 e1], f2 as [m2 e2].
  unfold inc_e in H; break_match; inversion H; clear H.
  unfold float_eqb; debool.
  simpl in *.
  right.
  replace (e1 + Z.pos de - e1) with (Z.pos de) by lia.
  rewrite <-two_power_pos_equiv.
  remember (two_power_pos de) as rm.
  rewrite Z.mul_comm.
  rewrite <-Z_div_exact_2 with (b := rm); try auto.
  rewrite two_power_pos_equiv in Heqrm.
  assert (0 < 2 ^ Z.pos de).
  apply Z.pow_pos_nonneg.
  all: try lia.
  subst rm.
  rewrite two_power_pos_equiv.
  generalize (Z.pow_pos_nonneg 2 (Z.pos de)).
  lia.
Qed.

Lemma dec_e_eq (f : bfloat) (de : positive) :
  float_eqb f (dec_e f de) = true.
Proof.
  destruct f as [m e].
  unfold dec_e, float_eqb; debool.
  simpl.
  left.
  replace (e - (e - Z.pos de)) with (Z.pos de) by lia.
  rewrite two_power_pos_equiv.
  split.
  lia.
  reflexivity.
Qed.

Lemma shift_e_eq (f1 f2 : bfloat) (de : Z) :
  shift_e f1 de = Some f2 ->
  float_eqb f1 f2 = true.
Proof.
  destruct de; simpl.
  - intro H; inversion H; apply float_eqb_refl.
  - apply inc_e_eq.
  - intro H; inversion H; apply dec_e_eq.
Qed.

Lemma set_e_eq (f1 f2 : bfloat) (e : Z) :
  set_e f1 e = Some f2 ->
  float_eqb f1 f2 = true.
Proof.
  unfold set_e.
  apply shift_e_eq.
Qed.



(** changing the mantissa's binary length results in an expected number of digits *)

Lemma inc_digits_m_res (f : bfloat) (ddm : positive) :
  Fnum f <> 0 ->
  digits2_Z (Fnum (inc_digits_m f ddm)) = digits2_Z (Fnum f) + Z.pos ddm.
Proof.
  unfold inc_digits_m, dec_e; simpl.
  apply digits2_mul_pow2.
Qed.

Lemma dec_digits_m_res (f1 f2 : bfloat) (ddm : positive) :
  Fnum f1 <> 0 ->
  dec_digits_m f1 ddm = Some f2 ->
  digits2_Z (Fnum f2) = digits2_Z (Fnum f1) - Z.pos ddm.
Proof.
  destruct f1 as [m1 e1], f2 as [m2 e2].
  unfold dec_digits_m, inc_e.
  simpl; intros NZ H.
  break_match; inversion H; clear H.
  rewrite Z.eqb_eq in Heqb.
  apply digits2_div_pow2; assumption.
Qed.

Lemma shift_digits_m_res (f1 f2 : bfloat) (ddm : Z) :
  Fnum f1 <> 0 ->
  shift_digits_m f1 ddm = Some f2 ->
  digits2_Z (Fnum f2) = digits2_Z (Fnum f1) + ddm.
Proof.
  unfold shift_digits_m, shift_e.
  simpl; intros NZ H.
  break_match; inversion H; clear H; subst.
  - lia.
  - replace inc_e with dec_digits_m in H1 by reflexivity.
    replace ddm with (Z.neg p) by lia.
    apply dec_digits_m_res; assumption.
  - replace dec_e with inc_digits_m in Heqz by reflexivity.
    replace ddm with (Z.pos p) by lia.
    apply inc_digits_m_res; assumption.
Qed.

Lemma set_digits_m_res (f1 f2 : bfloat) (dm : Z) :
  Fnum f1 <> 0 ->
  set_digits_m f1 dm = Some f2 ->
  digits2_Z (Fnum f2) = dm.
Proof.
  intros NZ H.
  unfold set_digits_m in H.
  apply shift_digits_m_res in H; lia.
Qed.



(** changing the binary length of the mantissa preserves the float's value *)

Lemma inc_digits_m_eq (f : bfloat) (ddm : positive) :
  float_eqb f (inc_digits_m f ddm) = true.
Proof.
  unfold inc_digits_m.
  apply dec_e_eq.
Qed.

Lemma dec_digits_m_eq (f1 f2 : bfloat) (ddm : positive) :
  dec_digits_m f1 ddm = Some f2 ->
  float_eqb f1 f2 = true.
Proof.
  unfold dec_digits_m.
  apply inc_e_eq.
Qed.

Lemma shift_digits_m_eq (f1 f2 : bfloat) (ddm : Z) :
  shift_digits_m f1 ddm = Some f2 ->
  float_eqb f1 f2 = true.
Proof.
  unfold shift_digits_m.
  apply shift_e_eq.
Qed.

Lemma set_digits_m_eq (f1 f2 : bfloat) (dm : Z) :
  set_digits_m f1 dm = Some f2 ->
  float_eqb f1 f2 = true.
Proof.
  unfold set_digits_m.
  apply shift_digits_m_eq.
Qed.



(** two equal floats with the same exponent are exactly the same *)

Lemma exponent_unique_fnum (f1 f2 : bfloat) :
  float_eqb f1 f2 = true ->
  Fexp f1 = Fexp f2 ->
  Fnum f1 = Fnum f2.
Proof.
  unfold float_eqb; debool.
  destruct f1 as [m1 e1], f2 as [m2 e2].
  simpl; intros H E; destruct H; destruct H as [T H]; clear T; subst.
  all: rewrite Z.sub_diag; simpl; lia.
Qed.

Lemma exponent_unique (f1 f2 : bfloat) :
  float_eqb f1 f2 = true ->
  Fexp f1 = Fexp f2 ->
  f1 = f2.
Proof.
  intros.
  pose proof exponent_unique_fnum f1 f2 H H0.
  destruct f1, f2; simpl in *.
  subst; reflexivity.
Qed.



(** two equal floats with the same mantissa length are exactly the same *)

Lemma digits_m_unique_fexp (f1 f2 : bfloat) :
  Fnum f1 <> 0 ->
  float_eqb f1 f2 = true ->
  digits2_Z (Fnum f1) = digits2_Z (Fnum f2) ->
  Fexp f1 = Fexp f2.
Proof.
  intros NZ H.
  unfold float_eqb in *; debool.
  destruct f1 as [m1 e1], f2 as [m2 e2].
  simpl in *; intro DM.
  destruct (Z.eq_dec e1 e2); try assumption.
  destruct H as [H | H]; destruct H as [E M].
  - assert (e2 < e1) by lia; clear n.
    apply Zcompare_Gt in H.
    apply Zcompare_Gt_spec in H; destruct H as [de H].
    subst m2.
    replace (e1 - e2) with (Z.pos de) in DM by lia.
    rewrite <-two_power_pos_equiv in DM.
    rewrite digits2_mul_pow2 in DM by assumption.
    contradict DM; lia.
  - assert (e1 < e2) by lia; clear n.
    apply Zcompare_Gt in H.
    apply Zcompare_Gt_spec in H; destruct H as [de H].
    subst m1.
    replace (e2 - e1) with (Z.pos de) in DM by lia.
    rewrite <-two_power_pos_equiv in DM.
    rewrite digits2_mul_pow2 in DM.
    lia.
    intros Z; contradict NZ; subst; reflexivity.
Qed.

Lemma digits_m_unique (f1 f2 : bfloat) :
  Fnum f1 <> 0 ->
  float_eqb f1 f2 = true ->
  digits2_Z (Fnum f1) = digits2_Z (Fnum f2) ->
  f1 = f2.
Proof.
  intros.
  pose proof digits_m_unique_fexp f1 f2 H H0 H1.
  apply exponent_unique; assumption.
Qed.



(** setting exponent to that of an equal float is always possible *)
Lemma set_e_possible (f1 f2 : bfloat) :
  float_eqb f1 f2 = true ->
  set_e f1 (Fexp f2) = Some f2.
Proof.
  intro.
  destruct set_e as [f |] eqn:SE.
  - (* if successful, then equal *)
    pose proof set_e_eq f1 f (Fexp f2) SE; rename H0 into H1.
    apply set_e_res in SE.
    apply float_eqb_sym in H1.
    pose proof (float_eqb_trans f f1 f2 H1 H).
    apply (exponent_unique f f2 H0) in SE.
    subst; reflexivity.
  - (* always successful *)
    exfalso.
    unfold float_eqb, set_e, shift_e, inc_e, dec_e in *.
    destruct f1 as [m1 e1], f2 as [m2 e2]; simpl in *.
    repeat break_match; try discriminate.
    clear SE; rename Heqb into H1.
    apply Z.eqb_neq in H1.
    debool; destruct H; destruct H.
    lia.
    rewrite two_power_pos_equiv in H1.
    subst m1.
    rewrite Z.mod_mul in H1; auto.
    generalize (Z.pow_pos_nonneg 2 (Z.pos p)); lia.
Qed.

(** setting binary length of mantissa
    to that of an equal float is always possible *)
Lemma set_digits_m_possible (f1 f2 : bfloat) :
  Fnum f1 <> 0 ->
  float_eqb f1 f2 = true ->
  set_digits_m f1 (digits2_Z (Fnum f2)) = Some f2.
Proof.
  intros NZ1 H.
  destruct set_digits_m as [f |] eqn:SDM.
  - (* if successful, then equal *)
    pose proof set_digits_m_eq f1 f (digits2_Z (Fnum f2)) SDM; rename H0 into H1.
    apply set_digits_m_res in SDM; auto.
    apply digits_m_unique in SDM.
    subst; reflexivity.
    {
      destruct f1 as [m1 e1], f as [m e]; simpl.
      unfold float_eqb in *; simpl in *; debool; split_logic.
      1,2: assert (0 < 2 ^ (e1 - e)) by (apply Z.pow_pos_nonneg; lia).
      1,2: rewrite H1; apply Z.neq_mul_0; lia.
      all: intros Z; contradict NZ1.
      all: rewrite H1; subst; reflexivity.
    }
    apply float_eqb_sym in H1.
    apply float_eqb_trans with (f4 := f1); assumption.
  - (* always successful *)
    exfalso.
    unfold float_eqb, set_digits_m, shift_digits_m, shift_e, inc_e, dec_e in *.
    destruct f1 as [m1 e1], f2 as [m2 e2]; simpl in *.
    repeat break_match; try discriminate.
    clear SDM; rename Heqb into H1.
    apply Z.eqb_neq in H1.
    debool; split_logic.
    + destruct (Z.eq_dec e1 e2).
      replace (e1 - e2) with 0 in H0 by lia;
        rewrite Z.mul_1_r in H0;
        subst; lia.
      assert (e2 < e1) by lia; clear H n.
      apply Zcompare_Gt in H2.
      apply Zcompare_Gt_spec in H2; destruct H2.
      replace (e1 - e2) with (Z.pos x) in *.
      rewrite <-two_power_pos_equiv in *.
      subst m2.
      rewrite digits2_mul_pow2 in Heqz.
      lia.
      auto.
    + destruct (Z.eq_dec e1 e2).
      replace (e2 - e1) with 0 in H0 by lia;
        rewrite Z.mul_1_r in H0;
        subst; lia.
      assert (e1 < e2) by lia; clear H n.
      apply Zcompare_Gt in H2.
      apply Zcompare_Gt_spec in H2; destruct H2.
      replace (e2 - e1) with (Z.pos x) in *.
      rewrite <-two_power_pos_equiv in *.
      subst m1.
      rewrite digits2_mul_pow2 in Heqz.
      assert (x = p) by lia; subst.
      rewrite two_power_pos_equiv in H1.
      rewrite Z.mod_mul in H1; auto.
      generalize (Z.pow_pos_nonneg 2 (Z.pos p)); lia.
      intros Z; contradict NZ1; subst; reflexivity.
Qed.


(** ** declarative [set_e] *)
Theorem set_e_correct (f1 f2 : bfloat) (e : Z) :
  set_e f1 e = Some f2 <->
  float_eqb f1 f2 = true /\ Fexp f2 = e.
Proof.
  split; intro.
  - split.
    apply (set_e_eq f1 f2 e H).
    apply (set_e_res f1 f2 e H).
  - destruct H as [EQ FEXP].
    subst.
    apply set_e_possible.
    assumption.
Qed.

Corollary set_e_correct' (f1 : bfloat) (e : Z) :
  set_e f1 e = None
  <->
  forall f2, not (float_eqb f1 f2 = true /\ Fexp f2 = e).
Proof.
  split.
  - intros.
    intro SE; contradict H.
    apply set_e_correct in SE.
    congruence.
  - intros.
    destruct set_e eqn:SE; try reflexivity.
    apply set_e_correct in SE.
    specialize H with (f2 := b).
    congruence.
Qed.
  
(** ** declarative [set_digits_m] *)
Theorem set_digits_m_correct (f1 f2 : bfloat) (dm : Z) :
  Fnum f1 <> 0 ->
    set_digits_m f1 dm = Some f2 <->
    float_eqb f1 f2 = true /\ digits2_Z (Fnum f2) = dm.
Proof.
  intros NZ1.
  split; intro.
  - split.
    apply (set_digits_m_eq f1 f2 dm H).
    apply (set_digits_m_res f1 f2 dm NZ1 H).
  - destruct H as [EQ FEXP].
    subst.
    apply (set_digits_m_possible f1 f2 NZ1 EQ).
Qed.

Corollary set_digits_m_correct' (f1 : bfloat) (dm : Z) :
  Fnum f1 <> 0 ->
    set_digits_m f1 dm = None <->
    forall f2, not (float_eqb f1 f2 = true /\ digits2_Z (Fnum f2) = dm).
Proof.
  intro NZ; split.
  - intros.
    intro SDM; contradict H.
    apply set_digits_m_correct in SDM; try assumption.
    congruence.
  - intros.
    destruct set_digits_m eqn:SDM; try reflexivity.
    apply set_digits_m_correct in SDM; try assumption.
    specialize H with (f2 := b).
    congruence.
Qed.
