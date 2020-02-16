Require Import Relations Classes.EquivDec Morphisms.

Inductive option_equiv {A : Type} {EqA : relation A} `{Equivalence A EqA}
  : relation (option A) :=
| equiv_Some : forall a1 a2, a1 === a2 -> option_equiv (Some a1) (Some a2)
| equiv_None : option_equiv None None.

Instance option_Equivalence {A : Type} {EqA : relation A} `{Equivalence A EqA} :
  Equivalence option_equiv.
Proof.
  constructor.
  -
    intros oa.
    destruct oa.
    constructor; reflexivity.
    constructor.
  -
    intros oa ob AB.
    destruct oa, ob; try inversion AB; try constructor.
    rewrite H2.
    reflexivity.
  -
    intros oa ob oc AB BC.
    destruct oa, ob, oc; try inversion AB; try inversion BC; try constructor.
    rewrite H2, H5.
    reflexivity.
Qed.

Instance Some_proper {A : Type} {EqA : relation A} `{Equivalence A EqA} :
  Proper (equiv ==> equiv) (@Some A).
Proof.
  intros a b E.
  constructor.
  assumption.
Qed.

Lemma Some_equiv_inv {A : Type} {EqA : relation A} `{Equivalence A EqA}
      (oa ob : A) :
  Some oa === Some ob -> oa === ob.
Proof.
  intros E.
  inversion E.
  assumption.
Qed.

Inductive is_Some {A : Type} : (option A) -> Prop :=
| is_Some_intro : forall a, is_Some (Some a).

Inductive is_None {A : Type} : (option A) -> Prop :=
| is_None_intro : is_None None.

Lemma not_Some_is_None {A : Type} (oa : option A) :
  ~ (is_Some oa) <-> is_None oa.
Proof.
  split; intros; destruct oa.
  contradict H; constructor.
  constructor.
  inversion H.
  intros C; inversion C.
Qed.

Lemma not_None_is_Some {A : Type} (oa : option A) :
  ~ (is_None oa) <-> is_Some oa.
Proof.
  split; intros; destruct oa.
  constructor.
  contradict H; constructor.
  intros C; inversion C.
  inversion H.
Qed.
