Require Import Bool.
Require Import Nat ZArith PArith NArith.

Ltac debool_logic :=
  repeat match goal with
         | [ |- context [andb _ _ = true ] ] => rewrite ->andb_true_iff
         | [ |- context [andb _ _ = false] ] => rewrite ->andb_false_iff
         | [ |- context [orb  _ _ = true ] ] => rewrite ->orb_true_iff
         | [ |- context [orb  _ _ = false] ] => rewrite ->orb_false_iff
         | [H : context [andb _ _ = true ] |- _ ] => rewrite ->andb_true_iff in H
         | [H : context [andb _ _ = false] |- _ ] => rewrite ->andb_false_iff in H
         | [H : context [orb  _ _ = true ] |- _ ] => rewrite ->orb_true_iff in H
         | [H : context [orb  _ _ = false] |- _ ] => rewrite ->orb_false_iff in H
         end.

Ltac debool_arith :=
 repeat rewrite ->Nat.eqb_eq  in *;
 repeat rewrite ->Nat.eqb_neq in *;
 repeat rewrite ->Nat.ltb_lt  in *;
 repeat rewrite ->Nat.ltb_ge  in *;
 repeat rewrite ->Nat.leb_le  in *;
 repeat rewrite ->Nat.leb_gt  in *;

 repeat rewrite ->Pos.eqb_eq  in *;
 repeat rewrite ->Pos.eqb_neq in *;
 repeat rewrite ->Pos.ltb_lt  in *;
 repeat rewrite ->Pos.ltb_ge  in *;
 repeat rewrite ->Pos.leb_le  in *;
 repeat rewrite ->Pos.leb_gt  in *;

 repeat rewrite ->N.eqb_eq  in *;
 repeat rewrite ->N.eqb_neq in *;
 repeat rewrite ->N.ltb_lt  in *;
 repeat rewrite ->N.ltb_ge  in *;
 repeat rewrite ->N.leb_le  in *;
 repeat rewrite ->N.leb_gt  in *;

 repeat rewrite ->Z.eqb_eq  in *;
 repeat rewrite ->Z.eqb_neq in *;
 repeat rewrite ->Z.ltb_lt  in *;
 repeat rewrite ->Z.ltb_ge  in *;
 repeat rewrite ->Z.leb_le  in *;
 repeat rewrite ->Z.leb_gt  in *;

 repeat rewrite ->Z.gtb_lt  in *;
 repeat rewrite ->Z.geb_le  in *.

Ltac debool :=
  debool_logic;
  debool_arith.

Ltac split_logic :=
  repeat match goal with
         | [ |- _ /\ _ ] => split
         | [ H : _ /\ _ |- _ ] => destruct H
         | [ H : _ \/ _ |- _ ] => destruct H
         end.

(*
 * Inspired by StructTact
 * Source: github.com/uwplse/StructTact
 *
 * [break_match] looks for a [match] construct in the goal or some hypothesis,
 * and destructs the discriminee, while retaining the information about
 * the discriminee's value leading to the branch being taken. 
 *)
Ltac break_match :=
  match goal with
    | [ |- context [ match ?X with _ => _ end ] ] =>
      match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
      end
    | [ H : context [ match ?X with _ => _ end ] |- _] =>
      match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
      end
  end.
