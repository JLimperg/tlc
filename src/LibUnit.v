(**************************************************************************
* Product of Data Structures                                              *
**************************************************************************)

Set Implicit Arguments.
Require Import LibTactics LibLogic LibReflect.


(* ********************************************************************** *)
(** * Inhabited  *)

Instance unit_inhab : Inhab unit.
Proof using. intros. apply (prove_Inhab tt). Qed.


(* ********************************************************************** *)
(** * Comparable *)

Global Instance unit_comparable : Comparable unit.
Proof using.
  apply make_comparable. intros x y. destruct x, y.
  apply decidable_make with (decide := true). rewrite eqb_eq; reflexivity.
Qed.


(* ********************************************************************** *)
(** * Structure *)

Lemma unit_unique : forall tt1 tt2 : unit,
  tt1 = tt2.
Proof using. intros. destruct tt1. destruct~ tt2. Qed.