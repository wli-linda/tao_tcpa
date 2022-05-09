(* isomorphism.v *)

(* ********** *)

Require Import Arith.

(* ********** *)

(* Tao's representation: *)

Inductive int : Type :=
| Int : nat -> nat -> int.

Notation "a -- b" := (Int a b) (at level 70, no associativity).

(* Signed integer representation: *)

Inductive sint : Type :=
| P : nat -> sint
| Z : sint
| N : nat -> sint.

(* ********** *)

(* Tao's integer equality: *)

Definition int_eq (x y : int) : Prop :=
  match x, y with
  | (a -- b), (c -- d) =>
    a + d = c + b
  end.

Definition int_eqb (x y : int) : bool :=
  match x, y with
  | (a -- b), (c -- d) =>
    a + d =? c + b
  end.

Definition test_int_of_sint (int_of_sint : sint -> int) : bool :=
  (int_eqb (int_of_sint Z) (0 -- 0))
    && (int_eqb (int_of_sint Z) (3 -- 3))
    && (int_eqb (int_of_sint Z) (9 -- 9))
    && (int_eqb (int_of_sint (P 0)) (1 -- 0))
    && (int_eqb (int_of_sint (P 15)) (16 -- 0))
    && (int_eqb (int_of_sint (P 4)) (7 -- 2))
    && (int_eqb (int_of_sint (P 7)) (20 -- 12))
    && (int_eqb (int_of_sint (N 0)) (0 -- 1))
    && (int_eqb (int_of_sint (N 6)) (0 -- 7))
    && (int_eqb (int_of_sint (N 9)) (6 -- 16))
    && (int_eqb (int_of_sint (N 13)) (14 -- 28)).

Definition int_of_sint (x : sint) :=
  match x with
  | P px =>
    (px + 1 -- 0)
  | Z => (0 -- 0)
  | N nx =>
    (0 -- nx + 1)
  end.

Compute (test_int_of_sint int_of_sint).

(* ********** *)

(* Signed integer equality: *)

Definition sint_eq (i1 i2 : sint) : Prop :=
  match i1 with
  | P n1 =>
    match i2 with
    | P n2 =>
      n1 = n2
    | Z =>
      False
    | N n2 =>
      False
    end
  | Z =>
    match i2 with
    | P n2 =>
      False
    | Z =>
      True
    | N n2 =>
      False
    end
  | N n1 =>
    match i2 with
    | P n2 =>
      False
    | Z =>
      False
    | N n2 =>
      n1 = n2
    end
  end.

Definition sint_eqb (i1 i2 : sint) : bool :=
  match i1 with
  | P n1 =>
    match i2 with
    | P n2 =>
      n1 =? n2
    | Z =>
      false
    | N n2 =>
      false
    end
  | Z =>
    match i2 with
    | P n2 =>
      false
    | Z =>
      true
    | N n2 =>
      false
    end
  | N n1 =>
    match i2 with
    | P n2 =>
      false
    | Z =>
      false
    | N n2 =>
      n1 =? n2
    end
  end.

Definition test_sint_of_int (sint_of_int : int -> sint) : bool :=
  (sint_eqb (sint_of_int (0 -- 0)) Z)
    && (sint_eqb (sint_of_int (7 -- 7)) Z)
    && (sint_eqb (sint_of_int (9 -- 8)) (P 0))
    && (sint_eqb (sint_of_int (8 -- 9)) (N 0))
    && (sint_eqb (sint_of_int (13 -- 2)) (P 10))
    && (sint_eqb (sint_of_int (9 -- 15)) (N 5)).

Definition sint_of_int (x : int) :=
  match x with
  | (a -- b) =>
    if a =? b
    then Z
    else if a <? b
         then N (b - a - 1)
         else P (a - b - 1)
  end.

Compute (test_sint_of_int sint_of_int).

(* ********** *)

Proposition int_of_sint_and_back :
  forall x : sint,
    sint_eq x (sint_of_int (int_of_sint x)).
Proof.
  intros [px |  | nx];
    unfold int_of_sint, sint_of_int, sint_eq.
  - Search (0 < S _).
    assert (H_lt := Nat.lt_0_succ px).
    case (px + 1 =? 0) as [ | ] eqn:H_eqb.
    + assert (H_eq := beq_nat_true (px + 1) 0 H_eqb).
      rewrite -> Nat.add_1_r in H_eq.
      Search (_ < _ -> _ <> _).
      contradiction (lt_0_neq (S px) H_lt (eq_sym H_eq)).
    + case (px + 1 <? 0) as [ | ] eqn:H_ltb.
      -- Search (_ < _ -> _).
         assert (H_nlt := Nat.lt_asymm 0 (S px) H_lt).
         unfold not in H_nlt.
         destruct (Nat.ltb_lt (px + 1) 0) as [H_ltb_lt _].
         assert (H_lt_absurd := H_ltb_lt H_ltb);
           clear H_ltb_lt.
         rewrite -> Nat.add_1_r in H_lt_absurd.
         contradiction (H_nlt H_lt_absurd).
      -- Search (_ - 0).
         rewrite -> Nat.sub_0_r.
         Search (_ + _ - _).
         rewrite -> Nat.add_sub.
         reflexivity.
  - Search (Nat.eqb).
    rewrite -> (Nat.eqb_refl 0).
    exact I.
  - Search (0 < S _).
    assert (H_lt := Nat.lt_0_succ nx).
    case (0 =? nx + 1) as [ | ] eqn:H_eqb.
    + assert (H_eq := beq_nat_true 0 (nx + 1) H_eqb).
      rewrite -> Nat.add_1_r in H_eq.
      contradiction (lt_0_neq (S nx) H_lt H_eq).
    + case (0 <? nx + 1) as [ | ] eqn:H_ltb.
      -- rewrite -> Nat.sub_0_r.
         rewrite -> Nat.add_sub.
         reflexivity.
      -- Search (_ <? _).
         destruct (Nat.ltb_nlt 0 (nx + 1)) as [H_ltb_nlt _].
         assert (H_nlt := H_ltb_nlt H_ltb);
           clear H_ltb_nlt.
         rewrite -> Nat.add_1_r in H_nlt.
         unfold not in H_nlt.
         contradiction (H_nlt H_lt).
Qed.
         
Proposition sint_of_int_and_back :
  forall x : int,
    int_eq x (int_of_sint (sint_of_int x)).
Proof.
  intros [a b].
  unfold sint_of_int.
  case (a =? b) as [ | ] eqn:H_eqb;
    unfold int_of_sint, int_eq.
  - rewrite -> Nat.add_0_r.
    rewrite -> Nat.add_0_l.
    exact (beq_nat_true a b H_eqb).
  - case (a <? b) as [ | ] eqn:H_ltb.
    + destruct (Nat.ltb_lt a b) as [H_ltb_lt _].
      assert (H_lt := H_ltb_lt H_ltb);
        clear H_ltb_lt; clear H_ltb.
      Search (_ - _ + _).
      Check (Nat.sub_add 1 (b - a)).
      Search (_ < _ - _).
      destruct (Nat.lt_add_lt_sub_r 0 b a) as [H_lt_add_sub _].
      rewrite <- (Nat.add_0_l a) in H_lt.
      assert (H_lt_sub := H_lt_add_sub H_lt);
        clear H_lt_add_sub.
      Search (_ < _ -> _ <= _).
      assert (H_le_S := lt_le_S 0 (b - a) H_lt_sub).
      rewrite -> (Nat.sub_add 1 (b - a) H_le_S).
      Search (_ + _ - _).
      rewrite -> Nat.add_0_l in H_lt.
      rewrite -> (Nat.add_sub_assoc
                    a b a (Nat.lt_le_incl a b H_lt)).
      rewrite -> minus_plus.
      rewrite -> Nat.add_0_l.
      reflexivity.
    + destruct (Nat.ltb_ge a b) as [H_ltb_ge _].
      assert (H_ge := H_ltb_ge H_ltb);
        clear H_ltb_ge.
      assert (H_neq := beq_nat_false a b H_eqb).
      Search ( _ <= _ /\ _ <> _).
      destruct (Nat.le_neq b a) as [_ H_le_neq].
      assert (H_gt := H_le_neq (conj H_ge (Nat.neq_sym a b H_neq)));
        clear H_le_neq.
      destruct (Nat.lt_add_lt_sub_r 0 a b) as [H_lt_add_sub _].
      rewrite <- Nat.add_0_l in H_gt at 1.
      assert (H_gt_sub := H_lt_add_sub H_gt);
        clear H_lt_add_sub.
      assert (H_ge_S := lt_le_S 0 (a - b) H_gt_sub);
        clear H_gt_sub.
      rewrite -> (Nat.sub_add 1 (a - b) H_ge_S).
      rewrite -> Nat.add_0_l in H_gt.
      rewrite -> (Nat.sub_add b a H_ge).
      rewrite -> Nat.add_0_r.
      reflexivity.
Qed.

(* ********** *)

(* end of isomorphism.v *)
