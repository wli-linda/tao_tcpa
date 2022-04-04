(* integers.v *)
(* http://www.math.ucla.edu/~tao/resource/general/131ah.1.03w/week1.pdf *)

(* ********** *)

Require Import Arith.

(* ********** *)

Inductive int : Type :=
  | Int : nat -> nat -> int.

Notation "a -- b" := (Int a b) (at level 70, no associativity).

(* ********** *)

Definition int_eq (x y : int) : Prop :=
  match x, y with
    | (a -- b), (c -- d) => a + d = c + b
  end.

Notation "x == y" := (int_eq x y) (at level 70, no associativity).

Proposition int_eq_refl :
  forall x : int,
    x == x.
Proof.
  intro x.
  destruct x as [a b].

  Restart.

  intros [a b].
  unfold int_eq.
  reflexivity.
Qed.

Proposition int_eq_sym :
  forall x y : int,
    x == y -> y == x.
Proof.
  intros [a b] [c d].
  unfold int_eq.
  intro H_eq.
  Check (eq_sym).
  Check (eq_sym H_eq).
  exact (eq_sym H_eq).
Qed.

Proposition int_eq_trans :
  forall x y z : int,
    x == y -> y == z -> x == z.
Proof.
  intros [a b] [c d] [e f].
  unfold int_eq.
  intros H_xy H_yz.
  Check (eq_trans).
  Check (plus_reg_l (a + f) (e + b) (d + c)).
  apply (plus_reg_l (a + f) (e + b) (d + c)).
  Search (_ + (_ + _)).
  rewrite <- (Nat.add_assoc d c (e + b)).
  rewrite -> (plus_permute c e b).
  rewrite <- H_xy.
  Search (_ + (_ + _)).
  rewrite <- (Nat.add_assoc d c (a + f)).
  rewrite -> (plus_permute c a f).
  rewrite -> H_yz.
  rewrite -> (plus_permute a e d).
  reflexivity.
Qed.

(* ********** *)

Definition int_plus (x y : int) : int :=
  match x, y with
  | (a -- b), (c -- d) =>
    (a + c) -- (b + d)
  end.

Lemma int_plus_eq_l :
  forall x x' y : int,
    x == x' ->
    int_plus x y == int_plus x' y.
Proof.
  intros [a b] [a' b'] [c d]. 
  unfold int_eq, int_plus.
  intro H_eqx.
  Search (_ + _ = _ + _).
  Check (Nat.add_shuffle1 a c b' d).
  rewrite -> (Nat.add_shuffle1 a c b' d).
  rewrite -> (Nat.add_shuffle1 a' c b d).
  rewrite -> H_eqx.
  reflexivity.
Qed.

Corollary int_plus_eq_r :
  forall y x x' : int,
    x == x' ->
    int_plus y x == int_plus y x'.
Proof.
  intros [c d] [a b] [a' b']. 
  unfold int_eq, int_plus.
  intro H_eqx.
  Search (_ + _ = _ + _).
  Check (Nat.add_shuffle1 c a d b').
  rewrite -> (Nat.add_shuffle1 c a d b').
  rewrite -> (Nat.add_shuffle1 c a' d b).
  rewrite -> H_eqx.
  reflexivity.
Qed.

(* ********** *)

Definition int_mult (x y : int) : int :=
  match x, y with
  | (a -- b), (c -- d) =>
    (a * c + b * d) -- (a * d + b * c)
  end.

Lemma int_mult_eq_l :
  forall x x' y : int,
    x == x' ->
    int_mult x y == int_mult x' y.
Proof.
  intros [a b] [a' b'] [c d].
  unfold int_eq, int_mult.
  intro H_eqx.
  rewrite -> (Nat.add_shuffle2 (a * c) (b * d) (a' * d) (b' * c)).
  rewrite -> (Nat.add_shuffle2 (a' * c) (b' * d) (a * d) (b * c)).
  Search (_ * _ + _ * _).
  Check (Nat.mul_add_distr_r a b' c).
  rewrite <- (Nat.mul_add_distr_r a b' c).
  rewrite <- (Nat.mul_add_distr_r a' b c).
  rewrite <- (Nat.mul_add_distr_r b a' d).
  rewrite <- (Nat.mul_add_distr_r b' a d).
  rewrite -> (Nat.add_comm b a').
  rewrite -> (Nat.add_comm b' a).
  rewrite -> H_eqx.
  reflexivity.
Qed.

Corollary int_mult_eq_r :
  forall y x x' : int,
    x == x' ->
    int_mult y x == int_mult y x'.
Proof.
  intros [c d][a b] [a' b'].
  unfold int_eq, int_mult.
  intro H_eqx.
  rewrite -> (Nat.add_shuffle1 (c * a) (d * b) (c * b') (d * a')).
  rewrite -> (Nat.add_shuffle1 (c * a') (d * b') (c * b) (d * a)).
  Search (_ * _ + _ * _).
  Check (Nat.mul_add_distr_l c a b').
  rewrite <- (Nat.mul_add_distr_l c a b').
  rewrite <- (Nat.mul_add_distr_l c a' b).
  rewrite <- (Nat.mul_add_distr_l d b a').
  rewrite <- (Nat.mul_add_distr_l d b' a).
  rewrite -> (Nat.add_comm b a').
  rewrite -> (Nat.add_comm b' a).
  rewrite -> H_eqx.
  reflexivity.
Qed.

(* ********** *)

Lemma int_lt_trichotomy :
  forall x : int,
  exists n : nat,
    x == (0 -- 0) \/
    x == (S n -- 0) \/
    x == (0 -- S n).
Proof.
  intros [[ | a'] [ | b']].
  - exists 0.
    left.
    Check (int_eq_refl (0 -- 0)).
    exact (int_eq_refl (0 -- 0)).

  - exists b'.
    right.
    right.
    exact (int_eq_refl (0 -- S b')).

  - exists a'.
    right.
    left.
    exact (int_eq_refl (S a' -- 0)).

  - Check (Nat.lt_trichotomy (S a') (S b')).
    destruct (Nat.lt_trichotomy (S a') (S b')) as [lt | [eq | gt]].

    + exists (b' - S a'). 
      right.
      right.
      unfold int_eq.
      rewrite -> (Nat.add_0_l).
      Check (plus_n_Sm).
      rewrite <- (plus_n_Sm).
      Check (f_equal).
      apply (f_equal S).
      Search (_ + (_ - _) = _).
      Check (le_plus_minus_r (S a') b').
      apply (le_plus_minus_r (S a') b').
      Search (_ < _ -> _ <= _).
      Check (lt_n_Sm_le (S a') b' lt).
      exact (lt_n_Sm_le (S a') b' lt).

    + exists 0.
      left.
      rewrite -> eq.
      unfold int_eq.
      apply Nat.add_comm.

    + exists (a' - S b').
      right.
      left.
      unfold int_eq.
      rewrite -> Nat.add_0_r.
      rewrite -> (plus_Sn_m).
      apply f_equal.
      Search (_ - _ + _).
      Check (Nat.sub_add (S b') a').
      symmetry.
      apply (Nat.sub_add (S b') a').
      exact (lt_n_Sm_le (S b') a' gt).
Qed.


(* ********** *)

Lemma int_plus_commutative :
  forall x y : int,
    int_plus x y == int_plus y x.
Proof. 
  - intros [a b] [c d].
    unfold int_eq, int_plus.
    rewrite -> (Nat.add_comm a c).
    rewrite -> (Nat.add_comm b d).
    reflexivity. 
Qed.

Lemma int_plus_associative :
  forall x y z : int,
    int_plus (int_plus x y) z == int_plus x (int_plus y z).
Proof.
  intros [a b] [c d] [e f].
  unfold int_eq, int_plus.
  rewrite -> (Nat.add_assoc b d f).
  rewrite -> (Nat.add_assoc a c e).
  reflexivity. 
Qed.

Lemma int_plus_0_r :
  forall x : int,
    int_plus x (0 -- 0) == x.
Proof.
  intros [a b].
  unfold int_eq, int_plus.
  rewrite -> Nat.add_0_r.
  rewrite -> Nat.add_0_r.
  reflexivity.
Qed.

Lemma int_plus_0_l :
  forall x : int,
    int_plus (0 -- 0) x == x.
Proof.
  (* Method 1: meta-level *)
  intros [a b].
  unfold int_eq, int_plus. 
  rewrite -> Nat.add_0_l.
  rewrite -> Nat.add_0_l.
  reflexivity.

  (* Method 2: object-level *)
  Restart.
  intro x.
  Check (int_eq_trans (int_plus (0 -- 0) x) (int_plus x (0 -- 0)) x
                      (int_plus_commutative (0 -- 0) x)
                      (int_plus_0_r x)).
  exact (int_eq_trans (int_plus (0 -- 0) x) (int_plus x (0 -- 0)) x
                      (int_plus_commutative (0 -- 0) x)
                      (int_plus_0_r x)).
Qed.

(* ********** *)

Definition int_neg (x : int) : int :=
  match x with
  | (a -- b) => (b -- a)
  end.

Lemma int_plus_neg_of_itself_l :
  forall x : int,
    int_plus x (int_neg x) == (0 -- 0).
Proof.
  intros [a b].
  unfold int_eq, int_plus, int_neg. 
  rewrite -> Nat.add_comm.
  rewrite -> Nat.add_0_l.
  rewrite -> Nat.add_0_l.
  rewrite -> Nat.add_comm.
  reflexivity.
Qed.

Lemma int_plus_neg_of_itself_r :
  forall x : int,
    int_plus (int_neg x) x == (0 -- 0).
Proof.
  intro x.
  Check (int_eq_trans (int_plus (int_neg x) x) (int_plus x (int_neg x)) (0 -- 0)
                      (int_eq_sym (int_plus x (int_neg x))
                                  (int_plus (int_neg x) x)
                                  (int_plus_commutative x (int_neg x)))
                      (int_plus_neg_of_itself_l x)).
  exact (int_eq_trans (int_plus (int_neg x) x) (int_plus x (int_neg x)) (0 -- 0)
                      (int_eq_sym (int_plus x (int_neg x))
                                  (int_plus (int_neg x) x)
                                  (int_plus_commutative x (int_neg x)))
                      (int_plus_neg_of_itself_l x)).
Qed.

(* ********** *)

Lemma int_mult_commutative :
  forall x y : int,
    int_mult x y == int_mult y x.
Proof.
  intros [a b] [c d].
  unfold int_eq, int_mult.
  rewrite -> (Nat.mul_comm a c).
  rewrite -> (Nat.mul_comm b d).
  rewrite -> (Nat.mul_comm a d).
  rewrite -> (Nat.mul_comm b c).
  rewrite -> (Nat.add_comm (c * b) (d * a)).
  reflexivity.
Qed.

Lemma int_mult_associative :
  forall x y z : int,
    int_mult (int_mult x y) z == int_mult x (int_mult y z).
Proof.
  intros [a b] [c d] [e f].
  unfold int_eq, int_mult.
  Search (_ + (_ + _) = _ + _).
  rewrite -> 2 Nat.add_assoc.
  Search (_ * _ = _ + _).
  rewrite -> 4 Nat.mul_add_distr_r.
  rewrite -> 4 Nat.mul_add_distr_l.
  rewrite -> 8 Nat.mul_assoc.
  rewrite -> (Nat.add_shuffle1 (a * c * e)).
  rewrite -> (Nat.add_comm (b * d * e)).
  Check (Nat.add_assoc (a * c * e + a * d * f + (b * c * f + b * d * e))
                       (a * c * f + a * d * e)
                       (b * c * e + b * d * f)).
  rewrite <- (Nat.add_assoc (a * c * e + a * d * f + (b * c * f + b * d * e))
                       (a * c * f + a * d * e)
                       (b * c * e + b * d * f)).
  rewrite -> (Nat.add_shuffle2 (a * c * f)).
  rewrite -> Nat.add_assoc.
  reflexivity.
Qed.

Lemma int_mult_1_r :
  forall x : int,
    int_mult x (1 -- 0) == x.
Proof.
  intros [a b].
  unfold int_eq, int_mult.
  rewrite -> 2 Nat.mul_0_r.
  rewrite -> 2 Nat.mul_1_r.
  rewrite -> Nat.add_0_r.
  rewrite -> Nat.add_0_l.
  reflexivity.
Qed.

Lemma int_mult_1_l :
  forall x : int,
    int_mult (1 -- 0) x == x.
Proof.
  (* Method 1: going back to natural numbers *)
  intros [a b].
  unfold int_eq, int_mult.
  rewrite -> 2 Nat.mul_0_l.
  rewrite -> 2 Nat.mul_1_l.
  rewrite -> Nat.add_0_r.
  rewrite -> Nat.add_0_r.
  reflexivity.

  Restart.
  (* Method 2: as a corollary of int_mult_1_r *)
  intro x.
  Check (int_eq_trans (int_mult (1 -- 0) x) (int_mult x (1 -- 0)) x
                      (int_mult_commutative (1 -- 0) x)
                      (int_mult_1_r x)).
  exact (int_eq_trans (int_mult (1 -- 0) x) (int_mult x (1 -- 0)) x
                      (int_mult_commutative (1 -- 0) x)
                      (int_mult_1_r x)).
Qed.

Corollary int_mult_1_both_sides :
  forall x : int,
    int_mult x (1 -- 0) == int_mult (1 -- 0) x.
Proof.
  intro x.
  Check (int_mult_commutative x (1 -- 0)).
  exact (int_mult_commutative x (1 -- 0)).
Qed.

Lemma int_mult_add_distr_r :
  forall x y z : int,
    int_mult (int_plus y z) x ==
    int_plus (int_mult y x) (int_mult z x).
Proof.
  intros [a b] [c d] [e f].
  unfold int_eq, int_plus, int_mult.
  Search ((_ + _) * _ = _).
  rewrite -> 4 Nat.mul_add_distr_r.
  rewrite -> (Nat.add_shuffle1 (c * a)).
  rewrite -> (Nat.add_comm (d * a)).
  rewrite -> (Nat.add_comm (f * a) (d * a)).
  rewrite -> 2 (Nat.add_shuffle2 (c * b)).
  rewrite -> (Nat.add_comm (f * a) (d * a)).
  reflexivity.
Qed.

Lemma int_mult_add_distr_l :
  forall x y z : int,
    int_mult x (int_plus y z) ==
    int_plus (int_mult x y) (int_mult x z).
Proof.
  intros x y z.
  assert (H_tmp := int_eq_trans (int_mult x (int_plus y z))
                                (int_mult (int_plus y z) x)
                                (int_plus (int_mult y x) (int_mult z x))
                                (int_mult_commutative x (int_plus y z))
                                (int_mult_add_distr_r x y z)).
  assert (H_rhs_comm := int_eq_trans
                          (int_plus (int_mult y x) (int_mult z x))
                          (int_plus (int_mult y x) (int_mult x z))
                          (int_plus (int_mult x y) (int_mult x z))
                          (int_plus_eq_r (int_mult y x)
                                         (int_mult z x)
                                         (int_mult x z)
                                         (int_mult_commutative z x))
                          (int_plus_eq_l (int_mult y x)
                                         (int_mult x y)
                                         (int_mult x z)
                                         (int_mult_commutative y x))).
  exact (int_eq_trans (int_mult x (int_plus y z))
                      (int_plus (int_mult y x) (int_mult z x))
                      (int_plus (int_mult x y) (int_mult x z))
                      H_tmp H_rhs_comm).
Qed.

(* ********** *)

Definition int_sub (x y : int) : int :=
  int_plus x (int_neg y).
  
Proposition int_mult_no_zero_divisors :
  forall x y : int,
    int_mult x y == (0 -- 0) ->
    x == (0 -- 0) \/ y == (0 -- 0) \/
    (x == (0 --0) /\ y == (0 -- 0)).
Proof.
  intros x y H_eq0.
  Check (int_lt_trichotomy x).
  destruct (int_lt_trichotomy x) as [n H_trich].
  destruct H_trich as [H_zero | [H_pos | H_neg]].

  - left.
    exact H_zero.

  - right.
    left.
    destruct x as [a b].
    destruct y as [c d].
    unfold int_eq in H_pos.
    unfold int_eq, int_mult in H_eq0.
    unfold int_eq.
    rewrite -> Nat.add_0_l in H_eq0.
    rewrite -> Nat.add_0_r in H_eq0.
    rewrite -> Nat.add_0_r in H_pos.
    rewrite -> Nat.add_0_l.
    rewrite -> Nat.add_0_r.
    rewrite -> H_pos in H_eq0.

    (* simplifying LHS of H_eq0*)
    Search ((_ + _) * _ = _ * _ + _ * _).
    Check (Nat.mul_add_distr_r (S n) b c).
    assert (H_tmp_Sn_b_c := Nat.mul_add_distr_r (S n) b c).
    Search (_ = _ -> _ + _ = _ + _).
    Check (f_equal2_plus ((S n + b) * c) (S n * c + b * c)
                         (b * d) (b * d)
                         H_tmp_Sn_b_c
                         (eq_refl (b * d))).
    rewrite -> (f_equal2_plus ((S n + b) * c) (S n * c + b * c)
                              (b * d) (b * d)
                              H_tmp_Sn_b_c
                              (eq_refl (b * d))) in H_eq0.
    clear H_tmp_Sn_b_c.

    (* simplifying RHS of H_eq0 *)
    Check (Nat.mul_add_distr_r (S n) b d).
    assert (H_tmp_Sn_b_d := Nat.mul_add_distr_r (S n) b d).
    Check (f_equal2_plus ((S n + b) * d) (S n * d + b * d)
                         (b * c) (b * c)
                         H_tmp_Sn_b_d
                         (eq_refl (b * c))).
    rewrite -> (f_equal2_plus ((S n + b) * d) (S n * d + b * d)
                              (b * c) (b * c)
                              H_tmp_Sn_b_d
                              (eq_refl (b * c))) in H_eq0.
    clear H_tmp_Sn_b_d.
    
    (* cancel repeated nat addition terms on both sides *)
    Search (_ + _ = _ + _ -> _ = _).
    Check (plus_reg_l (S n * c + b * d) (S n * d + b * d) (b * c)).
    (* wanted: b * c + (S n * c + b * d) = b * c + (S n * d + b * d) *)
    Check (Nat.add_comm (S n * d + b * d) (b * c)).
    rewrite -> (Nat.add_comm (S n * d + b * d) (b * c)) in H_eq0.
    Check (Nat.add_shuffle0 (S n * c) (b * c) (b * d)).
    rewrite -> (Nat.add_shuffle0 (S n * c) (b * c) (b * d)) in H_eq0.
    rewrite -> (Nat.add_comm (S n * c + b * d) (b * c)) in H_eq0.
    assert (H_eq0_reduced1 :=
              plus_reg_l (S n * c + b * d) (S n * d + b * d) (b * c) H_eq0).
    
    rewrite -> (Nat.add_comm (S n * d) (b * d)) in H_eq0_reduced1.
    rewrite -> (Nat.add_comm (S n * c) (b * d)) in H_eq0_reduced1.
    assert (H_eq0_reduced2 :=
              plus_reg_l (S n * c) (S n * d) (b * d) H_eq0_reduced1).
    clear H_eq0_reduced1.

    Search (_ * _ = _ * _ -> _ = _).
    Check (Nat.mul_cancel_l c d (S n)).
    Search (S _ <> 0).
    Check (Nat.mul_cancel_l c d (S n) (Nat.neq_succ_0 n)).
    destruct (Nat.mul_cancel_l c d (S n) (Nat.neq_succ_0 n))
      as [H_tmp_cancel _].
    exact (H_tmp_cancel H_eq0_reduced2).

  - right.
    left.
    destruct x as [a b].
    destruct y as [c d].
    unfold int_eq in H_neg.
    unfold int_eq, int_mult in H_eq0.
    unfold int_eq.
    rewrite -> Nat.add_0_l in H_eq0.
    rewrite -> Nat.add_0_r in H_eq0.
    rewrite -> Nat.add_0_l in H_neg.
    rewrite -> Nat.add_0_l.
    rewrite -> Nat.add_0_r.
    rewrite <- H_neg in H_eq0.

    (* simplifying LHS of H_eq0*)
    Check (Nat.mul_add_distr_r a (S n) d).
    assert (H_tmp_a_Sn_d := Nat.mul_add_distr_r a (S n) d).
    Check (f_equal2_plus (a * c) (a * c)
                         ((a + S n) * d) (a * d + S n * d)
                         (eq_refl (a * c))
                         H_tmp_a_Sn_d).
    rewrite -> (f_equal2_plus (a * c) (a * c)
                              ((a + S n) * d) (a * d + S n * d)
                              (eq_refl (a * c))
                              H_tmp_a_Sn_d) in H_eq0.
    clear H_tmp_a_Sn_d.

    (* simplifying RHS of H_eq0 *)
    Check (Nat.mul_add_distr_r a (S n) c).
    assert (H_tmp_a_Sn_c := Nat.mul_add_distr_r a (S n) c).
    Check (f_equal2_plus (a * d) (a * d)
                         ((a + S n) * c) (a * c + S n * c)
                         (eq_refl (a * d))
                         H_tmp_a_Sn_c).
    rewrite -> (f_equal2_plus (a * d) (a * d)
                              ((a + S n) * c) (a * c + S n * c)
                              (eq_refl (a * d))
                              H_tmp_a_Sn_c) in H_eq0.
    clear H_tmp_a_Sn_c.
    
    (* cancel repeated nat addition terms on both sides *)
    Check (plus_reg_l (a * d + S n * d)
                      (a * d + S n * c)
                      (a * c)).
    Check (Nat.add_shuffle3 (a * d) (a * c) (S n * c)).
    rewrite -> (Nat.add_shuffle3 (a * d) (a * c) (S n * c)) in H_eq0.
    assert (H_eq0_reduced1 := plus_reg_l (a * d + S n * d)
                                         (a * d + S n * c)
                                         (a * c) H_eq0).
    assert (H_eq0_reduced2 := plus_reg_l (S n * d)
                                         (S n * c)
                                         (a * d) H_eq0_reduced1).
    clear H_eq0_reduced1.

    (* apply cancellation law to H_eq0_reduced2 *)
    destruct (Nat.mul_cancel_l d c (S n) (Nat.neq_succ_0 n))
      as [H_tmp_cancel _].
    rewrite -> (H_tmp_cancel H_eq0_reduced2).
    reflexivity.
Qed.

Definition int_neq (x y : int) : Prop :=
  match x, y with
  | (a -- b), (c -- d) => a + d <> c + b
  end.

Lemma int_sub_eq_is_0 :
  forall x y : int,
    x == y <-> int_sub x y == (0 -- 0).
Proof.
  intros x y.
  split.

  - intro H_eq.
    unfold int_sub.
    Check (int_plus_neg_of_itself_l y).
    Check (int_eq_trans (int_plus x (int_neg y))
                        (int_plus y (int_neg y))
                        (0 -- 0)).
    (* wanted: int_plus x (int_neg y) == int_plus y (int_neg y) *)
    Check (int_plus_eq_l x y (int_neg y) H_eq).
    Check (int_eq_trans (int_plus x (int_neg y))
                        (int_plus y (int_neg y))
                        (0 -- 0)
                        (int_plus_eq_l x y (int_neg y) H_eq)
                        (int_plus_neg_of_itself_l y)).

    exact (int_eq_trans (int_plus x (int_neg y))
                        (int_plus y (int_neg y))
                        (0 -- 0)
                        (int_plus_eq_l x y (int_neg y) H_eq)
                        (int_plus_neg_of_itself_l y)).

  - revert x y.
    intros [a b] [c d].
    unfold int_sub.
    unfold int_plus, int_neg, int_eq.
    intro H_eq0.
    rewrite -> Nat.add_0_r in H_eq0.
    rewrite -> Nat.add_0_l in H_eq0.
    rewrite -> (Nat.add_comm b c) in H_eq0.
    exact H_eq0.
Qed.

Lemma int_mult_neg_r :
  forall x y : int,
    int_mult x (int_neg y) == int_neg (int_mult x y).
Proof.
  intros [a b] [c d].
  unfold int_mult, int_neg.
  reflexivity.
Qed.

Lemma int_mult_sub_distr_r :
  forall x y z : int,
    int_mult (int_sub y z) x ==
    int_sub (int_mult x y) (int_mult x z).
Proof.
  intros x y z.
  Check (int_mult_add_distr_r).
  (* int_mult_add_distr_r: forall x y z : int,
   * int_mult (int_plus y z) x == int_plus (int_mult y x) (int_mult z x) *)
  
  unfold int_sub.
  Check (int_mult_add_distr_r x y (int_neg z)).
  (* int_mult (int_plus y (int_neg z)) x ==
   * int_plus (int_mult x y) (int_mult x (int_neg z)) *)

  Check (int_mult_neg_r x z).
  assert (H_rhs_commutative := int_eq_trans
                          (int_plus (int_mult y x) (int_mult (int_neg z) x))
                          (int_plus (int_mult x y) (int_mult (int_neg z) x))
                          (int_plus (int_mult x y) (int_mult x (int_neg z)))
                          (int_plus_eq_l
                             (int_mult y x)
                             (int_mult x y)
                             (int_mult (int_neg z) x)
                             (int_mult_commutative y x))
                          (int_plus_eq_r
                             (int_mult x y)
                             (int_mult (int_neg z) x)
                             (int_mult x (int_neg z))
                             (int_mult_commutative (int_neg z) x))).
  assert (H_neg_assoc := int_plus_eq_r (int_mult x y)
                                       (int_mult x (int_neg z))
                                       (int_neg (int_mult x z))
                                       (int_mult_neg_r x z)).
  assert (H_tmp := int_eq_trans
                     (int_mult (int_plus y (int_neg z)) x)
                     (int_plus (int_mult y x) (int_mult (int_neg z) x))
                     (int_plus (int_mult x y) (int_mult x (int_neg z)))
                     (int_mult_add_distr_r x y (int_neg z))
                     H_rhs_commutative); clear H_rhs_commutative.
  exact (int_eq_trans (int_mult (int_plus y (int_neg z)) x)
                       (int_plus (int_mult x y) (int_mult x (int_neg z)))
                       (int_plus (int_mult x y) (int_neg (int_mult x z)))
                       H_tmp H_neg_assoc).
Qed.

Corollary int_mult_non_zero :
  forall x y : int,
    int_mult x y == (0 -- 0) ->
    int_neq y (0 -- 0) ->
    x == (0 -- 0).
Proof.
  intros x y H_eq0.
  Check (int_mult_no_zero_divisors x y H_eq0).
  destruct (int_mult_no_zero_divisors x y H_eq0) as [H_x_eq0 | [H_y_eq0 | H_x_y_eq0]].
  
  - intro H_y_neq0.
    exact H_x_eq0.

  - intro H_y_neq0.
    destruct y as [a b].
    unfold int_neq in H_y_neq0.
    unfold int_eq in H_y_eq0.
    unfold not in H_y_neq0.
    contradiction (H_y_neq0 H_y_eq0).

  - intro H_y_neq0.
    destruct H_x_y_eq0 as [H_x_eq0 _].
    exact H_x_eq0.
Qed.

Corollary int_mult_cancel_l :
  forall x y z : int,
    int_neq z (0 -- 0) ->
    int_mult z x == int_mult z y -> x == y.
Proof.
  intros x y z H_0 H_eq.
  
  (* wanted: int_mult x z == int_mult y z ->
   * int_sub (int_mult x z) (int_mult y z) == (0 -- 0) *)
  destruct (int_sub_eq_is_0 (int_mult z x) (int_mult z y)) as [H_sub_eq_mult _].
  
  (* wanted: int_mult (int_sub x y) z == (0 -- 0) *)
  Check (int_eq_trans (int_mult (int_sub x y) z)
                      (int_sub (int_mult x z)
                               (int_mult y z))
                      (0 -- 0)).
  assert (H_move_to_lhs := int_eq_trans (int_mult (int_sub x y) z)
                                        (int_sub (int_mult z x)
                                                 (int_mult z y))
                                        (0 -- 0)
                                        (int_mult_sub_distr_r z x y)
                                        (H_sub_eq_mult H_eq)).
  
  (* wanted: int_sub x y == (0 -- 0) *)
  assert (H_cancelled_lhs := int_mult_non_zero (int_sub x y) z
                                               H_move_to_lhs
                                               H_0).

  (*  wanted: int_sub x y == (0 -- 0) -> x == y *)
  Check (int_sub_eq_is_0 x y).
  destruct (int_sub_eq_is_0 x y) as [_ H_sub_eq_xy].
  Check (H_sub_eq_xy H_cancelled_lhs).
  exact (H_sub_eq_xy H_cancelled_lhs).
Qed.

(* ********** *)

Definition int_ge (x y : int) : Prop :=
  exists n : nat,
    x == int_plus y (n -- 0).

Definition int_le (x y : int) : Prop :=
  int_ge y x.

Definition int_gt (x y : int) : Prop :=
  int_ge x y /\ int_neq x y.

Definition int_lt (x y : int) : Prop :=
  int_le x y /\ int_neq x y.

Lemma int_neq_and_eq_false :
  forall x y : int,
    int_neq x y ->
    x == y -> False.
Proof.
  intros [a b] [c d].
  unfold int_neq, int_eq.
  intros H_neq H_eq.
  unfold not in H_neq.
  exact (H_neq H_eq).
Qed.

Lemma int_plus_neg_of_itself_and_others_l :
  forall x y : int,
    int_plus (int_plus x y) (int_neg x) == y.
Proof.
  intros [a b] [c d].
  unfold int_eq, int_plus, int_neg. 
  repeat rewrite -> Nat.add_assoc.
  rewrite -> (Nat.add_comm (c + b + d) a).
  repeat rewrite -> Nat.add_assoc.
  reflexivity.
Qed.

Proposition int_gt_to_pos_nat :
  forall x y : int,
    int_gt x y -> 
    exists n : nat,
      int_sub x y == (S n -- 0).
Proof.
  intros x y.
  unfold int_gt.
  intros [H_ge H_neq].
  unfold int_ge in H_ge.
  destruct H_ge as [[ | n'] H_n'].
  - Check (int_plus_0_r y).
    assert (H_eq := int_eq_trans
                      x
                      (int_plus y (0 -- 0))
                      y
                      H_n'
                      (int_plus_0_r y)).
    Check (int_neq_and_eq_false x y H_neq H_eq).
    contradiction (int_neq_and_eq_false x y H_neq H_eq).
  - exists n'.
    unfold int_sub.
    Check (int_plus_eq_l
             x
             (int_plus y (S n' -- 0))
             (int_neg y)
             H_n').
    (* wanted: int_plus (int_plus y (S n' -- 0)) (int_neg y) == (S n' -- 0) *)
    Check (int_plus_neg_of_itself_and_others_l
             y (S n' -- 0)).
    Check (int_eq_trans
             (int_plus x (int_neg y))
             (int_plus (int_plus y (S n' -- 0)) (int_neg y))
             (S n' -- 0)
             (int_plus_eq_l
                x
                (int_plus y (S n' -- 0))
                (int_neg y)
                H_n')
             (int_plus_neg_of_itself_and_others_l
                y (S n' -- 0))).
    exact (int_eq_trans
             (int_plus x (int_neg y))
             (int_plus (int_plus y (S n' -- 0)) (int_neg y))
             (S n' -- 0)
             (int_plus_eq_l
                x
                (int_plus y (S n' -- 0))
                (int_neg y)
                H_n')
             (int_plus_neg_of_itself_and_others_l
                y (S n' -- 0))).
Qed.

Proposition pos_nat_to_int_gt :
  forall x y : int,
  exists n : nat,
    int_sub x y == (S n -- 0) ->
    int_gt x y.
Proof.
  intros [a b] [c d].
  exists 0.
  unfold int_sub, int_gt, int_ge,
  int_plus, int_neg, int_eq, int_neq.
  intro H_eq.
  split.
  - exists 1.
    rewrite -> Nat.add_0_r.
    rewrite -> Nat.add_0_r in H_eq.
    rewrite -> H_eq.
    ring.
  - rewrite -> Nat.add_0_r in H_eq.
    rewrite -> H_eq.
    rewrite -> (Nat.add_1_l (b + c)).
    rewrite -> (Nat.add_comm c b).
    Search (S _ <> _).
    Check (Nat.neq_succ_diag_l (b + c)).
    exact (Nat.neq_succ_diag_l (b + c)).
Qed.

Proposition int_ge_plus_both_sides :
  forall x y z : int,
    int_ge x y -> int_ge (int_plus x z) (int_plus y z).
Proof.
  intros [a b] [c d] [e f].
  unfold int_ge, int_plus, int_eq.
  intro H_ge.
  inversion H_ge as [n H_eq].
  exists n.
  Search (_ = _ -> _ + _ = _).
  rewrite -> Nat.add_0_r in H_eq.
  rewrite -> Nat.add_0_r.
  Check (f_equal2_plus e e (a + d) (c + n + b)
                       (eq_refl e) H_eq).
  assert (H_eq_added1 := f_equal2_plus
                           e e (a + d)
                           (c + n + b)
                           (eq_refl e) H_eq).
  rewrite -> 2 Nat.add_assoc.
  rewrite -> (Nat.add_comm a e).
  rewrite -> (Nat.add_comm c e).
  assert (H_eq_added2 := f_equal2_plus
                           (e + (a + d))
                           (e + (c + n + b))
                           f f H_eq_added1
                           (eq_refl f)).
  rewrite -> 3 Nat.add_assoc in H_eq_added2.
  exact H_eq_added2.
Qed.

Lemma int_neq_plus_both_sides :
  forall x y z : int,
    int_neq x y -> int_neq (int_plus x z) (int_plus y z).
Proof.
  intros [a b] [c d] [e f].
  unfold int_neq, int_plus, not.
  intros H_neq_x_y.
  intros H_neq_xz_yz.
  rewrite -> (Nat.add_shuffle1 a e d f) in H_neq_xz_yz.
  rewrite -> (Nat.add_shuffle1 c e b f) in H_neq_xz_yz.
  rewrite -> (Nat.add_comm (a + d)) in H_neq_xz_yz.
  rewrite -> (Nat.add_comm (c + b)) in H_neq_xz_yz.
  Search (_ + _ = _ -> _ = _).
  Check (plus_reg_l (a + d) (c + b) (e + f) H_neq_xz_yz).
  exact (H_neq_x_y (plus_reg_l (a + d) (c + b) (e + f) H_neq_xz_yz)).
Qed.

Proposition int_gt_plus_both_sides :
  forall x y z : int,
    int_gt x y -> int_gt (int_plus x z) (int_plus y z).
Proof.
  intros x y z.
  unfold int_gt.
  intros [H_ge H_neq].
  split.
  - exact (int_ge_plus_both_sides x y z H_ge).
  - exact (int_neq_plus_both_sides x y z H_neq).
Qed.

Proposition int_gt_mult_both_sides :
  forall x y: int,
    int_gt x y ->
    forall n : nat,
      int_gt (int_mult x (S n -- 0)) (int_mult y (S n -- 0)).
Proof.
  intros [a b] [c d].
  unfold int_gt, int_ge.
  intros [H_ge_x_y H_neq] n.
  destruct H_ge_x_y as [n' H_eq].
  split.
  - exists (S n * n').
    unfold int_mult, int_plus, int_eq.
    repeat rewrite -> Nat.mul_0_r.
    repeat rewrite -> Nat.add_0_r.
    repeat rewrite -> Nat.add_0_l.
    rewrite -> (Nat.mul_comm (S n) n').
    repeat rewrite <- Nat.mul_add_distr_r.
    unfold int_plus, int_eq in H_eq.
    rewrite -> Nat.add_0_r in H_eq.
    rewrite -> H_eq.
    reflexivity.
  - unfold int_neq, not in H_neq.
    unfold int_mult, int_neq, not.
    repeat rewrite -> Nat.mul_0_r.
    repeat rewrite -> Nat.add_0_r.
    repeat rewrite -> Nat.add_0_l.
    repeat rewrite <- Nat.mul_add_distr_r.
    intro H_neq'.
    Search (S _ <> 0).
    Check (Nat.mul_cancel_r (a + d) (c + b) (S n)
                            (Nat.neq_succ_0 n)).
    destruct (Nat.mul_cancel_r
                (a + d) (c + b) (S n)
                (Nat.neq_succ_0 n)) as [H_neq'_to_neq _].
    exact (H_neq (H_neq'_to_neq H_neq')).
Qed.

Proposition int_gt_to_int_lt_neg :
  forall x y : int,
    int_gt x y ->
    int_lt (int_neg x) (int_neg y).
Proof.
  intros [a b] [c d].
  unfold int_gt, int_lt, int_neg, int_le, int_ge.
  intros [[n H_eq_x_yn] H_neq].
  split.
  - exists n.
    unfold int_plus, int_eq;
      unfold int_plus, int_eq in H_eq_x_yn.
    rewrite -> Nat.add_0_r;
      rewrite -> Nat.add_0_r in H_eq_x_yn.
    rewrite -> Nat.add_comm in H_eq_x_yn.
    rewrite -> H_eq_x_yn.
    ring.
  - unfold int_neq, not;
      unfold int_neq, not in H_neq.
    intro H_eq.
    rewrite -> (Nat.add_comm d a) in H_eq.
    rewrite -> (Nat.add_comm b c) in H_eq.
    Check (eq_sym H_eq).
    exact (H_neq (eq_sym H_eq)).
Qed.

Proposition int_gt_trans :
  forall x y z : int,
    int_gt x y ->
    int_gt y z ->
    int_gt x z.
Proof.
  intros [a b] [c d] [e f].
  unfold int_gt, int_ge, int_plus, int_eq, int_neq, not.
  intros [[n1 H_eq_x_yn] H_neq_x_y] [[n2 H_eq_y_zn] _].
  split.
  - exists (n1 + n2).
    rewrite -> Nat.add_0_r;
      rewrite -> Nat.add_0_r in H_eq_x_yn, H_eq_y_zn.
    Search (_ = _ -> _ = _ -> _ + _ = _).
    Check (f_equal2_plus (a + d) (c + n1 + b)
                         (c + f) (e + n2 + d)
                         H_eq_x_yn H_eq_y_zn).
    assert (H_combined := f_equal2_plus
                            (a + d) (c + n1 + b)
                            (c + f) (e + n2 + d)
                            H_eq_x_yn H_eq_y_zn).
    (* wanted: c + d + _ = c + d + _ *)
    rewrite -> (Nat.add_shuffle2 a d c f) in H_combined.
    rewrite -> (Nat.add_comm (a + f)) in H_combined.
    repeat rewrite -> Nat.add_assoc in H_combined.
    rewrite -> (Nat.add_comm (c + n1 + b + e + n2) d) in H_combined.
    repeat rewrite -> Nat.add_assoc in H_combined.
    Check (Nat.add_assoc).
    repeat rewrite <- (Nat.add_assoc (d + c)) in H_combined.
    Check (plus_reg_l (a + f) (n1 + b + e + n2) (d + c)).
    rewrite -> (plus_reg_l (a + f) (n1 + b + e + n2) (d + c) H_combined).
    ring.
  - intro H_neq_x_z.
    rewrite -> Nat.add_0_r in H_eq_x_yn, H_eq_y_zn.
    destruct n1 as [ | n1'].
    + rewrite -> Nat.add_0_r in H_eq_x_yn.
      exact (H_neq_x_y H_eq_x_yn).
    + assert (H_combined := f_equal2_plus
                              (a + d) (c + S n1' + b)
                              (c + f) (e + n2 + d)
                              H_eq_x_yn H_eq_y_zn).
      repeat rewrite -> Nat.add_assoc in H_combined.
      rewrite -> (Nat.add_comm (a + d + c) f) in H_combined.
      repeat rewrite -> Nat.add_assoc in H_combined.
      rewrite -> (Nat.add_comm f a) in H_combined.
      rewrite -> H_neq_x_z in H_combined.
      rewrite -> (Nat.add_comm (c + S n1' + b + e + n2) d) in H_combined.
      repeat rewrite -> Nat.add_assoc in H_combined.
      repeat rewrite <- (Nat.add_assoc (d + c)) in H_combined.
      repeat rewrite <- (Nat.add_assoc (e + b)) in H_combined.
      rewrite -> (Nat.add_comm (e + b)) in H_combined.
      assert (H_reduced1 := plus_reg_l
                              (e + b) (S n1' + b + e + n2)
                              (d + c) H_combined).
      clear H_combined.
      repeat rewrite <- (Nat.add_assoc (S n1')) in H_reduced1.
      rewrite -> (Nat.add_comm (S n1')) in H_reduced1.
      rewrite -> (Nat.add_comm e b) in H_reduced1.
      repeat rewrite <- (Nat.add_assoc (b + e)) in H_reduced1.
      rewrite <- Nat.add_0_r in H_reduced1 at 1.
      assert (H_eq_0_S := plus_reg_l 0 (n2 + S n1')
                                     (b + e) H_reduced1).
      clear H_reduced1.
      Search (S _ = _).
      rewrite <- plus_n_Sm in H_eq_0_S.
      Search (0 < S _).
      assert (H_lt := Nat.lt_0_succ (n2 + n1')).
      Search (_ < _ -> _ <> _).
      Check (Nat.lt_neq 0 (S (n2 + n1')) H_lt).
      assert (H_neq := Nat.lt_neq 0 (S (n2 + n1')) H_lt).
      unfold not in H_neq.
      contradiction (H_neq H_eq_0_S).
Qed.

Proposition int_ge_sym_eq :
  forall x y : int,
    int_ge x y ->
    int_ge y x ->
    x == y.
Proof.
  intros [a b] [c d].
  unfold int_ge, int_plus, int_eq.
  intros [[ | n1'] H_eq_x_yn] [n2 H_eq_y_xn].
  - rewrite -> Nat.add_0_r in H_eq_x_yn, H_eq_y_xn.
    rewrite -> Nat.add_0_r in H_eq_x_yn.
    exact H_eq_x_yn.
  - rewrite -> Nat.add_0_r in H_eq_x_yn, H_eq_y_xn.
    assert (H_combined := f_equal2_plus
                            (a + d) (c + S n1' + b)
                            (c + b) (a + n2 + d)
                            H_eq_x_yn H_eq_y_xn).
    rewrite -> (Nat.add_shuffle0 c (S n1') b) in H_combined.
    rewrite -> (Nat.add_comm (a + d)) in H_combined.
    repeat rewrite -> Nat.add_assoc in H_combined.
    repeat rewrite <- (Nat.add_assoc (c + b)) in H_combined.
    Check (plus_reg_l (a + d) (S n1' + a + n2 + d) (c + b) H_combined).
    assert (H_reduced1 := plus_reg_l (a + d) (S n1' + a + n2 + d)
                                     (c + b) H_combined).
    clear H_combined.
    rewrite -> (Nat.add_comm (S n1') a) in H_reduced1.
    rewrite -> (Nat.add_comm (a + S n1' + n2) d) in H_reduced1.
    repeat rewrite -> Nat.add_assoc in H_reduced1.
    rewrite -> (Nat.add_comm d a) in H_reduced1.
    rewrite <- (Nat.add_assoc (a + d)) in H_reduced1.
    rewrite <- Nat.add_0_r in H_reduced1 at 1.
    assert (H_eq_0_S := plus_reg_l 0 (S n1' + n2)
                                   (a + d) H_reduced1).
    clear H_reduced1.
    rewrite -> Nat.add_comm in H_eq_0_S.
    rewrite <- plus_n_Sm in H_eq_0_S.
    assert (H_lt := Nat.lt_0_succ (n2 + n1')).
    Check (Nat.lt_neq 0 (S (n2 + n1')) H_lt).
    assert (H_neq := Nat.lt_neq 0 (S (n2 + n1')) H_lt).
    unfold not in H_neq.
    contradiction (H_neq H_eq_0_S).
Qed.

(* ********** *)

(* end of integers.v *)
