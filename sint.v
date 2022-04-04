(* sint.v *)

(* ********** *)

Require Import Arith Bool.

Inductive sint : Type :=
| P : nat -> sint
| Z : sint
| N : nat -> sint.

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

Notation "x == y" := (sint_eq x y) (at level 70, no associativity).

Proposition sint_eq_refl :
  forall x : sint,
    x == x.
Proof.
  intro x.
  destruct x as [p |  | n].
  - unfold sint_eq; reflexivity.
  - unfold sint_eq; reflexivity.
  - unfold sint_eq; reflexivity.

  Restart.

  (intros [p |  | n]; unfold sint_eq; reflexivity).
Qed.


Proposition sint_eq_sym :
  forall x y : sint,
    x == y -> y == x.
Proof.
  intros [px |  | nx] [py |  | ny].
  
  - unfold sint_eq.
    intro H_eq.
    exact (eq_sym H_eq).
  - unfold sint_eq; intro H_eq.
    contradiction H_eq.
  - unfold sint_eq; intro H_eq; contradiction H_eq.
    
  - unfold sint_eq; intro H_eq; contradiction H_eq.
  - unfold sint_eq; intro H_eq.
    exact H_eq.
  - unfold sint_eq; intro H_eq; contradiction H_eq.
    
  - unfold sint_eq; intro H_eq; contradiction H_eq.
  - unfold sint_eq; intro H_eq; contradiction H_eq.
  - unfold sint_eq; intro H_eq.
    rewrite -> H_eq.
    reflexivity.

  Restart.
  
  (intros [px |  | nx] [py |  | ny];
   unfold sint_eq; intro H_eq;
   (exact (eq_sym H_eq) || contradiction H_eq ||
    exact H_eq || rewrite -> H_eq; reflexivity)).
Qed.

Proposition sint_eq_trans :
  forall x y z : sint,
    x == y -> y == z -> x == z.
Proof.
  intros [px |  | nx] [py |  | ny] [pz |  | nz].
  
  - unfold sint_eq.
    intros H_xy H_yz.
    rewrite -> H_xy.
    rewrite -> H_yz.
    reflexivity.
  - unfold sint_eq; intros H_xy H_yz.
    contradiction H_yz.
  - unfold sint_eq; intros H_xy H_yz; contradiction H_yz.

  - unfold sint_eq; intros H_xy H_yz; contradiction H_xy.
  - unfold sint_eq; intros H_xy H_yz; contradiction H_xy.
  - unfold sint_eq; intros H_xy H_yz; contradiction H_xy.

  - unfold sint_eq; intros H_xy H_yz; contradiction H_xy.
  - unfold sint_eq; intros H_xy H_yz; contradiction H_xy.
  - unfold sint_eq; intros H_xy H_yz; contradiction H_xy.

  - unfold sint_eq; intros H_xy H_yz; contradiction H_xy.
  - unfold sint_eq; intros H_xy H_yz; contradiction H_xy.
  - unfold sint_eq; intros H_xy H_yz; contradiction H_xy.
    
  - unfold sint_eq; intros H_xy H_yz; contradiction H_yz.
  - unfold sint_eq; intros H_xy H_yz.
    exact H_yz.
  - unfold sint_eq; intros H_xy H_yz; contradiction H_yz.

  - unfold sint_eq; intros H_xy H_yz; contradiction H_xy.
  - unfold sint_eq; intros H_xy H_yz; contradiction H_xy.
  - unfold sint_eq; intros H_xy H_yz; contradiction H_xy.

  - unfold sint_eq; intros H_xy H_yz; contradiction H_xy.
  - unfold sint_eq; intros H_xy H_yz; contradiction H_xy.
  - unfold sint_eq; intros H_xy H_yz; contradiction H_xy.

  - unfold sint_eq; intros H_xy H_yz; contradiction H_xy.
  - unfold sint_eq; intros H_xy H_yz; contradiction H_xy.
  - unfold sint_eq; intros H_xy H_yz; contradiction H_xy.

  - unfold sint_eq; intros H_xy H_yz; contradiction H_yz.
  - unfold sint_eq; intros H_xy H_yz; contradiction H_yz.
  - unfold sint_eq; intros H_xy H_yz.
    rewrite -> H_xy; rewrite -> H_yz; reflexivity.

    Restart.

    (intros [px |  | nx] [py |  | ny] [pz |  | nz];
     unfold sint_eq; intros H_xy H_yz;
     ((rewrite -> H_xy; rewrite -> H_yz; reflexivity) ||
      contradiction H_yz ||
      contradiction H_xy ||
      exact H_yz)).
Qed.

Definition nat_to_sint (n : nat) : sint :=
  match n with
  | O =>
    Z
  | S _ =>
    P n
  end.

Definition sint_add (i1 i2 : sint) : sint :=
  match i1 with
  | P n1 =>
    match i2 with
    | P n2 =>
      P (n1 + n2 + 1)
    | Z =>
      i1
    | N n2 =>
      if n1 =? n2
      then Z
      else if n1 <? n2
           then N (n2 - n1 - 1)
           else P (n1 - n2 - 1)
    end
  | Z =>
    i2
  | N n1 =>
    match i2 with
    | P n2 =>
      if n1 =? n2
      then Z
      else if n1 <? n2
           then P (n2 - n1 - 1)
           else N (n1 - n2 - 1)
    | Z =>
      i1
    | N n2 =>
      N (n1 + n2 + 1)
    end
  end.

Lemma sint_add_eq_l :
  forall x x' y : sint,
    x == x' ->
    sint_add x y == sint_add x' y.
Proof.
  intros [px |  | nx] [px' |  | nx'] [py |  | ny].

  - unfold sint_eq, sint_add.
    intro H_eqx.
    rewrite -> H_eqx.
    reflexivity.
  - unfold sint_eq, sint_add; intros H_eqx.
    exact H_eqx.
  - unfold sint_add; intros H_eqx.
    unfold sint_eq in H_eqx.
    rewrite -> H_eqx.
    (* reflexivity. *)
    Check (sint_eq_refl (if px' =? ny then Z
                         else if px' <? ny then N (ny - px' - 1) else P (px' - ny - 1))).
    exact (sint_eq_refl (if px' =? ny then Z
                         else if px' <? ny then N (ny - px' - 1) else P (px' - ny - 1))).
  - unfold sint_eq; intro H_eqx.
    contradiction H_eqx.
  - unfold sint_eq; intro H_eqx; contradiction H_eqx.
  - unfold sint_eq; intro H_eqx; contradiction H_eqx.
    
  - unfold sint_eq; intro H_eqx; contradiction H_eqx.
  - unfold sint_eq; intro H_eqx; contradiction H_eqx.
  - unfold sint_eq; intro H_eqx; contradiction H_eqx.
    
  - unfold sint_eq; intro H_eqx; contradiction H_eqx.
  - unfold sint_eq; intro H_eqx; contradiction H_eqx.
  - unfold sint_eq; intro H_eqx; contradiction H_eqx.

  - unfold sint_eq, sint_add; intro H_eqx; reflexivity.
  - unfold sint_eq, sint_add; intro H_eqx; reflexivity.
  - unfold sint_eq, sint_add; intro H_eqx; reflexivity.

  - unfold sint_eq; intro H_eqx; contradiction H_eqx.
  - unfold sint_eq; intro H_eqx; contradiction H_eqx.
  - unfold sint_eq; intro H_eqx; contradiction H_eqx.
    
  - unfold sint_eq; intro H_eqx; contradiction H_eqx.
  - unfold sint_eq; intro H_eqx; contradiction H_eqx.
  - unfold sint_eq; intro H_eqx; contradiction H_eqx.
    
  - unfold sint_eq; intro H_eqx; contradiction H_eqx.
  - unfold sint_eq; intro H_eqx; contradiction H_eqx.
  - unfold sint_eq; intro H_eqx; contradiction H_eqx.

  - unfold sint_add; intro H_eqx.
    unfold sint_eq in H_eqx; rewrite -> H_eqx.    
    Check (sint_eq_refl (if nx' =? py then Z
                         else if nx' <? py then P (py - nx' - 1) else N (nx' - py - 1))).
    exact (sint_eq_refl (if nx' =? py then Z
                         else if nx' <? py then P (py - nx' - 1) else N (nx' - py - 1))).
  - unfold sint_eq, sint_add; intro H_eqx.
    exact H_eqx.
  - unfold sint_eq, sint_add; intro H_eqx.
    rewrite -> H_eqx; reflexivity.

  Restart.  
    
  (intros [px |  | nx] [px' |  | nx'] [py |  | ny];
   ((unfold sint_eq, sint_add; intro H_eqx;
     ((rewrite -> H_eqx; reflexivity) ||
      exact H_eqx ||
      reflexivity)) ||

    (unfold sint_add; intro H_eqx;
     unfold sint_eq in H_eqx; rewrite -> H_eqx;
     (exact (sint_eq_refl (if px' =? ny then Z
                           else if px' <? ny then N (ny - px' - 1)
                                else P (px' - ny - 1))) ||
      exact (sint_eq_refl (if nx' =? py then Z
                           else if nx' <? py then P (py - nx' - 1)
                                else N (nx' - py - 1))))) ||
    (unfold sint_eq; intro H_eqx; contradiction H_eqx)
  )).
Qed.

Lemma sint_add_comm :
  forall x y : sint,
    sint_add x y == sint_add y x.
Proof.
  intros [px |  | nx] [py |  | ny].
  - unfold sint_add, sint_eq; ring.
  - unfold sint_add, sint_eq; reflexivity.
  - unfold sint_add.
    case (px =? ny) as [ | ]eqn:H_eqb_px_ny.
    + Search (Nat.eqb).
      rewrite -> (Nat.eqb_sym px ny) in H_eqb_px_ny.
      rewrite -> H_eqb_px_ny.
      reflexivity.
    + case (px <? ny) as [ | ]eqn:H_ltb_px_ny.
      -- rewrite -> (Nat.eqb_sym px ny) in H_eqb_px_ny. 
         rewrite -> H_eqb_px_ny.
         (* wanted: (ny <? px) = false *)
         Search (Nat.ltb).
         destruct (Nat.ltb_ge ny px) as [_ H_ge_to_ltb_false].
         (* wanted: px <= ny *)
         destruct (Nat.ltb_lt px ny) as [H_ltb_true_to_lt _].
         Check (H_ltb_true_to_lt H_ltb_px_ny).
         Search (_ < _ -> _ <= _).
         Check (Nat.lt_le_incl
                  px ny (H_ltb_true_to_lt H_ltb_px_ny)).
         Check (H_ge_to_ltb_false
                  (Nat.lt_le_incl px ny (H_ltb_true_to_lt H_ltb_px_ny))).
         rewrite -> (H_ge_to_ltb_false
                       (Nat.lt_le_incl px ny (H_ltb_true_to_lt H_ltb_px_ny))).
         reflexivity.
      -- rewrite -> (Nat.eqb_sym px ny) in H_eqb_px_ny. 
         rewrite -> H_eqb_px_ny.
         (* wanted: (ny <? px) = true *)
         Search (Nat.ltb).
         destruct (Nat.ltb_lt ny px) as [_ H_lt_to_ltb_true].
         (* wanted: ny < px *)
         destruct (Nat.ltb_ge px ny) as [H_ltb_false_to_ge _].
         assert (H_le_ny_px := H_ltb_false_to_ge H_ltb_px_ny).
         clear H_ltb_false_to_ge.
         Search (_ <= _ /\ _ <> _).
         destruct (Nat.le_neq ny px) as [_ H_le_neq].
         (* wanted: ny <> px *)
         Search (Nat.eqb).
         assert (H_neq_ny_px := beq_nat_false ny px H_eqb_px_ny).
         clear H_eqb_px_ny.
         Search (_ -> _ -> _ /\ _).
         assert (H_lt_ny_px := H_le_neq (conj H_le_ny_px H_neq_ny_px)).
         clear H_le_ny_px.
         clear H_neq_ny_px.
         clear H_le_neq.
         rewrite -> (H_lt_to_ltb_true H_lt_ny_px).
         (* Potentially interesting: that reflexivity works here... detects
          * structural equality?? How *)
         reflexivity.
  - unfold sint_add, sint_eq; reflexivity.
  - unfold sint_add, sint_eq; reflexivity.
  - unfold sint_add, sint_eq; reflexivity.
  - unfold sint_add.
    case (nx =? py) as [ | ]eqn:H_eqb_nx_py.
    + Search (Nat.eqb).
      rewrite -> (Nat.eqb_sym nx py) in H_eqb_nx_py.
      rewrite -> H_eqb_nx_py.
      reflexivity.
    + case (nx <? py) as [ | ]eqn:H_ltb_nx_py.
      -- rewrite -> (Nat.eqb_sym nx py) in H_eqb_nx_py. 
         rewrite -> H_eqb_nx_py.
         (* wanted: (py <? nx) = false *)
         Search (Nat.ltb).
         destruct (Nat.ltb_ge py nx) as [_ H_ge_to_ltb_false].
         (* wanted: nx <= py *)
         destruct (Nat.ltb_lt nx py) as [H_ltb_true_to_lt _].
         Check (H_ltb_true_to_lt H_ltb_nx_py).
         Search (_ < _ -> _ <= _).
         Check (Nat.lt_le_incl
                  nx py (H_ltb_true_to_lt H_ltb_nx_py)).
         Check (H_ge_to_ltb_false
                  (Nat.lt_le_incl nx py (H_ltb_true_to_lt H_ltb_nx_py))).
         rewrite -> (H_ge_to_ltb_false
                       (Nat.lt_le_incl nx py (H_ltb_true_to_lt H_ltb_nx_py))).
         reflexivity.
      -- rewrite -> (Nat.eqb_sym nx py) in H_eqb_nx_py. 
         rewrite -> H_eqb_nx_py.
         (* wanted: (py <? nx) = true *)
         Search (Nat.ltb).
         destruct (Nat.ltb_lt py nx) as [_ H_lt_to_ltb_true].
         (* wanted: py < nx *)
         destruct (Nat.ltb_ge nx py) as [H_ltb_false_to_ge _].
         assert (H_le_py_nx := H_ltb_false_to_ge H_ltb_nx_py).
         clear H_ltb_false_to_ge.
         Search (_ <= _ /\ _ <> _).
         destruct (Nat.le_neq py nx) as [_ H_le_neq].
         (* wanted: py <> nx *)
         Search (Nat.eqb).
         assert (H_neq_py_nx := beq_nat_false py nx H_eqb_nx_py).
         clear H_eqb_nx_py.
         Search (_ -> _ -> _ /\ _).
         assert (H_lt_py_nx := H_le_neq (conj H_le_py_nx H_neq_py_nx)).
         clear H_le_py_nx.
         clear H_neq_py_nx.
         clear H_le_neq.
         rewrite -> (H_lt_to_ltb_true H_lt_py_nx).
         reflexivity.
  - unfold sint_add, sint_eq; reflexivity.
  - unfold sint_add, sint_eq; ring.
Qed.

Lemma sint_add_eq_r :
  forall x x' y : sint,
    x == x' ->
    sint_add y x == sint_add y x'.
Proof.
  intros x x' y H_eqx.
  Check (sint_eq_trans (sint_add y x)
                       (sint_add x y)
                       (sint_add x' y)
                       (sint_add_comm y x)
                       (sint_add_eq_l x x' y H_eqx)).
  assert (H_eq_yx_x'y := sint_eq_trans
                           (sint_add y x)
                           (sint_add x y)
                           (sint_add x' y)
                           (sint_add_comm y x)
                           (sint_add_eq_l x x' y H_eqx)).
  exact (sint_eq_trans (sint_add y x)
                       (sint_add x' y)
                       (sint_add y x')
                       H_eq_yx_x'y
                       (sint_add_comm x' y)).
Qed.

Lemma sint_add_0_l :
  forall x : sint,
    sint_add Z x == x.
Proof.
  (intros [px |  | nx];
   unfold sint_add, sint_eq;
   reflexivity).

  Restart.
  
  intro x.
  unfold sint_add.
  exact (sint_eq_refl x).
Qed.

Lemma sint_add_0_r :
  forall x : sint,
    sint_add x Z == x.
Proof.
  (intros [px |  | nx];
   unfold sint_add, sint_eq;
   reflexivity).

  Restart.

  intro x.
  Check (sint_eq_trans (sint_add x Z)
                       (sint_add Z x)
                       x
                       (sint_add_comm x Z)
                       (sint_add_0_l x)).
  exact (sint_eq_trans (sint_add x Z)
                       (sint_add Z x)
                       x
                       (sint_add_comm x Z)
                       (sint_add_0_l x)).
Qed.

Lemma sint_add_assoc_aux_eqb_true :
  forall m n p : nat,
    (n =? p) = true ->
    (m + n + 1 =? p) = false /\
    (m + n + 1 <? p) = false /\
    m + n + 1 - p - 1 = m.
Proof.
  intros m n p H_eqb_n_p.
  assert (H_eq_n_p := beq_nat_true n p H_eqb_n_p).
  (* Basically, if n = p, m + n + 1 > p *)
  rewrite -> H_eq_n_p.
  destruct (Nat.eqb_neq (m + p + 1) p) as [_ H_neq_to_neqb].
  assert (H_lt_p_Sp := Nat.lt_succ_diag_r p).
  rewrite <- Nat.add_1_r in H_lt_p_Sp. 
  Check (Nat.add_le_lt_mono 0 m p (p + 1)
                            (Nat.le_0_l m)
                            H_lt_p_Sp).
  assert (H_lt_mSp_p := Nat.add_le_lt_mono
                             0 m p (p + 1)
                             (Nat.le_0_l m)
                             H_lt_p_Sp).
  clear H_lt_p_Sp.
  rewrite -> Nat.add_assoc in H_lt_mSp_p.
  rewrite -> Nat.add_0_l in H_lt_mSp_p.
  split.
  - rewrite -> (H_neq_to_neqb (Nat.neq_sym
                                 p (m + p + 1)
                                 (Nat.lt_neq p (m + p + 1)
                                             H_lt_mSp_p))).
    reflexivity.
  - split.
    + destruct (Nat.ltb_ge (m + p + 1) p) as [_ H_lt_to_ltb].
      rewrite -> (H_lt_to_ltb (Nat.lt_le_incl p (m + p + 1)
                                              H_lt_mSp_p)).
      reflexivity.
    + rewrite <- Nat.sub_add_distr.
      apply (Nat.add_sub_eq_l (m + p + 1) (p + 1) m).
      rewrite -> Nat.add_comm.
      rewrite -> Nat.add_assoc.
      reflexivity.
Qed.


Lemma contrapositive :
  forall P Q : Prop,
    (P -> Q) ->
    (~Q -> ~P).
Proof.
  intros P Q H_PQ.
  unfold not.
  intros H_notQ H_P.
  exact (H_notQ (H_PQ H_P)).
Qed.

Lemma sint_add_assoc_aux_ltb_true :
  forall m n p : nat,
    (m + n + 1 =? p) = true ->
    (m =? p - n - 1) = true.
Proof.
  intros m n p H_eqb_mn1_p.
  Search (Nat.eqb).
  assert (H_eq_mn1_p := beq_nat_true (m + n + 1) p H_eqb_mn1_p).
  Search (_ + _ = _ - _).
  Check (Nat.add_sub_eq_l p n (m + 1)).
  rewrite -> (Nat.add_comm m n) in H_eq_mn1_p.
  rewrite <- Nat.add_assoc in H_eq_mn1_p.
  assert (H_tmp := Nat.add_sub_eq_l p n (m + 1) H_eq_mn1_p).
  Check (Nat.add_sub_eq_l (p - n) 1 m).
  apply (eq_sym) in H_tmp.
  rewrite -> Nat.add_comm in H_tmp.
  Check (Nat.add_sub_eq_l (p - n) 1 m H_tmp).
  destruct (Nat.eqb_eq m (p - n - 1)) as [_ H_eq_to_eqb].
  exact (H_eq_to_eqb (eq_sym (Nat.add_sub_eq_l (p - n) 1 m H_tmp))).
Qed.

Corollary sint_add_assoc_aux_ltb_true_reverse :
  forall m n p : nat,
    (n <? p) = true ->
    (m =? p - n - 1) = true ->
    (m + n + 1 =? p) = true.
Proof.
  intros m n p H_ltb H_eqb.
  assert (H_eq := beq_nat_true m (p - n - 1) H_eqb);
    clear H_eqb.
  rewrite <- Nat.sub_add_distr in H_eq.
  rewrite -> Nat.add_1_r in H_eq.
  assert (H_cancel := f_equal2_plus
                        m (p - S n) (S n) (S n)
                        H_eq (Nat.eq_refl (S n)));
    clear H_eq.
  destruct (Nat.ltb_lt n p) as [H_ltb_to_lt _].
  assert (H_lt := H_ltb_to_lt H_ltb);
    clear H_ltb_to_lt; clear H_ltb.
  rewrite -> (Nat.sub_add
                (S n) p (lt_le_S n p H_lt)) in H_cancel.
  rewrite <- Nat.add_1_r in H_cancel.
  rewrite -> Nat.add_assoc in H_cancel.
  Search (Nat.eqb).
  destruct (Nat.eqb_eq (m + n + 1) p) as [_ H_eq_to_eqb].
  exact (H_eq_to_eqb H_cancel).
Qed.

Lemma sint_add_assoc_aux_ltb_true_ltb_true :
  forall m n p : nat,
    (n <? p) = true ->
    (m + n + 1 =? p) = false ->
    (m + n + 1 <? p) = true ->
    
    (m =? p - n - 1) = false /\
    (m <? p - n - 1) = true /\
    p - (m + n + 1) - 1 = p - n - 1 - m - 1.
Proof.
  intros m n p H_ltb_n_p H_eqb_mn1_p H_ltb_mn1_p.
  split.
  - Check (contrapositive
             ((m =? p - n - 1) = true)
             ((m + n + 1 =? p) = true)
             (sint_add_assoc_aux_ltb_true_reverse
                m n p H_ltb_n_p)).
    assert (H_rev := contrapositive
                       ((m =? p - n - 1) = true)
                       ((m + n + 1 =? p) = true)
                       (sint_add_assoc_aux_ltb_true_reverse
                          m n p H_ltb_n_p)).
    Search (_ <> true).
    destruct (not_true_iff_false (m =? p - n - 1))
      as [H_neq_to_eq _].
    apply H_neq_to_eq.
    apply H_rev.
    rewrite -> H_eqb_mn1_p.
    Search (_ <> true).
    exact diff_false_true.
  - split.
    + rewrite <- Nat.add_assoc in H_ltb_mn1_p.
      rewrite -> (Nat.add_1_r n) in H_ltb_mn1_p.
      destruct (Nat.ltb_lt (m + S n) p) as [H_ltb_lt _].
      assert (H_lt := H_ltb_lt H_ltb_mn1_p);
        clear H_ltb_lt; clear H_ltb_mn1_p.
      rewrite <- Nat.sub_add_distr.
      rewrite -> Nat.add_1_r.
      destruct (Nat.ltb_lt m (p - S n)) as [_ H_eq_eqb].
      apply H_eq_eqb; clear H_eq_eqb.
      Search (_ < _ - _).
      destruct (Nat.lt_add_lt_sub_r m p (S n))
        as [H_lt_add_lt_sub _].
      exact (H_lt_add_lt_sub H_lt).
    + rewrite <- Nat.add_assoc.
      rewrite -> Nat.add_comm.
      Search (_ - (_ + _)).
      rewrite -> 2 Nat.sub_add_distr.
      reflexivity.
Qed.

Lemma sint_add_assoc_aux_ltb_true_ltb_false :
  forall m n p : nat,
    (n <? p) = true ->
    (m + n + 1 =? p) = false ->
    (m + n + 1 <? p) = false ->
    
    (m =? p - n - 1) = false /\
    (m <? p - n - 1) = false /\
    m + n + 1 - p - 1 = m - (p - n - 1) - 1.
Proof.
  intros m n p H_ltb_n_p H_eqb_mn1_p H_ltb_mn1_p.
  split.
  - assert (H_rev := contrapositive
                       ((m =? p - n - 1) = true)
                       ((m + n + 1 =? p) = true)
                       (sint_add_assoc_aux_ltb_true_reverse
                          m n p H_ltb_n_p)).
    destruct (not_true_iff_false (m =? p - n - 1))
      as [H_neq_to_eq _].
    apply H_neq_to_eq.
    apply H_rev.
    rewrite -> H_eqb_mn1_p.
    exact diff_false_true.
  - destruct (Nat.ltb_lt n p) as [H_ltb_lt _].
    assert (H_lt := H_ltb_lt H_ltb_n_p);
      clear H_ltb_lt; clear H_ltb_n_p.
    destruct (Nat.ltb_ge (m + n + 1) p) as [H_ltb_ge _].
    assert (H_ge := H_ltb_ge H_ltb_mn1_p);
      clear H_ltb_ge; clear H_ltb_mn1_p.
    assert (H_neq := beq_nat_false (m + n + 1) p H_eqb_mn1_p);
      clear H_eqb_mn1_p.
    destruct (Nat.le_neq p (m + n + 1)) as [_ H_le_neq].
    assert (H_gt := H_le_neq
                      (conj H_ge (Nat.neq_sym
                                    (m + n + 1) p H_neq)));
      clear H_le_neq; clear H_ge; clear H_neq.
    split.
    + destruct (Nat.ltb_ge m (p - n - 1)) as [_ H_ltb_ge].
      apply H_ltb_ge; clear H_ltb_ge.
      Search (_ - _ <= _).
      destruct (Nat.le_sub_le_add_r (p - n) m 1) as [_ H_le_add_le_sub_1].
      apply H_le_add_le_sub_1; clear H_le_add_le_sub_1.
      destruct (Nat.le_sub_le_add_r p (m + 1) n) as [_ H_le_add_le_sub_2].
      apply H_le_add_le_sub_2; clear H_le_add_le_sub_2.
      rewrite <- Nat.add_assoc.
      rewrite -> (Nat.add_comm 1 n).
      rewrite -> Nat.add_assoc.
      exact (Nat.lt_le_incl p (m + n + 1) H_gt).
    + rewrite <- (Nat.sub_add_distr m).
      Check (Nat.sub_add 1 (p - n)).
      Search (_ < _ - _).
      destruct (Nat.lt_add_lt_sub_r 0 p n)
        as [H_lt_add_lt_sub _].
      rewrite -> Nat.add_0_l in H_lt_add_lt_sub.
      assert (H_lt_0_pn := H_lt_add_lt_sub H_lt);
        clear H_lt_add_lt_sub.
      rewrite -> (Nat.sub_add 1 (p - n)
                              (lt_le_S 0 (p - n) H_lt_0_pn));
        clear H_lt_0_pn.
      Search (_ - _ + _).
      rewrite -> (Nat.add_comm (m + n)).
      rewrite -> Nat.sub_1_r.
      Search (_ + _ - _).
      Check (Nat.add_sub_assoc 1 (m + n) p).
      Search (_ < S _).
      rewrite -> Nat.add_1_r in H_gt.
      assert (H_ge_S := lt_n_Sm_le p (m + n) H_gt).
      rewrite <- (Nat.add_sub_assoc 1 (m + n) p H_ge_S).
      rewrite -> Nat.add_1_l.
      Search (Nat.pred _).
      rewrite -> Nat.pred_succ.
      Search (_ + _ = _ + _).
      destruct (Nat.add_cancel_r
                  (m + n - p) (m - (p - n)) (p - n))
        as [H_add_cancel _].
      apply H_add_cancel; clear H_add_cancel.
      Search (_ - _ <= _).
      destruct (Nat.le_sub_le_add_r p m n)
        as [_ H_le_add_le_sub].
      assert (H_le_sub := H_le_add_le_sub H_ge_S);
        clear H_le_add_le_sub.
      rewrite -> (Nat.sub_add (p - n) m H_le_sub).
      Search (_ + _ - _).
      rewrite -> (Nat.add_sub_assoc
                    (m + n - p) p n (Nat.lt_le_incl n p H_lt)).
      rewrite -> (Nat.sub_add p (m + n) H_ge_S).
      exact (Nat.add_sub m n).
Qed.

Lemma sint_add_assoc_aux_ltb_false :
  forall m n p : nat,
    (n =? p) = false ->
    (n <? p) = false ->
    (m + n + 1 =? p) = false /\
    (m + n + 1 <? p) = false /\
    m + n + 1 - p - 1 = m + (n - p - 1) + 1.
Proof.
  intros m n p H_eqb_n_p H_ltb_n_p.
  assert (H_neq_n_p := beq_nat_false n p H_eqb_n_p).
  Search (Nat.ltb).
  (* Basically, if n > p, then m + n + 1 <> p and > p *)
  destruct (Nat.ltb_ge n p) as [H_ltb_false_to_ge _].
  assert (H_ge_n_p := H_ltb_false_to_ge H_ltb_n_p).
  clear H_ltb_n_p.
  clear H_ltb_false_to_ge.
  Search (_ <= _ /\ _ <> _).
  destruct (Nat.le_neq p n) as [_ H_le_neq_to_lt].
  Search (_ <> _ -> _ <> _).
  assert (H_lt_p_n :=
            H_le_neq_to_lt
              (conj H_ge_n_p
                    (not_eq_sym H_neq_n_p))).
  clear H_neq_n_p; clear H_ge_n_p; clear H_le_neq_to_lt.
  (* wanted: m + n + 1 <> p *)
  Search (_ < _ -> _ + _ < _ + _).
  Check (Nat.add_le_lt_mono 0 m p n
                            (Nat.le_0_l m)
                            H_lt_p_n).
  assert (H_lt_p_mn := Nat.add_le_lt_mono
                            0 m p n
                            (Nat.le_0_l m)
                            H_lt_p_n).
  rewrite -> Nat.add_0_l in H_lt_p_mn.
  assert (H_lt_p_mn1 := Nat.add_lt_le_mono
                             p (m + n) 0 1
                             H_lt_p_mn
                             (Nat.le_0_l 1)).
  clear H_lt_p_mn.
  rewrite -> Nat.add_0_r in H_lt_p_mn1.
  Search (_ < _ -> _ <> _).
  assert (H_neq_mn1_p :=
            not_eq_sym 
              (Nat.lt_neq p (m + n + 1)
                          H_lt_p_mn1)).
  Search (Nat.eqb).
  destruct (Nat.eqb_neq (m + n + 1) p) as [_ H_neq_to_eqb_false].
  split.
  - rewrite -> (H_neq_to_eqb_false H_neq_mn1_p).
    clear H_neq_to_eqb_false; clear H_neq_mn1_p.
    reflexivity.
  - split.
    + Search (Nat.ltb).
      destruct (Nat.ltb_ge (m + n + 1) p) as [_ H_ge_to_ltb_false].
      Search (_ < _ -> _ <= _).
      rewrite -> (H_ge_to_ltb_false
                    (Nat.lt_le_incl p (m + n + 1) H_lt_p_mn1)).
      clear H_lt_p_mn1; clear H_ge_to_ltb_false.
      reflexivity.
      (* wanted: m + n + 1 - p - 1 = m + (n - p - 1) + 1 *)
    + rewrite -> (Nat.add_comm (m + (n - p - 1)) 1).
      rewrite -> (Nat.add_comm (m + n) 1).
      repeat rewrite -> Nat.add_assoc.
      Search (_ - _ - _).
      repeat rewrite <- Nat.sub_add_distr.
      Search (_ + (_ - _)).
      
      Check (Nat.add_sub_assoc (1 + m) n (p + 1)).
      (* wanted: p + 1 <= n *)
      Search (S _ <= _).
      assert (H_le_Sp_n := lt_le_S p n H_lt_p_n).
      rewrite <- Nat.add_1_r in H_le_Sp_n.
      rewrite -> (Nat.add_sub_assoc
                    (1 + m) n (p + 1) H_le_Sp_n).
      reflexivity.
Qed.

Lemma sint_add_assoc_aux_2P :
  forall px py nz : nat,
    sint_add (sint_add (P px) (P py)) (N nz) ==
    sint_add (P px) (sint_add (P py) (N nz)).
Proof.
  intros px py nz.
  unfold sint_add, sint_eq.
  case (py =? nz) as [ | ] eqn:H_eqb_py_nz.
  - Check (sint_add_assoc_aux_eqb_true px py nz H_eqb_py_nz).
    destruct (sint_add_assoc_aux_eqb_true px py nz H_eqb_py_nz)
      as [H_eqb [H_gtb H_eq_nat]].
    rewrite -> H_eqb.
    rewrite -> H_gtb.
    exact H_eq_nat.   
    
  - case (py <? nz) as [ | ] eqn:H_ltb_py_nz.
    + case (px + py + 1 =? nz) as [ | ] eqn:H_eqb_pxpy1_nz.
      -- Check (sint_add_assoc_aux_ltb_true
                  px py nz H_eqb_pxpy1_nz).
         rewrite -> (sint_add_assoc_aux_ltb_true
                       px py nz H_eqb_pxpy1_nz).
         exact I.
      -- case (px + py + 1 <? nz) as [ | ] eqn:H_ltb_pxpy1_nz.
         ++ Check (sint_add_assoc_aux_ltb_true_ltb_true
                     px py nz H_ltb_py_nz
                     H_eqb_pxpy1_nz H_ltb_pxpy1_nz).
            destruct (sint_add_assoc_aux_ltb_true_ltb_true
                        px py nz H_ltb_py_nz
                        H_eqb_pxpy1_nz H_ltb_pxpy1_nz)
              as [H_eqb [H_ltb H_eq_nat]].
            rewrite -> H_eqb.
            rewrite -> H_ltb.
            exact H_eq_nat.
         ++ Check (sint_add_assoc_aux_ltb_true_ltb_false
                     px py nz H_ltb_py_nz
                     H_eqb_pxpy1_nz H_ltb_pxpy1_nz).
            destruct (sint_add_assoc_aux_ltb_true_ltb_false
                        px py nz H_ltb_py_nz
                        H_eqb_pxpy1_nz H_ltb_pxpy1_nz)
              as [H_eqb [H_ltb H_eq_nat]].
            rewrite -> H_eqb.
            rewrite -> H_ltb.
            exact H_eq_nat.
    + Check (sint_add_assoc_aux_ltb_false
               px py nz H_eqb_py_nz H_ltb_py_nz).
      destruct (sint_add_assoc_aux_ltb_false
                  px py nz H_eqb_py_nz H_ltb_py_nz)
        as [H_eqb [H_ltb H_eq]].
      rewrite -> H_eqb.
      rewrite -> H_ltb.
      exact H_eq.
Qed.

Lemma sint_add_assoc_aux_2N:
  forall nx ny pz : nat,
  sint_add (sint_add (N nx) (N ny)) (P pz) == 
  sint_add (N nx) (sint_add (N ny) (P pz)).
Proof.
  intros nx ny pz.
  unfold sint_add, sint_eq.
  case (ny =? pz) as [ | ] eqn:H_eqb_ny_pz.
  - Check (sint_add_assoc_aux_eqb_true nx ny pz H_eqb_ny_pz).
    destruct (sint_add_assoc_aux_eqb_true nx ny pz H_eqb_ny_pz)
      as [H_eqb [H_gtb H_eq_nat]].
    rewrite -> H_eqb.
    rewrite -> H_gtb.
    exact H_eq_nat.
  - case (ny <? pz) as [ | ] eqn:H_ltb_ny_pz.
    + case (nx + ny + 1 =? pz) as [ | ] eqn:H_eqb_nxny1_pz.
      -- Check (sint_add_assoc_aux_ltb_true
                  nx ny pz H_eqb_nxny1_pz).
         rewrite -> (sint_add_assoc_aux_ltb_true
                       nx ny pz H_eqb_nxny1_pz).
         exact I.
      -- case (nx + ny + 1 <? pz) as [ | ] eqn:H_ltb_nxny1_pz.
         ++ Check (sint_add_assoc_aux_ltb_true_ltb_true
                     nx ny pz H_ltb_ny_pz
                     H_eqb_nxny1_pz H_ltb_nxny1_pz).
            destruct (sint_add_assoc_aux_ltb_true_ltb_true
                        nx ny pz H_ltb_ny_pz
                        H_eqb_nxny1_pz H_ltb_nxny1_pz)
              as [H_eqb [H_ltb H_eq]].
            rewrite -> H_eqb.
            rewrite -> H_ltb.
            exact H_eq.
         ++ Check (sint_add_assoc_aux_ltb_true_ltb_false
                     nx ny pz H_ltb_ny_pz
                     H_eqb_nxny1_pz H_ltb_nxny1_pz).
            destruct (sint_add_assoc_aux_ltb_true_ltb_false
                        nx ny pz H_ltb_ny_pz
                        H_eqb_nxny1_pz H_ltb_nxny1_pz)
              as [H_eqb [H_ltb H_eq]].
            rewrite -> H_eqb.
            rewrite -> H_ltb.
            exact H_eq.
    + Check (sint_add_assoc_aux_ltb_false
               nx ny pz H_eqb_ny_pz H_ltb_ny_pz).
      destruct (sint_add_assoc_aux_ltb_false
                  nx ny pz H_eqb_ny_pz H_ltb_ny_pz)
        as [H_neqb [H_gtb H_eq_nat]].
      rewrite -> H_neqb.
      rewrite -> H_gtb.
      exact H_eq_nat.
Qed.
    
Lemma sint_add_assoc :
  forall x y z : sint,
    sint_add (sint_add x y) z == sint_add x (sint_add y z).
Proof.
  intros [px |  | nx] [py |  | ny] [pz |  | nz].
  - unfold sint_add, sint_eq.
    (* px + py + 1 + pz + 1 = px + (py + pz + 1) + 1 *)
    ring.
  - unfold sint_add, sint_eq; reflexivity.
  - exact (sint_add_assoc_aux_2P px py nz).
  - unfold sint_add, sint_eq; reflexivity.
  - unfold sint_add, sint_eq; reflexivity.
  - Check (sint_add_0_r (P px)).
    exact (sint_eq_trans (sint_add (sint_add (P px) Z) (N nz))
                         (sint_add (P px) (N nz))
                         (sint_add (P px) (sint_add Z (N nz)))
                         (sint_add_eq_l (sint_add (P px) Z) (P px) (N nz)
                                        (sint_add_0_r (P px)))
                         (sint_add_eq_r (N nz) (sint_add Z (N nz)) (P px)
                                        (sint_add_0_l (N nz)))).
  - Check (sint_add_assoc_aux_2P pz px ny).
    assert (H_lhs := sint_eq_trans
                       (sint_add (sint_add (P px) (N ny)) (P pz))
                       (sint_add (P pz) (sint_add (P px) (N ny)))
                       (sint_add (sint_add (P pz) (P px)) (N ny))
                       (sint_add_comm (sint_add (P px) (N ny)) (P pz))
                       (sint_eq_sym
                          (sint_add (sint_add (P pz) (P px)) (N ny))
                          (sint_add (P pz) (sint_add (P px) (N ny)))
                          (sint_add_assoc_aux_2P pz px ny))). 
    Check (sint_add_assoc_aux_2P px pz ny).
    assert (H_ltr := sint_eq_trans
                       (sint_add (sint_add (P pz) (P px)) (N ny))
                       (sint_add (sint_add (P px) (P pz)) (N ny))
                       (sint_add (P px) (sint_add (P pz) (N ny)))
                       (sint_add_eq_l
                          (sint_add (P pz) (P px))
                          (sint_add (P px) (P pz))
                          (N ny) (sint_add_comm (P pz) (P px)))
                       (sint_add_assoc_aux_2P px pz ny)).
    assert (H_rhs := sint_eq_trans
                       (sint_add (sint_add (P pz) (P px)) (N ny))
                       (sint_add (P px) (sint_add (P pz) (N ny)))
                       (sint_add (P px) (sint_add (N ny) (P pz)))
                       H_ltr
                       (sint_add_eq_r
                          (sint_add (P pz) (N ny))
                          (sint_add (N ny) (P pz))
                          (P px) (sint_add_comm (P pz) (N ny))));
      clear H_ltr.
    exact (sint_eq_trans
             (sint_add (sint_add (P px) (N ny)) (P pz))
             (sint_add (sint_add (P pz) (P px)) (N ny))
             (sint_add (P px) (sint_add (N ny) (P pz)))
             H_lhs H_rhs).
  - exact (sint_eq_trans (sint_add (sint_add (P px) (N ny)) Z)
                         (sint_add (P px) (N ny))
                         (sint_add (P px) (sint_add (N ny) Z))
                         (sint_add_0_r (sint_add (P px) (N ny)))
                         (sint_add_eq_r (N ny) (sint_add (N ny) Z) (P px)
                                        (sint_add_0_r (N ny)))).
  - Check (sint_add_assoc_aux_2N nz ny px).
    assert (H_lhs := sint_eq_trans
                       (sint_add (sint_add (P px) (N ny)) (N nz))
                       (sint_add (N nz) (sint_add (P px) (N ny)))
                       (sint_add (N nz) (sint_add (N ny) (P px)))
                       (sint_add_comm (sint_add (P px) (N ny)) (N nz))
                       (sint_add_eq_r (sint_add (P px) (N ny))
                                      (sint_add (N ny) (P px))
                                      (N nz)
                                      (sint_add_comm (P px) (N ny)))).
    assert (H_ltr := sint_eq_trans
                       (sint_add (sint_add (P px) (N ny)) (N nz))
                       (sint_add (N nz) (sint_add (N ny) (P px)))
                       (sint_add (sint_add (N nz) (N ny)) (P px))
                       H_lhs
                       (sint_eq_sym
                          (sint_add (sint_add (N nz) (N ny)) (P px))
                          (sint_add (N nz) (sint_add (N ny) (P px)))
                          (sint_add_assoc_aux_2N nz ny px))).
    assert (H_rhs := sint_eq_trans
                       (sint_add (sint_add (N nz) (N ny)) (P px))
                       (sint_add (P px) (sint_add (N nz) (N ny)))
                       (sint_add (P px) (sint_add (N ny) (N nz)))
                       (sint_add_comm (sint_add (N nz) (N ny)) (P px))
                       (sint_add_eq_r (sint_add (N nz) (N ny))
                                      (sint_add (N ny) (N nz))
                                      (P px)
                                      (sint_add_comm (N nz) (N ny)))).
    exact (sint_eq_trans
             (sint_add (sint_add (P px) (N ny)) (N nz))
             (sint_add (sint_add (N nz) (N ny)) (P px))
             (sint_add (P px) (sint_add (N ny) (N nz)))
             H_ltr H_rhs).
  - unfold sint_add, sint_eq; reflexivity.
  - unfold sint_add, sint_eq; reflexivity.
  - exact (sint_eq_trans (sint_add (sint_add Z (P py)) (N nz))
                         (sint_add (P py) (N nz))
                         (sint_add Z (sint_add (P py) (N nz)))
                         (sint_add_eq_l (sint_add Z (P py)) (P py) (N nz)
                                        (sint_add_0_l (P py)))
                         (sint_eq_sym
                            (sint_add (P py) (N nz))
                            (sint_add Z (sint_add (P py) (N nz)))
                            (sint_add_0_l (sint_add (P py) (N nz))))).
  - unfold sint_add, sint_eq; reflexivity.
  - unfold sint_add, sint_eq; reflexivity.
  - unfold sint_add, sint_eq; reflexivity.
  - exact (sint_eq_trans (sint_add (sint_add Z (N ny)) (P pz))
                         (sint_add (N ny) (P pz))
                         (sint_add Z (sint_add (N ny) (P pz)))
                         (sint_add_eq_l (sint_add Z (N ny)) (N ny) (P pz)
                                        (sint_add_0_l (N ny)))
                         (sint_eq_sym
                            (sint_add (N ny) (P pz))
                            (sint_add Z (sint_add (N ny) (P pz)))
                            (sint_add_0_l (sint_add (N ny) (P pz))))).
  - unfold sint_add, sint_eq; reflexivity.
  - unfold sint_add, sint_eq; reflexivity.
  - Check (sint_add_assoc_aux_2P pz py nx).
    (* sint_add (sint_add (P pz) (P py)) (N nx) ==
     * sint_add (P pz) (sint_add (P py) (N nx)) *)
    assert (H_lhs := sint_eq_trans
                       (sint_add (sint_add (N nx) (P py)) (P pz))
                       (sint_add (P pz) (sint_add (N nx) (P py)))
                       (sint_add (P pz) (sint_add (P py) (N nx)))
                       (sint_add_comm (sint_add (N nx) (P py)) (P pz))
                       (sint_add_eq_r (sint_add (N nx) (P py))
                                      (sint_add (P py) (N nx))
                                      (P pz)
                                      (sint_add_comm (N nx) (P py)))).
    assert (H_ltr := sint_eq_trans
                       (sint_add (sint_add (N nx) (P py)) (P pz))
                       (sint_add (P pz) (sint_add (P py) (N nx)))
                       (sint_add (sint_add (P pz) (P py)) (N nx))
                       H_lhs
                       (sint_eq_sym
                          (sint_add (sint_add (P pz) (P py)) (N nx))
                          (sint_add (P pz) (sint_add (P py) (N nx)))
                          (sint_add_assoc_aux_2P pz py nx))).
    assert (H_rhs := sint_eq_trans
                       (sint_add (sint_add (P pz) (P py)) (N nx))
                       (sint_add (N nx) (sint_add (P pz) (P py)))
                       (sint_add (N nx) (sint_add (P py) (P pz)))
                       (sint_add_comm (sint_add (P pz) (P py)) (N nx))
                       (sint_add_eq_r (sint_add (P pz) (P py))
                                      (sint_add (P py) (P pz))
                                      (N nx)
                                      (sint_add_comm (P pz) (P py)))).
    exact (sint_eq_trans
             (sint_add (sint_add (N nx) (P py)) (P pz))
             (sint_add (sint_add (P pz) (P py)) (N nx))
             (sint_add (N nx) (sint_add (P py) (P pz)))
             H_ltr H_rhs).
  (* sint_add (sint_add (N nx) (P py)) (P pz) == 
   * sint_add (N nx) (sint_add (P py) (P pz)) *)
  (* 2 *)
  - exact (sint_eq_trans (sint_add (sint_add (N nx) (P py)) Z)
                         (sint_add (N nx) (P py))
                         (sint_add (N nx) (sint_add (P py) Z))
                         (sint_add_0_r (sint_add (N nx) (P py)))
                         (sint_add_eq_r (P py) (sint_add (P py) Z) (N nx)
                                        (sint_eq_sym
                                           (sint_add (P py) Z) (P py)
                                           (sint_add_0_r (P py))))).
  - Check (sint_add_assoc_aux_2N nz nx py).
    assert (H_lhs := sint_eq_trans
                       (sint_add (sint_add (N nx) (P py)) (N nz))
                       (sint_add (N nz) (sint_add (N nx) (P py)))
                       (sint_add (sint_add (N nz) (N nx)) (P py))
                       (sint_add_comm (sint_add (N nx) (P py)) (N nz))
                       (sint_eq_sym
                          (sint_add (sint_add (N nz) (N nx)) (P py))
                          (sint_add (N nz) (sint_add (N nx) (P py)))
                          (sint_add_assoc_aux_2N nz nx py))).
    Check (sint_add_assoc_aux_2N nx nz py).
    assert (H_ltr := sint_eq_trans
                       (sint_add (sint_add (N nz) (N nx)) (P py))
                       (sint_add (sint_add (N nx) (N nz)) (P py))
                       (sint_add (N nx) (sint_add (N nz) (P py)))
                       (sint_add_eq_l
                          (sint_add (N nz) (N nx))
                          (sint_add (N nx) (N nz))
                          (P py) (sint_add_comm (N nz) (N nx)))
                       (sint_add_assoc_aux_2N nx nz py)).
    assert (H_rhs := sint_eq_trans
                       (sint_add (sint_add (N nz) (N nx)) (P py))
                       (sint_add (N nx) (sint_add (N nz) (P py)))
                       (sint_add (N nx) (sint_add (P py) (N nz)))
                       H_ltr
                       (sint_add_eq_r
                          (sint_add (N nz) (P py))
                          (sint_add (P py) (N nz))
                          (N nx) (sint_add_comm (N nz) (P py))));
      clear H_ltr.
    exact (sint_eq_trans
             (sint_add (sint_add (N nx) (P py)) (N nz))
             (sint_add (sint_add (N nz) (N nx)) (P py))
             (sint_add (N nx) (sint_add (P py) (N nz)))
             H_lhs H_rhs).                          
  (* sint_add (sint_add (N nx) (P py)) (N nz) == 
   * sint_add (N nx) (sint_add (P py) (N nz)) *)
  (* 2 *)
  - exact (sint_eq_trans (sint_add (sint_add (N nx) Z) (P pz))
                         (sint_add (N nx) (P pz))
                         (sint_add (N nx) (sint_add Z (P pz)))
                         (sint_add_eq_l (sint_add (N nx) Z) (N nx) (P pz)
                                        (sint_add_0_r (N nx)))
                         (sint_add_eq_r (P pz) (sint_add Z (P pz)) (N nx)
                                        (sint_eq_sym (sint_add Z (P pz)) (P pz)
                                                     (sint_add_0_l (P pz))))).
  - unfold sint_add, sint_eq; reflexivity.
  - unfold sint_add, sint_eq; reflexivity.
  - exact (sint_add_assoc_aux_2N nx ny pz).
  (* sint_add (sint_add (N nx) (N ny)) (P pz) == 
   * sint_add (N nx) (sint_add (N ny) (P pz)) *)
  (* 2 *)
  - unfold sint_add, sint_eq; reflexivity.
  - unfold sint_add, sint_eq; ring.
    (* nx + ny + 1 + nz + 1 = nx + (ny + nz + 1) + 1 *)
Qed.

Lemma sint_lt_trichotomy :
  forall x : sint,
  exists n : nat,
    x == P n \/
    x == Z \/
    x == N n.
Proof.
  intros [px |  | nx].
  - exists px.
    left.
    reflexivity.
  - exists 0; right; left; reflexivity.
  - exists nx; right; right; reflexivity.

  Restart.

  (intros [px |  | nx];
   (* Potentially interesting: that exists 0 is the last case here, not in order *)
   (exists px || exists nx || exists 0);
   ((left; reflexivity) ||
    (right; left; reflexivity) ||
    (right; right; reflexivity))).
Qed.


(* ********** *)

Definition sint_neg (x : sint) : sint :=
  match x with
  | P n => N n
  | Z => Z
  | N n => P n
  end.

Lemma sint_add_neg_of_itself_l :
  forall x : sint,
    sint_add (sint_neg x) x == Z.
Proof.
  intros [px |  | nx].
  - unfold sint_neg, sint_add.
    Search (Nat.eqb).
    rewrite -> Nat.eqb_refl.
    reflexivity.
  - unfold sint_neg, sint_add.
    reflexivity.
  - unfold sint_neg, sint_add.
    rewrite -> Nat.eqb_refl.
    reflexivity.

  Restart.

  (intros [px |  | nx];
   unfold sint_neg, sint_add;
   (reflexivity || (rewrite -> Nat.eqb_refl; reflexivity))).
Qed.

Lemma sint_add_neg_of_itself_r :
  forall x : sint,
    sint_add x (sint_neg x) == Z.
Proof.
  (intros [px |  | nx];
   unfold sint_neg, sint_add;
   (reflexivity || (rewrite -> Nat.eqb_refl; reflexivity))).

  Restart.

  intro x.
  Check (sint_eq_trans (sint_add x (sint_neg x))
                       (sint_add (sint_neg x) x)
                       Z
                       (sint_add_comm x (sint_neg x))
                       (sint_add_neg_of_itself_l x)).
  exact (sint_eq_trans (sint_add x (sint_neg x))
                       (sint_add (sint_neg x) x)
                       Z
                       (sint_add_comm x (sint_neg x))
                       (sint_add_neg_of_itself_l x)).
Qed.

(* ********** *)

Definition sint_mul (i1 i2 : sint) : sint := 
  match i1 with
  | P n1 =>
    match i2 with
    | P n2 =>
      P (S n1 * S n2 - 1)
    | Z =>
      Z
    | N n2 =>
      N (S n1 * S n2 - 1)
    end
  | Z => Z
  | N n1 =>
    match i2 with
    | P n2 => N (S n1 * S n2 - 1)
    | Z => Z
    | N n2 => P (S n1 * S n2 - 1)
    end
  end.

Lemma sint_mul_eq_l :
  forall x x' y : sint,
    x == x' ->
    sint_mul x y == sint_mul x' y.
Proof.
  intros [px |  | nx] [px' |  | nx'] [py |  | ny];
    unfold sint_mul, sint_eq; intro H_eqx;
      ((rewrite -> H_eqx; reflexivity) || contradiction H_eqx || trivial).
Qed.

Lemma sint_mul_comm :
  forall x y : sint,
    sint_mul x y == sint_mul y x.
Proof.
  (intros [px |  | nx] [py |  | ny];
   unfold sint_mul, sint_eq;
   ((rewrite -> Nat.mul_comm; reflexivity) || trivial)).
Qed.
   
Lemma sint_mul_eq_r :
  forall x x' y : sint,
    x == x' ->
    sint_mul y x == sint_mul y x'.
Proof.
  intros [px |  | nx] [px' |  | nx'] [py |  | ny];
    unfold sint_mul, sint_eq; intro H_eqx;
      ((rewrite -> H_eqx; reflexivity) || contradiction H_eqx || trivial).

  Restart.

  intros x x' y H_eqx.
  Check (sint_eq_trans (sint_mul y x)
                       (sint_mul x y)
                       (sint_mul x' y)
                       (sint_mul_comm y x)
                       (sint_mul_eq_l x x' y H_eqx)).
  assert (H_eq_yx_x'y :=
            sint_eq_trans (sint_mul y x)
                          (sint_mul x y)
                          (sint_mul x' y)
                          (sint_mul_comm y x)
                          (sint_mul_eq_l x x' y H_eqx)).
  exact (sint_eq_trans (sint_mul y x)
                       (sint_mul x' y)
                       (sint_mul y x')
                       H_eq_yx_x'y
                       (sint_mul_comm x' y)).
Qed.

Lemma le_1_SmSn :
  forall m n : nat,
    1 <= S m * S n.
Proof.
  intros m n.
  assert (H_le_0_m := Nat.le_0_l m).
  assert (H_le_0_n := Nat.le_0_l n).
  assert (H_le_1_Sm := plus_le_compat_r 0 m 1 H_le_0_m).
  rewrite -> Nat.add_0_l in H_le_1_Sm;
    rewrite -> Nat.add_1_r in H_le_1_Sm.
  assert (H_le_1_Sn := plus_le_compat_r 0 n 1 H_le_0_n).
  rewrite -> Nat.add_0_l in H_le_1_Sn;
    rewrite -> Nat.add_1_r in H_le_1_Sn.
  clear H_le_0_m; clear H_le_0_n.
  assert (H_le_1_SmSn := Nat.mul_le_mono
                             1 (S m) 1 (S n)
                             H_le_1_Sm H_le_1_Sn).
  clear H_le_1_Sm; clear H_le_1_Sn.
  rewrite -> Nat.mul_1_l in H_le_1_SmSn.
  exact H_le_1_SmSn.
Qed.  

(* wanted: S (S px * S ny - 1) * S pz - 1 = S px * S (S ny * S pz - 1) - 1 *)
Lemma sint_mul_assoc_aux :
  forall m n p : nat,
    S (S m * S n - 1) * S p - 1 = S m * S (S n * S p - 1) - 1.
Proof.
  intros m n p.
  Search (_ - _ = _).
  Check (minus_plus 1 (S m * S n)).
  
  (* Simplifying LHS *)
  (* wanted: 1 + S m * S n - 1 *)
  rewrite <- (Nat.add_1_l (S m * S n - 1)).
  Search (_ + (_ - _)).
  Check (Nat.add_sub_assoc 1 (S m * S n) 1).
  (* wanted: 1 <= S m * S n *)
  rewrite -> (Nat.add_sub_assoc 1 (S m * S n) 1
                                (le_1_SmSn m n)).
  rewrite -> (minus_plus 1 (S m * S n)).

  (* Simplifying RHS *)
  rewrite <- (Nat.add_1_l (S n * S p - 1)).
  rewrite -> (Nat.add_sub_assoc 1 (S n * S p) 1
                                (le_1_SmSn n p)).
  rewrite -> (minus_plus 1 (S n * S p)).
  rewrite -> Nat.mul_assoc.
  reflexivity.
Qed.

Lemma sint_mul_assoc :
  forall x y z : sint,
    sint_mul (sint_mul x y) z == sint_mul x (sint_mul y z).
Proof.
  (intros [px |  | nx] [py |  | ny] [pz |  | nz];
   unfold sint_mul, sint_eq;
   (trivial ||
    exact (sint_mul_assoc_aux px py pz) ||
    exact (sint_mul_assoc_aux px py nz) ||
    exact (sint_mul_assoc_aux px ny pz) ||
    exact (sint_mul_assoc_aux px ny nz) ||
    exact (sint_mul_assoc_aux nx py pz) ||
    exact (sint_mul_assoc_aux nx py nz) ||
    exact (sint_mul_assoc_aux nx ny pz) ||
    exact (sint_mul_assoc_aux nx ny nz))).
Qed.

Lemma sint_mul_1_l :
  forall x : sint,
    sint_mul (P 0) x == x.
Proof.
  (intros [px |  | nx];
   unfold sint_mul, sint_eq;
   ((rewrite -> Nat.mul_1_l;
     rewrite <- Nat.add_1_l;
     rewrite -> minus_plus;
     reflexivity) || trivial)).
Qed.

Lemma sint_mul_1_r :
  forall x : sint,
    sint_mul x (P 0) == x.
Proof.
  (intros [px |  | nx];
   unfold sint_mul, sint_eq;
   (* Note: only one should be changed to _r from _l,
    * need to add 1 on the left for minus_plus to work *)
   ((rewrite -> Nat.mul_1_r;
     rewrite <- Nat.add_1_l;
     rewrite -> minus_plus;
     reflexivity) || trivial)).

  Restart.

  intro x.
  exact (sint_eq_trans (sint_mul x (P 0))
                       (sint_mul (P 0) x)
                       x
                       (sint_mul_comm x (P 0))
                       (sint_mul_1_l x)).  
Qed.

(* Would it help to have neq_mn_to_neq_pred_SmSn_mul_Sp here? 
 * I assume not much, as you still have to prove < and > here,
 * which gives you <> for cheap... sad *)

Lemma sint_mul_add_distr_aux_plus :
  forall m n p : nat,
    S m * S (n + p + 1) - 1 =
    S m * S n - 1 + (S m * S p - 1) + 1.
Proof.
  intros m n p.
  
  (* Simplifying LHS *)
  Check (Nat.mul_add_distr_l (S m) (S n) (S p)).
  (* wanted: S m * S (n + p + 1) -> S m * (S n + S p) *)
  rewrite <- (Nat.add_assoc n p 1).
  rewrite -> (Nat.add_1_r p).
  rewrite <- (Nat.add_1_l (n + S p)).
  rewrite -> (Nat.add_assoc 1 n (S p)).
  rewrite -> (Nat.add_1_l n).
  rewrite -> (Nat.mul_add_distr_l (S m) (S n) (S p)).

  (* Simplifying RHS *)
  rewrite -> (Nat.add_comm (S m * S n - 1 + (S m * S p - 1)) 1).
  rewrite -> Nat.add_assoc.
  Check (Nat.add_sub_assoc 1 (S m * S n) 1).
  (* wanted: 1 <= S m * S n*)
  rewrite -> (Nat.add_sub_assoc 1 (S m * S n) 1
                                (le_1_SmSn m n)).
  rewrite -> (minus_plus 1 (S m * S n)).

  Check (Nat.add_sub_assoc (S m * S n) (S m * S p) 1).
  (* wanted: 1 <= S m * S p *)
  rewrite -> (Nat.add_sub_assoc (S m * S n) (S m * S p) 1
                                (le_1_SmSn m p)).
  reflexivity.
Qed.

Lemma sint_mul_add_distr_aux_minus :
  forall m n p : nat,
    n < p ->
    S m * S (p - n - 1) - 1 =
    S m * S p - 1 - (S m * S n - 1) - 1.
Proof.
  intros m n p H_lt.

  (* Simplifying LHS *)
  Search (_ - (_ + _)).
  rewrite <- Nat.sub_add_distr.
  rewrite -> Nat.add_1_r.
  Search (S _ = _).
  Check (minus_Sn_m p (S n)).
  Search (S _ <= _).
  rewrite -> (minus_Sn_m p (S n) (lt_le_S n p H_lt)) (*;
    assert (H_lt_S := le_n_S n p (Nat.lt_le_incl n p H_lt))*).
  Search (_ * (_ - _) = _).
  rewrite -> Nat.mul_sub_distr_l.

  (* Simplifying RHS *)
  Search (Nat.sub).
  Check (Nat.sub_add_distr
           (S m * S p - 1) (S m * S n - 1) 1).
  rewrite <- (Nat.sub_add_distr
                (S m * S p - 1) (S m * S n - 1) 1).
  Search (_ - _ + _).
  rewrite -> (Nat.sub_add 1 (S m * S n) (le_1_SmSn m n)).
  rewrite <- (Nat.sub_add_distr (S m * S p) (S m * S n) 1).
  rewrite -> Nat.add_comm.
  rewrite -> Nat.sub_add_distr.
  reflexivity.
Qed.

Lemma sint_mul_add_distr_aux_case_true :
  forall m n p : nat,
    (n <? p) = true -> 
    (S m * S n - 1 =? S m * S p - 1) = false /\
    (S m * S n - 1 <? S m * S p - 1) = true.
Proof.
  intros m n p H_ltb_np.

  (* wanted: S m * S n - 1 < S m * S p - 1; 
   * S m * S n - 1 <> S m * S p - 1 *)
  destruct (Nat.ltb_lt n p) as [H_ltb_to_lt _].
  assert (H_lt_np := H_ltb_to_lt H_ltb_np);
    clear H_ltb_to_lt; clear H_ltb_np.
  Search (_ < _ -> S _ < _).
  assert (H_lt_S := lt_n_S n p H_lt_np).
  Search (_ * _ < _ * _).
  Check (mult_lt_compat_l (S n) (S p) (S m) H_lt_S).
  Search (0 < S _).
  assert (H_lt_Sm := mult_lt_compat_l
                       (S n) (S p) (S m) H_lt_S
                       (Nat.lt_0_succ m));
    clear H_lt_S.
  Search (Nat.pred _ < Nat.pred _).
  Check (Nat.pred_lt_mono (S m * S n) (S m * S p)).
  (* wanted: S m * S n <> 0 *)
  Search (0 < 1).
  Search (_ < _ -> _ <= _ -> _ < _).
  assert (H_0_lt_Sm := Nat.lt_le_trans
                         0 1 (S m * S n)
                         Nat.lt_0_1
                         (le_1_SmSn m n)).
  assert (H_neq := Nat.neq_sym
                     0 (S m * S n)
                     (Nat.lt_neq 0 (S m * S n) H_0_lt_Sm));
    clear H_0_lt_Sm.
  destruct (Nat.pred_lt_mono (S m * S n) (S m * S p) H_neq)
    as [H_lt_to_pred _]; clear H_neq.
  assert (H_pred := H_lt_to_pred H_lt_Sm);
    clear H_lt_to_pred; clear H_lt_Sm.
  Search (_ = _ - 1).
  rewrite -> 2 pred_of_minus in H_pred.
  assert (H_pred_neq := Nat.lt_neq
                          (S m * S n - 1)
                          (S m * S p - 1)
                          H_pred).

  split.
  - Search (Nat.eqb).
    destruct (Nat.eqb_neq (S m * S n - 1) (S m * S p - 1))
      as [_ H_neq_to_eqb].
    exact (H_neq_to_eqb H_pred_neq).
  - destruct (Nat.ltb_lt (S m * S n - 1) (S m * S p - 1))
      as [_ H_lt_to_ltb].
    exact (H_lt_to_ltb H_pred).
Qed.

Lemma sint_mul_add_distr_aux_case_false :
  forall m n p : nat,
    (n =? p) = false /\ (n <? p) = false -> 
    (S m * S n - 1 =? S m * S p - 1) = false /\
    (S m * S n - 1 <? S m * S p - 1) = false.
Proof.
  intros m n p [H_eqb_np H_ltb_np].
  destruct (Nat.ltb_ge n p) as [H_ltb_to_ge _].
  assert (H_le_pn := H_ltb_to_ge H_ltb_np);
    clear H_ltb_to_ge; clear H_ltb_np.
  assert (H_neq_pn := Nat.neq_sym
                        n p (beq_nat_false n p H_eqb_np)).
  destruct (Nat.le_neq p n) as [_ H_le_neq].
  assert (H_lt_pn := H_le_neq (conj H_le_pn H_neq_pn));
    clear H_le_neq; clear H_le_pn; clear H_neq_pn.
  (* copied and rearranged from _case_true *)
  assert (H_lt_S := lt_n_S p n H_lt_pn).
  Check (mult_lt_compat_l (S p) (S n) (S m) H_lt_S).
  assert (H_lt_Sm := mult_lt_compat_l
                       (S p) (S n) (S m) H_lt_S
                       (Nat.lt_0_succ m));
    clear H_lt_S.
  assert (H_0_lt_Sm := Nat.lt_le_trans
                         0 1 (S m * S p)
                         Nat.lt_0_1
                         (le_1_SmSn m p)).
  assert (H_neq := Nat.neq_sym
                     0 (S m * S p)
                     (Nat.lt_neq 0 (S m * S p) H_0_lt_Sm));
    clear H_0_lt_Sm.
  destruct (Nat.pred_lt_mono (S m * S p) (S m * S n) H_neq)
    as [H_lt_to_pred _]; clear H_neq.
  assert (H_pred := H_lt_to_pred H_lt_Sm);
    clear H_lt_to_pred; clear H_lt_Sm.
  rewrite -> 2 pred_of_minus in H_pred.
  assert (H_pred_neq := Nat.lt_neq
                          (S m * S p - 1)
                          (S m * S n - 1)
                          H_pred).
  
  split.
  - destruct (Nat.eqb_neq (S m * S n - 1) (S m * S p - 1))
      as [_ H_neq_to_eqb].
    exact (H_neq_to_eqb (Nat.neq_sym (S m * S p - 1)
                                     (S m * S n - 1)
                                     H_pred_neq)).
  - Search (Nat.ltb).
    destruct (Nat.ltb_ge (S m * S n - 1) (S m * S p - 1))
      as [_ H_ge_to_ltb].
    exact (H_ge_to_ltb (Nat.lt_le_incl (S m * S p - 1)
                                       (S m * S n - 1)
                                       H_pred)).
Qed.

Lemma sint_mul_add_distr_aux_PN_1 :
  forall m n p : nat,
    sint_mul (P m) (sint_add (P n) (N p)) ==
    sint_add (sint_mul (P m) (P n)) (sint_mul (P m) (N p)).
Proof.
  intros m n p.
  unfold sint_mul, sint_add.
  case (n =? p) as [ | ] eqn:H_eqb_np.
  - rewrite -> (beq_nat_true n p H_eqb_np).
    rewrite -> (Nat.eqb_refl (S m * S p - 1)).
    reflexivity.
  - case (n <? p) as [ | ] eqn:H_ltb_np.
    + destruct (sint_mul_add_distr_aux_case_true
                  m n p H_ltb_np) as [H_neq H_ltb].
      rewrite -> H_neq, H_ltb;
        clear H_neq; clear H_ltb.
      Check (sint_mul_add_distr_aux_plus m p n).
      (* wanted: n < p ->
       * S m * S (p - n - 1) - 1 =
       * S m * S p - 1 - (S m * S n - 1) - 1 *)
      destruct (Nat.ltb_lt n p) as [H_ltb_to_lt _].
      Check (sint_mul_add_distr_aux_minus
               m n p (H_ltb_to_lt H_ltb_np)).
      rewrite -> (sint_mul_add_distr_aux_minus
                    m n p (H_ltb_to_lt H_ltb_np)).
      reflexivity.
    + destruct (sint_mul_add_distr_aux_case_false
                  m n p (conj H_eqb_np H_ltb_np)) as [H_neq H_ltb].
      rewrite -> H_neq, H_ltb;
        clear H_neq; clear H_ltb.
      destruct (Nat.ltb_ge n p) as [H_ltb_to_ge _].
      Search (_ /\ _ <> _).
      destruct (Nat.le_neq p n) as [_ H_le_neq].
      assert (H_lt_pn :=
                H_le_neq
                  (conj (H_ltb_to_ge H_ltb_np)
                        (Nat.neq_sym
                           n p (beq_nat_false n p H_eqb_np))));
        clear H_ltb_to_ge; clear H_le_neq.
      rewrite -> (sint_mul_add_distr_aux_minus
                    m p n H_lt_pn).
      reflexivity.
Qed.

Lemma sint_mul_add_distr_aux_PN_2 :
  forall m n p : nat,
    sint_mul (N m) (sint_add (P n) (N p)) ==
    sint_add (sint_mul (N m) (N p)) (sint_mul (N m) (P n)).
Proof.
  intros m n p.
  unfold sint_mul, sint_add.
  case (n =? p) as [ | ] eqn:H_eqb_np.
  - rewrite -> (beq_nat_true n p H_eqb_np).
    rewrite -> (Nat.eqb_refl (S m * S p - 1)).
    reflexivity.
  - case (n <? p) as [ | ] eqn:H_ltb_np.
    + destruct (sint_mul_add_distr_aux_case_true
                  m n p H_ltb_np) as [H_neq H_ltb].
      rewrite -> Nat.eqb_sym in H_neq.
      rewrite -> H_neq.
      Search (_ <? _).
      destruct (Nat.ltb_lt (S m * S n - 1) (S m * S p - 1))
        as [H_ltb_to_lt _].
      assert (H_lt := H_ltb_to_lt H_ltb);
        clear H_ltb; clear H_ltb_to_lt.
      Search (_ < _ -> _ <= _).
      assert (H_leb := leb_correct
                         (S m * S n - 1) (S m * S p - 1)
                         (Nat.lt_le_incl
                            (S m * S n - 1) (S m * S p - 1) H_lt));
        clear H_lt.
      Search (_ <=? _).
      rewrite -> Nat.leb_antisym in H_leb.
      Search (negb).
      destruct (negb_true_iff (S m * S p - 1 <? S m * S n - 1))
        as [H_negb_t_is_f _].
      rewrite -> (H_negb_t_is_f H_leb).
      Check (sint_mul_add_distr_aux_plus m p n).
      (* wanted: n < p -> 
       * S m * S (p - n - 1) - 1 =
       * S m * S p - 1 - (S m * S n - 1) - 1 *)
      destruct (Nat.ltb_lt n p) as [H_ltb_to_lt _].
      rewrite -> (sint_mul_add_distr_aux_minus
                    m n p (H_ltb_to_lt H_ltb_np)).
      reflexivity.
    + destruct (sint_mul_add_distr_aux_case_false
                  m n p (conj H_eqb_np H_ltb_np)) as [H_neq H_ltb].
      rewrite -> Nat.eqb_sym in H_neq.
      rewrite -> H_neq.
      Search (_ <? _).
      destruct (Nat.ltb_ge (S m * S n - 1) (S m * S p - 1))
        as [H_ltb_to_ge _].
      assert (H_le := H_ltb_to_ge H_ltb);
        clear H_ltb; clear H_ltb_to_ge.
      Search (_ <= _ /\ _ <> _).
      destruct (Nat.le_neq (S m * S p - 1) (S m * S n - 1))
        as [_ H_le_neq_to_lt].
      Search (Nat.eqb).
      assert (H_lt := H_le_neq_to_lt 
                        (conj H_le (beq_nat_false
                                      (S m * S p - 1)
                                      (S m * S n - 1)
                                      H_neq)));
        clear H_le; clear H_le_neq_to_lt.
      Search (_ <? _).
      destruct (Nat.ltb_lt (S m * S p - 1) (S m * S n - 1))
        as [_ H_lt_to_ltb].
      rewrite -> (H_lt_to_ltb H_lt).
      (* wanted: p < n ->
       * S m * S (n - p - 1) - 1 =
       * S m * S n - 1 - (S m * S p - 1) - 1 *)
      destruct (Nat.ltb_ge n p) as [H_ltb_to_ge _].
      destruct (Nat.le_neq p n) as [_ H_le_neq].
      assert (H_lt_pn :=
                H_le_neq
                  (conj (H_ltb_to_ge H_ltb_np)
                        (Nat.neq_sym
                           n p (beq_nat_false n p H_eqb_np))));
        clear H_ltb_to_ge; clear H_le_neq.
      rewrite -> (sint_mul_add_distr_aux_minus
                    m p n H_lt_pn).
      reflexivity.
Qed.

Lemma sint_mul_add_distr_l :
  forall x y z : sint,
    sint_mul x (sint_add y z) ==
    sint_add (sint_mul x y) (sint_mul x z).
Proof.
  intros [px |  | nx] [py |  | ny] [pz |  | nz].
  - unfold sint_mul, sint_add, sint_eq.
    exact (sint_mul_add_distr_aux_plus px py pz).
    (* wanted: S px * S (py + pz + 1) - 1 = 
     * S px * S py - 1 + (S px * S pz - 1) + 1 *)
  - reflexivity.
  - exact (sint_mul_add_distr_aux_PN_1 px py nz).
  - unfold sint_mul, sint_add, sint_eq; reflexivity. 
  - unfold sint_mul, sint_add, sint_eq; trivial.
  - unfold sint_mul, sint_add, sint_eq; reflexivity. 
  - Check (sint_mul_add_distr_aux_PN_1 px pz ny).
    Check (sint_mul_eq_r
             (sint_add (N ny) (P pz))
             (sint_add (P pz) (N ny)) (P px)
             (sint_add_comm (N ny) (P pz))).
    assert (H_lhs_eq := sint_mul_eq_r
                          (sint_add (N ny) (P pz))
                          (sint_add (P pz) (N ny)) (P px)
                          (sint_add_comm (N ny) (P pz))).
    assert (H_tmp_eq := sint_eq_trans
                          (sint_mul (P px) (sint_add (N ny) (P pz)))
                          (sint_mul (P px) (sint_add (P pz) (N ny)))
                          (sint_add (sint_mul (P px) (P pz))
                                    (sint_mul (P px) (N ny)))
                          H_lhs_eq
                          (sint_mul_add_distr_aux_PN_1 px pz ny)).
    exact (sint_eq_trans (sint_mul (P px) (sint_add (N ny) (P pz)))
                         (sint_add (sint_mul (P px) (P pz))
                                   (sint_mul (P px) (N ny)))
                         (sint_add (sint_mul (P px) (N ny))
                                   (sint_mul (P px) (P pz)))
                         H_tmp_eq
                         (sint_add_comm (sint_mul (P px) (P pz))
                                        (sint_mul (P px) (N ny)))).
  - unfold sint_mul, sint_add, sint_eq; reflexivity. 
  - unfold sint_mul, sint_add, sint_eq.
    exact (sint_mul_add_distr_aux_plus px ny nz).
  - unfold sint_mul, sint_add, sint_eq; trivial.
  - unfold sint_mul, sint_add, sint_eq; trivial.
  - unfold sint_mul, sint_add, sint_eq; trivial.
  - unfold sint_mul, sint_add, sint_eq; trivial.
  - unfold sint_mul, sint_add, sint_eq; trivial.
  - unfold sint_mul, sint_add, sint_eq; trivial.
  - unfold sint_mul, sint_add, sint_eq; trivial.
  - unfold sint_mul, sint_add, sint_eq; trivial.
  - unfold sint_mul, sint_add, sint_eq; trivial.
  - unfold sint_mul, sint_add, sint_eq.
    exact (sint_mul_add_distr_aux_plus nx py pz).
  - unfold sint_mul, sint_add, sint_eq; reflexivity. 
  - Check (sint_mul_add_distr_aux_PN_2 nx py nz).
    Check (sint_eq_trans
             (sint_mul (N nx) (sint_add (P py) (N nz)))
             (sint_add (sint_mul (N nx) (N nz)) (sint_mul (N nx) (P py)))
             (sint_add (sint_mul (N nx) (P py)) (sint_mul (N nx) (N nz)))
             (sint_mul_add_distr_aux_PN_2 nx py nz)
             (sint_add_comm (sint_mul (N nx) (N nz))
                            (sint_mul (N nx) (P py)))).
    exact (sint_eq_trans
             (sint_mul (N nx) (sint_add (P py) (N nz)))
             (sint_add (sint_mul (N nx) (N nz)) (sint_mul (N nx) (P py)))
             (sint_add (sint_mul (N nx) (P py)) (sint_mul (N nx) (N nz)))
             (sint_mul_add_distr_aux_PN_2 nx py nz)
             (sint_add_comm (sint_mul (N nx) (N nz))
                            (sint_mul (N nx) (P py)))).
  - unfold sint_mul, sint_add, sint_eq; reflexivity. 
  - unfold sint_mul, sint_add, sint_eq; trivial.
  - unfold sint_mul, sint_add, sint_eq; reflexivity. 
  - Check (sint_mul_add_distr_aux_PN_2 nx pz ny).
    Check (sint_mul_eq_r
             (sint_add (N ny) (P pz))
             (sint_add (P pz) (N ny)) (N nx)
             (sint_add_comm (N ny) (P pz))).
    assert (H_lhs_eq := sint_mul_eq_r
                          (sint_add (N ny) (P pz))
                          (sint_add (P pz) (N ny)) (N nx)
                          (sint_add_comm (N ny) (P pz))).
    exact (sint_eq_trans (sint_mul (N nx) (sint_add (N ny) (P pz)))
                         (sint_mul (N nx) (sint_add (P pz) (N ny)))
                         (sint_add (sint_mul (N nx) (N ny))
                                   (sint_mul (N nx) (P pz)))
                         H_lhs_eq
                         (sint_mul_add_distr_aux_PN_2 nx pz ny)).
  - unfold sint_mul, sint_add, sint_eq; reflexivity. 
  - unfold sint_mul, sint_add, sint_eq.
    exact (sint_mul_add_distr_aux_plus nx ny nz).
Qed.

Lemma sint_mul_add_distr_r :
  forall x y z : sint,
    sint_mul (sint_add y z) x ==
    sint_add (sint_mul y x) (sint_mul z x).
Proof.
  intros x y z.
  Check (sint_mul_add_distr_l x y z).
  assert (H_tmp_eq := sint_eq_trans
                        (sint_mul (sint_add y z) x)
                        (sint_mul x (sint_add y z))
                        (sint_add (sint_mul x y) (sint_mul x z))
                        (sint_mul_comm (sint_add y z) x)
                        (sint_mul_add_distr_l x y z)).
  (* wanted: sint_add (sint_mul x y) (sint_mul x z) ==
   * sint_add (sint_mul y x) (sint_mul z x) *)
  Check (sint_add_eq_r (sint_mul x z) (sint_mul z x) (sint_mul x y)
                       (sint_mul_comm x z)).
  assert (H_rhs_eq := sint_eq_trans
                        (sint_mul (sint_add y z) x)
                        (sint_add (sint_mul x y) (sint_mul x z))
                        (sint_add (sint_mul x y) (sint_mul z x))
                        H_tmp_eq
                        (sint_add_eq_r
                           (sint_mul x z) (sint_mul z x) (sint_mul x y)
                           (sint_mul_comm x z))).
  clear H_tmp_eq.
  exact (sint_eq_trans
           (sint_mul (sint_add y z) x)
           (sint_add (sint_mul x y) (sint_mul z x))
           (sint_add (sint_mul y x) (sint_mul z x))
           H_rhs_eq (sint_add_eq_l
                       (sint_mul x y) (sint_mul y x)
                       (sint_mul z x) (sint_mul_comm x y))).
Qed.

Proposition sint_mul_no_zero_divisors :
  forall x y : sint,
    sint_mul x y == Z ->
    x == Z \/ y == Z \/
    (x == Z /\ y == Z).
Proof.
  intros [px |  | nx] y H_eq0.
  - right; left.
    unfold sint_mul in H_eq0.

  Restart.

  intros [px |  | nx] [py |  | ny] H_eq0;
    unfold sint_mul in H_eq0.
  - contradiction H_eq0.
  - right; left; exact H_eq0.
  - contradiction H_eq0.
  - left; exact H_eq0.
  - left; exact H_eq0.
  - left; exact H_eq0.
  - contradiction H_eq0.
  - right; left; reflexivity.
  - contradiction H_eq0.

  Restart.  

  (intros [px |  | nx] [py |  | ny] H_eq0;
   unfold sint_mul in H_eq0;
   ((contradiction H_eq0) ||
    (right; left; reflexivity) ||
    (left; reflexivity))).
Qed.

(* ********** *)

(* incomplete prelim ver.? probably sound, but not super helpful? *)
Definition sint_neq (x y : sint) : Prop :=
  match x, y with
  | P n1, P n2 | N n1, N n2 => n1 <> n2
  | Z, Z => False
  | _, _ => True         
  end.

Definition sint_sub (x y : sint) : sint :=
  sint_add x (sint_neg y).

Lemma sint_sub_eq_is_0 :
  forall x y : sint,
    x == y <-> sint_sub x y == Z.
Proof.
  intros x y.
  split.

  - intro H_eq.
    unfold sint_sub.
    Check (sint_add_eq_l x y (sint_neg y) H_eq).
    exact (sint_eq_trans (sint_add x (sint_neg y))
                         (sint_add y (sint_neg y))
                         Z
                         (sint_add_eq_l x y (sint_neg y) H_eq)
                         (sint_add_neg_of_itself_r y)).

  - revert x y.
    unfold sint_sub, sint_add, sint_neg, sint_eq;
      intros [px |  | nx] [py |  | ny] H_eq0.
    + case (px =? py) as [ | ] eqn:H_eq.
      -- exact (beq_nat_true px py H_eq).
      -- case (px <? py) as [ | ] eqn:H_lt.
         ++ contradiction H_eq0.
         ++ contradiction H_eq0.
    + contradiction H_eq0.
    + contradiction H_eq0.
    + contradiction H_eq0. 
    + trivial.
    + contradiction H_eq0.
    + contradiction H_eq0.
    + contradiction H_eq0.
    + case (nx =? ny) as [ | ] eqn:H_eq.
      -- exact (beq_nat_true nx ny H_eq).
      -- case (nx <? ny) as [ | ] eqn:H_lt.
         ++ contradiction H_eq0.
         ++ contradiction H_eq0.
Qed.

Lemma sint_mul_neg_r :
  forall x y : sint,
    sint_mul x (sint_neg y) == sint_neg (sint_mul x y).
Proof.
  intros [px |  | nx] [py |  | ny];
    unfold sint_mul, sint_neg;
    reflexivity.
Qed.

Lemma sint_mul_sub_distr_r :
  forall x y z : sint,
    sint_mul (sint_sub y z) x ==
    sint_sub (sint_mul x y) (sint_mul x z).
Proof.
  intros x y z.
  unfold sint_sub.
  Check (sint_mul_add_distr_r x y (sint_neg z)).
  assert (H_rhs_comm := sint_eq_trans
                          (sint_add (sint_mul y x) (sint_mul (sint_neg z) x))
                          (sint_add (sint_mul x y) (sint_mul (sint_neg z) x))
                          (sint_add (sint_mul x y) (sint_mul x (sint_neg z)))
                          (sint_add_eq_l
                             (sint_mul y x)
                             (sint_mul x y)
                             (sint_mul (sint_neg z) x)
                             (sint_mul_comm y x))
                          (sint_add_eq_r
                             (sint_mul (sint_neg z) x)
                             (sint_mul x (sint_neg z))
                             (sint_mul x y)
                             (sint_mul_comm (sint_neg z) x))).
  assert (H_neg_assoc := sint_add_eq_r (sint_mul x (sint_neg z))
                                       (sint_neg (sint_mul x z))
                                       (sint_mul x y)
                                       (sint_mul_neg_r x z)).
  assert (H_tmp := sint_eq_trans
                     (sint_mul (sint_add y (sint_neg z)) x)
                     (sint_add (sint_mul y x) (sint_mul (sint_neg z) x))
                     (sint_add (sint_mul x y) (sint_mul x (sint_neg z)))
                     (sint_mul_add_distr_r x y (sint_neg z))
                     H_rhs_comm); clear H_rhs_comm.
  exact (sint_eq_trans (sint_mul (sint_add y (sint_neg z)) x)
                       (sint_add (sint_mul x y) (sint_mul x (sint_neg z)))
                       (sint_add (sint_mul x y) (sint_neg (sint_mul x z)))
                       H_tmp H_neg_assoc).
Qed.

Corollary sint_mul_non_zero :
  forall x y : sint,
    sint_mul x y == Z ->
    sint_neq y Z ->
    x == Z.
Proof.
  intros x y H_eq0.
  Check (sint_mul_no_zero_divisors x y H_eq0).
  destruct (sint_mul_no_zero_divisors x y H_eq0) as [H_x_eq0 | [H_y_eq0 | H_x_y_eq0]].

  (* Follow-up: if it's a disjunctive pattern, why is it necessary to go through
   * all three cases? Is proving one not enough? *)
  
  - intro H_y_neq0.
    exact H_x_eq0.

  - intro H_y_neq0.
    destruct y as [py |  | ny].
    + unfold sint_eq in H_y_eq0;
        contradiction H_y_eq0.
    + unfold sint_neq, not in H_y_neq0;
        contradiction H_y_neq0.
    + unfold sint_eq in H_y_eq0;
      contradiction H_y_eq0.

  - intro H_y_neq0.
    destruct H_x_y_eq0 as [H_x_eq0 _].
    exact H_x_eq0.
Qed.
  
Proposition sint_mul_cancel_l :
  forall x y z : sint,
    sint_neq z Z ->
    sint_mul z x == sint_mul z y -> x == y.
Proof.
  intros [px |  | nx] [py |  | ny] [pz |  | nz] H_neq H_eq_zx_zy;
    unfold sint_neq in H_neq; unfold sint_mul, sint_eq in H_eq_zx_zy.
  - (* wanted: S pz * S px - 1 = S pz * S py - 1 -> px = py *)
    
    (* Potentially interesting: thought this doesn't work for a sec bc
     * we don't have pz <> 0, but actually, sint_neq z Z doesn't imply 
     * that when z in the form of pos/nat integers, the corresponding nat
     * isn't equal to 0. It's just bc it's (S pz) here, which guarantees
     * (S pz > 0), that allows nat cancellation... 
     * Okay I was gonna rewrite sint_neq but I guess there's no need now *)
    admit.

    (* Either way tho doing this wouldn't be fun with 27 cases... But it would
     * be following what Tao said about Corollary 12 + Lemma 15 combined, instead
     * of the simpler method involving subtraction of integers etc. (week1 p32) *)
    Restart.

    intros x y z H_0 H_eq.
    destruct (sint_sub_eq_is_0 (sint_mul z x) (sint_mul z y)) as [H_sub_eq_mul _].
    Check (sint_eq_trans (sint_mul (sint_sub x y) z)
                         (sint_sub (sint_mul x z)
                                   (sint_mul y z))
                         Z).
    assert (H_move_to_lhs := sint_eq_trans (sint_mul (sint_sub x y) z)
                                           (sint_sub (sint_mul z x)
                                                     (sint_mul z y))
                                           Z
                                           (sint_mul_sub_distr_r z x y)
                                           (H_sub_eq_mul H_eq)).
    assert (H_cancelled_lhs := sint_mul_non_zero (sint_sub x y) z
                                                 H_move_to_lhs
                                                 H_0).
    destruct (sint_sub_eq_is_0 x y) as [_ H_sub_eq_xy].
    Check (H_sub_eq_xy H_cancelled_lhs).
    exact (H_sub_eq_xy H_cancelled_lhs).
Qed.
    
(* ********** *)

(* Potentially interesting: vs. int representation *)
Definition sint_ge (x y : sint) : Prop :=
  exists n : nat,
    x == sint_add y (P n) \/
    x == sint_add y Z.

Definition sint_le (x y : sint) : Prop :=
  sint_ge y x.

Definition sint_gt (x y : sint) : Prop :=
  sint_ge x y /\ sint_neq x y.

Definition sint_lt (x y : sint) : Prop :=
  sint_le x y /\ sint_neq x y.

Lemma sint_neq_and_eq_false :
  forall x y : sint,
    sint_neq x y ->
    x == y -> False.
Proof.
  (intros [px |  | nx] [py |  | ny];
   unfold sint_neq, sint_eq;
   intros H_neq H_eq;
   ((unfold not in H_neq;
     exact (H_neq H_eq)) || exact H_eq || exact H_neq)).
Qed.

(* Potentially interesting: more subgoals can also force you to be more
 * economical and discover object-level solutions, not fall back on meta-level *)
Lemma sint_add_neg_of_itself_and_others_l :
  forall x y : sint,
    sint_add (sint_add x y) (sint_neg x) == y.
Proof.
  intros [px |  | nx] [py |  | ny];
    unfold sint_neg, sint_eq, sint_add.
  
  Restart.
  
  intros x y.
  Check (sint_add_assoc y x (sint_neg x)).
  assert (H_lhs := sint_eq_trans
                     (sint_add (sint_add x y) (sint_neg x))
                     (sint_add (sint_add y x) (sint_neg x))
                     (sint_add y (sint_add x (sint_neg x)))
                     (sint_add_eq_l (sint_add x y) (sint_add y x) (sint_neg x)
                                    (sint_add_comm x y))
                     (sint_add_assoc y x (sint_neg x))).
  assert (H_rhs := sint_eq_trans
                     (sint_add y (sint_add x (sint_neg x)))
                     (sint_add y Z)
                     y
                     (sint_add_eq_r
                        (sint_add x (sint_neg x)) Z y
                        (sint_add_neg_of_itself_r x))
                     (sint_add_0_r y)).
  exact (sint_eq_trans (sint_add (sint_add x y) (sint_neg x))
                       (sint_add y (sint_add x (sint_neg x)))
                       y H_lhs H_rhs).
Qed.
                     
Proposition sint_gt_to_pos_nat :
  forall x y : sint,
    sint_gt x y ->
    exists n : nat,
      sint_sub x y == P n.
Proof.
  intros x y.
  unfold sint_gt.
  intros [H_ge H_neq].
  unfold sint_ge in H_ge.
  destruct H_ge as [n [H_n' | H_n'_Z]].
  - exists n.
    unfold sint_sub.
    Check (sint_add_neg_of_itself_and_others_l y (P n)).
    exact (sint_eq_trans
             (sint_add x (sint_neg y))
             (sint_add (sint_add y (P n)) (sint_neg y))
             (P n)
             (sint_add_eq_l x (sint_add y (P n)) (sint_neg y) H_n')
             (sint_add_neg_of_itself_and_others_l y (P n))).
  - Check (sint_add_0_r y).
    assert (H_eq := sint_eq_trans x (sint_add y Z) y
                                  H_n'_Z (sint_add_0_r y)).
    contradiction (sint_neq_and_eq_false x y H_neq H_eq).
Qed.

(* Potentially interesting: this wasn't needed for Tao's representation
 * as his definition of sint_neg fell back on the nat definition, 
 * which already provides this property for cheap? *)
Lemma not_sint_eq_is_sint_neq :
  forall x y : sint,
    (x == y -> False) ->
    sint_neq x y.
Proof.
  intros [px |  | nx] [py |  | ny];
    unfold sint_eq, sint_neq;
    intro H_neq;
    (exact H_neq || exact I || exact (H_neq I)).
Qed.
  
(* Potentially interesting: most definitely not easier on this side,
 * as compared to Tao's integers? *)
Proposition pos_nat_to_sint_gt :
  forall x y : sint,
  exists n : nat,
    sint_sub x y == P n ->
    sint_gt x y.
Proof.
  unfold sint_sub, sint_gt, sint_ge.
  intros x y.
  exists 0.
  intro H_sub.
  split.
  - exists 0.
    left.
    Check (sint_add_assoc y x (sint_neg y)).
    assert (H_rhs := sint_eq_trans
                       (sint_add y (P 0))
                       (sint_add y (sint_add x (sint_neg y)))
                       (sint_add (sint_add y x) (sint_neg y))
                       (sint_add_eq_r
                          (P 0) (sint_add x (sint_neg y)) y
                          (sint_eq_sym
                             (sint_add x (sint_neg y)) (P 0)
                             H_sub))
                       (sint_eq_sym
                          (sint_add (sint_add y x) (sint_neg y))
                          (sint_add y (sint_add x (sint_neg y)))
                          (sint_add_assoc y x (sint_neg y)))).
    Check (sint_add_neg_of_itself_and_others_l y x).
    exact (sint_eq_sym
             (sint_add y (P 0))
             x
             (sint_eq_trans
                (sint_add y (P 0))
                (sint_add (sint_add y x) (sint_neg y))
                x
                H_rhs (sint_add_neg_of_itself_and_others_l y x))).
  - Check (not_sint_eq_is_sint_neq x y).
    apply (not_sint_eq_is_sint_neq x y).
    intro H_eq.
    assert (H_lhs := sint_eq_trans
                       Z
                       (sint_add y (sint_neg y))
                       (sint_add x (sint_neg y))
                       (sint_eq_sym
                          (sint_add y (sint_neg y)) Z
                          (sint_add_neg_of_itself_r y))
                       (sint_add_eq_l y x (sint_neg y)
                                      (sint_eq_sym x y H_eq))).
    contradiction (sint_eq_trans
                     Z
                     (sint_add x (sint_neg y))
                     (P 0)
                     H_lhs H_sub).
Qed.

Lemma sint_ge_plus_both_sides :
  forall x y z : sint,
    sint_ge x y ->
    sint_ge (sint_add x z) (sint_add y z).
Proof.
  unfold sint_ge.
  intros x y z H_ge.
  destruct H_ge as [n [H_n' | H_eq]].
  - exists n.
    left.
    Check (sint_add_assoc y (P n) z).
    assert (H_lhs := sint_eq_trans
                       (sint_add x z)
                       (sint_add (sint_add y (P n)) z)
                       (sint_add y (sint_add (P n) z))
                       (sint_add_eq_l x (sint_add y (P n)) z H_n')
                       (sint_add_assoc y (P n) z)).
    Check (sint_add_assoc y z (P n)).
    assert (H_rhs := sint_eq_trans
                       (sint_add y (sint_add (P n) z))
                       (sint_add y (sint_add z (P n)))
                       (sint_add (sint_add y z) (P n))
                       (sint_add_eq_r (sint_add (P n) z)
                                      (sint_add z (P n)) y
                                      (sint_add_comm (P n) z))
                       (sint_eq_sym
                          (sint_add (sint_add y z) (P n))
                          (sint_add y (sint_add z (P n)))
                          (sint_add_assoc y z (P n)))).
    exact (sint_eq_trans
             (sint_add x z)
             (sint_add y (sint_add (P n) z))
             (sint_add (sint_add y z) (P n))
             H_lhs H_rhs).
  - exists 0.
    right.
    Check (sint_add_assoc y z Z).
    Check (sint_add_assoc y Z z).
    assert (H_lhs := sint_eq_trans
                       (sint_add x z)
                       (sint_add (sint_add y Z) z)
                       (sint_add y (sint_add Z z))
                       (sint_add_eq_l x (sint_add y Z) z H_eq)
                       (sint_add_assoc y Z z)).
    assert (H_rhs := sint_eq_trans
                       (sint_add y (sint_add Z z))
                       (sint_add y (sint_add z Z))
                       (sint_add (sint_add y z) Z)
                       (sint_add_eq_r
                          (sint_add Z z) (sint_add z Z) y
                          (sint_add_comm Z z))
                       (sint_eq_sym
                          (sint_add (sint_add y z) Z)
                          (sint_add y (sint_add z Z))
                          (sint_add_assoc y z Z))).
    exact (sint_eq_trans
             (sint_add x z)
             (sint_add y (sint_add Z z))
             (sint_add (sint_add y z) Z)
             H_lhs H_rhs).
Qed.

Lemma eq_Smp_Snp_to_eq_mn :
  forall m n p : nat,
    m + p + 1 = n + p + 1 ->
    m = n.
Proof.
  intros m n p H_eq_S.
  rewrite <- 2 Nat.add_assoc in H_eq_S.
  rewrite -> Nat.add_1_r in H_eq_S.
  Search (_ + _ = _ + _ -> _ = _).
  rewrite <- 2 (Nat.add_comm (S p)) in H_eq_S.
  exact (plus_reg_l m n (S p) H_eq_S).
Qed.

Lemma neq_Smn_n :
  forall m n : nat,
    m + n + 1 <> n.
Proof.
  unfold not.
  intros m n H_eq.
  rewrite -> (Nat.add_comm m n) in H_eq.
  rewrite <- Nat.add_assoc in H_eq.
  rewrite -> Nat.add_1_r in H_eq.
  Check (Nat.add_le_lt_mono
           n n 0 (S m) (Nat.le_refl n) (Nat.lt_0_succ m)).
  assert (H_lt := Nat.add_le_lt_mono
                    n n 0 (S m) (Nat.le_refl n) (Nat.lt_0_succ m)).
  rewrite -> Nat.add_0_r in H_lt.
  assert (H_absurd := Nat.lt_neq n (n + S m) H_lt).
  unfold not in H_absurd.
  exact (H_absurd (eq_sym H_eq)).
Qed.

Lemma lt_pred_mn_m :
  forall m n : nat,
    n < m ->
    m - n - 1 < m.
Proof.
  intros m n H_lt.
  rewrite <- Nat.sub_add_distr.
  rewrite -> Nat.add_1_r.
  Search (_ + _ < _ + _ -> _).
  Check (Nat.le_lt_add_lt (S n) (S n) (m - S n) m
                          (Nat.le_refl (S n))).
  apply (Nat.le_lt_add_lt (S n) (S n) (m - S n) m
                          (Nat.le_refl (S n))).
  Check (Nat.sub_add (S n) m (lt_le_S n m H_lt)).
  rewrite -> (Nat.sub_add (S n) m (lt_le_S n m H_lt)).
  assert (H_lt_m_mSn := Nat.add_le_lt_mono
                          m m 0 (S n)
                          (Nat.le_refl m) (Nat.lt_0_succ n)).
  rewrite -> Nat.add_0_r in H_lt_m_mSn.
  exact H_lt_m_mSn.
Qed.

Lemma neq_pred_mn_m :
  forall m n : nat,
    n < m ->
    m - n - 1 <> m.
Proof.
  intros m n H_lt H_eq.
  assert (H_lt_pred_mn_m := lt_pred_mn_m m n H_lt).
  assert (H_absurd := Nat.lt_neq (m - n - 1) m H_lt_pred_mn_m);
    clear H_lt_pred_mn_m.
  exact (H_absurd H_eq).
Qed.

Lemma neq_Smn_pred_np :
  forall m n p : nat,
    p < n ->
    m + n + 1 <> n - p - 1.
Proof.
  intros m n p H_lt H_eq.
  Check (lt_pred_mn_m n p H_lt).
  assert (H_lt_pred_np_n := lt_pred_mn_m n p H_lt).
  Search (_ < _ -> _ < _ + _).
  Check (Nat.lt_lt_add_r (n - p - 1) n (m + 1) H_lt_pred_np_n).
  assert (H_lt' := Nat.lt_lt_add_r
                     (n - p - 1) n (m + 1) H_lt_pred_np_n);
    clear H_lt_pred_np_n.
  rewrite -> (Nat.add_comm m n) in H_eq.
  rewrite <- Nat.add_assoc in H_eq.
  Check (Nat.lt_neq (n - p - 1) (n + (m + 1)) H_lt' (eq_sym H_eq)).
  exact (Nat.lt_neq (n - p - 1) (n + (m + 1)) H_lt' (eq_sym H_eq)).
Qed.

Lemma eq_pred_pm_pred_pn_to_eq_mn :
  forall m n p : nat,
    m < p -> n < p ->
    p - m - 1 = p - n - 1 ->
    m = n.
Proof.
  intros m n p H_lt_m_p H_lt_n_p H_eq.
  rewrite <- 2 Nat.sub_add_distr in H_eq.
  rewrite -> 2 Nat.add_1_r in H_eq.
  Check (f_equal2_plus).
  assert (H_eq_Sm := f_equal2_plus
                       (p - S m) (p - S n) (S m) (S m)
                       H_eq (Nat.eq_refl (S m)));
    clear H_eq.
  Search (_ < _ -> S _ <= _).
  rewrite -> (Nat.sub_add (S m) p (lt_le_S m p H_lt_m_p)) in H_eq_Sm.
  assert (H_eq_Sn := f_equal2_plus
                       p (p - S n + S m) (S n) (S n)
                       H_eq_Sm (Nat.eq_refl (S n)));
    clear H_eq_Sm.
  rewrite <- Nat.add_assoc in H_eq_Sn.
  rewrite -> (Nat.add_comm (S m)) in H_eq_Sn.
  rewrite -> Nat.add_assoc in H_eq_Sn.
  rewrite -> (Nat.sub_add (S n) p (lt_le_S n p H_lt_n_p)) in H_eq_Sn.
  Search (_ + _ = _ -> _ = _).
  assert (H_eq_S := plus_reg_l (S n) (S m) p H_eq_Sn);
    clear H_eq_Sn.
  Search (S _ = S _ -> _ = _).
  exact (eq_sym (eq_add_S n m H_eq_S)).
Qed.

Lemma eq_pred_mp_pred_np_to_eq_mn :
  forall m n p : nat,
    p < m -> p < n ->
    m - p - 1 = n - p - 1 ->
    m = n.
Proof.
  intros m n p H_lt_p_m H_lt_p_n H_eq.
  rewrite <- 2 Nat.sub_add_distr in H_eq.
  rewrite -> Nat.add_1_r in H_eq.
  assert (H_eq_S := f_equal2_plus
                      (m - S p) (n - S p) (S p) (S p)
                      H_eq (Nat.eq_refl (S p)));
    clear H_eq.
  rewrite -> (Nat.sub_add (S p) m (lt_le_S p m H_lt_p_m)) in H_eq_S.
  rewrite -> (Nat.sub_add (S p) n (lt_le_S p n H_lt_p_n)) in H_eq_S.
  exact H_eq_S.
Qed.
  
Lemma sint_add_cancel_r :
  forall x y z : sint,
    sint_add x z == sint_add y z ->
    x == y.
Proof.
  intros x y [pz |  | nz] H_eq.
  - destruct x as [px |  | nx];
      destruct y as [py |  | ny].
    + unfold sint_add, sint_eq in H_eq.
      rewrite -> (eq_Smp_Snp_to_eq_mn px py pz H_eq).
      exact (sint_eq_refl (P py)).
    + unfold sint_add, sint_eq in H_eq.
      contradiction (neq_Smn_n px pz H_eq).
      (* contradiction *)
    + unfold sint_add, sint_eq in H_eq.
      case (ny =? pz) as [ | ] eqn:H_eqb_ny_pz.
      -- contradiction H_eq.
      -- case (ny <? pz) as [ | ] eqn:H_ltb_ny_pz.
         ++ destruct (Nat.ltb_lt ny pz) as [H_ltb_lt _].
            Check (neq_Smn_pred_np px pz ny (H_ltb_lt H_ltb_ny_pz)).
            contradiction (neq_Smn_pred_np
                             px pz ny (H_ltb_lt H_ltb_ny_pz) H_eq).
         (* px + pz + 1 = pz - ny - 1 *)
         ++ contradiction H_eq.
    + unfold sint_add, sint_eq in H_eq.
      contradiction (neq_Smn_n py pz (eq_sym H_eq)).
      (* contradiction *)
    + exact (sint_eq_refl Z).
    + unfold sint_add, sint_eq in H_eq.
      case (ny =? pz) as [ | ] eqn:H_eqb_ny_pz.
      -- contradiction H_eq.
      -- case (ny <? pz) as [ | ] eqn:H_ltb_ny_pz.
         ++ destruct (Nat.ltb_lt ny pz) as [H_ltb_lt _].
            Check (neq_pred_mn_m pz ny (H_ltb_lt H_ltb_ny_pz)).
            contradiction (neq_pred_mn_m
                             pz ny (H_ltb_lt H_ltb_ny_pz) (eq_sym H_eq)).
         ++ contradiction H_eq.
    + unfold sint_add, sint_eq in H_eq.
      case (nx =? pz) as [ | ] eqn:H_eqb_nx_pz.
      -- contradiction H_eq.
      -- case (nx <? pz) as [ | ] eqn:H_ltb_nx_pz.
         ++ destruct (Nat.ltb_lt nx pz) as [H_ltb_lt _].
            contradiction (neq_Smn_pred_np
                             py pz nx (H_ltb_lt H_ltb_nx_pz) (eq_sym H_eq)).
         ++ contradiction H_eq.
    + unfold sint_add, sint_eq in H_eq.
      case (nx =? pz) as [ | ] eqn:H_eqb_nx_pz.
      -- contradiction H_eq.
      -- case (nx <? pz) as [ | ] eqn:H_ltb_nx_pz.
         ++ destruct (Nat.ltb_lt nx pz) as [H_ltb_lt _].
            Check (neq_pred_mn_m pz nx (H_ltb_lt H_ltb_nx_pz)).
            contradiction (neq_pred_mn_m
                             pz nx (H_ltb_lt H_ltb_nx_pz) H_eq).
         (* pz - nx - 1 = pz *)
         ++ contradiction H_eq.
    + unfold sint_add, sint_eq in H_eq.
      case (nx =? pz) as [ | ] eqn:H_eqb_nx_pz.
      -- case (ny =? pz) as [ | ] eqn:H_eqb_ny_pz.
         ++ rewrite -> (beq_nat_true nx pz H_eqb_nx_pz).
            rewrite -> (beq_nat_true ny pz H_eqb_ny_pz).
            exact (sint_eq_refl (N pz)).
         ++ case (ny <? pz) as [ | ] eqn:H_ltb_ny_pz.
            --- contradiction H_eq.
            --- contradiction H_eq.
      -- case (nx <? pz) as [ | ] eqn:H_ltb_nx_pz;
           case (ny =? pz) as [ | ] eqn:H_eqb_ny_pz.
         ++ contradiction H_eq.
         ++ case (ny <? pz) as [ | ] eqn:H_ltb_ny_pz.
            --- destruct (Nat.ltb_lt nx pz) as [H_ltb_lt_x_z _].
                assert (H_lt_x_z := H_ltb_lt_x_z H_ltb_nx_pz);
                  clear H_ltb_lt_x_z; clear H_ltb_nx_pz.
                destruct (Nat.ltb_lt ny pz) as [H_ltb_lt_y_z _].
                assert (H_lt_y_z := H_ltb_lt_y_z H_ltb_ny_pz);
                  clear H_ltb_lt_y_z; clear H_ltb_ny_pz.
                rewrite ->  (eq_pred_pm_pred_pn_to_eq_mn
                               nx ny pz H_lt_x_z H_lt_y_z H_eq).
                exact (sint_eq_refl (N ny)).
            (* wanted: pz - nx - 1 = pz - ny - 1 -> nx = ny *)
            --- contradiction H_eq.
         ++ contradiction H_eq.
         ++ case (ny <? pz) as [ | ] eqn:H_ltb_ny_pz.
            --- contradiction H_eq.
            --- assert (H_neq_x_z :=
                          Nat.neq_sym
                            nx pz (beq_nat_false nx pz H_eqb_nx_pz));
                  clear H_eqb_nx_pz.
                assert (H_neq_y_z :=
                          Nat.neq_sym
                            ny pz (beq_nat_false ny pz H_eqb_ny_pz));
                  clear H_eqb_ny_pz.
                destruct (Nat.ltb_ge nx pz) as [H_to_ge _];
                  assert (H_ge_x_z := H_to_ge H_ltb_nx_pz);
                  clear H_to_ge; clear H_ltb_nx_pz.
                destruct (Nat.ltb_ge ny pz) as [H_to_ge _];
                  assert (H_ge_y_z := H_to_ge H_ltb_ny_pz);
                  clear H_to_ge; clear H_ltb_ny_pz.
                Search (_ <= _ /\ _ <> _).
                destruct (Nat.le_neq pz nx) as [_ H_to_lt_x_z];
                  assert (H_lt_x_z :=
                            H_to_lt_x_z (conj H_ge_x_z H_neq_x_z));
                  clear H_to_lt_x_z; clear H_ge_x_z; clear H_neq_x_z.
                destruct (Nat.le_neq pz ny) as [_ H_to_lt_y_z];
                  assert (H_lt_y_z :=
                            H_to_lt_y_z (conj H_ge_y_z H_neq_y_z));
                  clear H_to_lt_y_z; clear H_ge_y_z; clear H_neq_y_z.
                rewrite -> (eq_pred_mp_pred_np_to_eq_mn
                              nx ny pz H_lt_x_z H_lt_y_z H_eq).
                exact (sint_eq_refl (N ny)).
                (* wanted: nx - pz - 1 = ny - pz - 1 -> nx = ny *)
  - assert (H_tmp := sint_eq_trans
                       x
                       (sint_add x Z)
                       (sint_add y Z)
                       (sint_eq_sym
                          (sint_add x Z) x
                          (sint_add_0_r x))
                       H_eq).
    exact (sint_eq_trans x (sint_add y Z) y
                         H_tmp (sint_add_0_r y)).
  - destruct x as [px |  | nx];
      destruct y as [py |  | ny].
    + unfold sint_add, sint_eq in H_eq.
      case (py =? nz) as [ | ] eqn:H_eqb_py_nz;
        case (px =? nz) as [ | ] eqn:H_eqb_px_nz.
      -- rewrite -> (beq_nat_true px nz H_eqb_px_nz).
         rewrite -> (beq_nat_true py nz H_eqb_py_nz).
         exact (sint_eq_refl (P nz)).
      -- case (px <? nz) as [ | ] eqn:H_ltb_px_nz.
         ++ contradiction H_eq.
         ++ contradiction H_eq.
      -- case (py <? nz) as [ | ] eqn:H_ltb_py_nz.
         ++ contradiction H_eq.
         ++ contradiction H_eq.
      -- case (px <? nz) as [ | ] eqn:H_ltb_px_nz;
           case (py <? nz) as [ | ] eqn:H_ltb_py_nz.
         ++ destruct (Nat.ltb_lt px nz) as [H_to_lt_x_z _];
              destruct (Nat.ltb_lt py nz) as [H_to_lt_y_z _].
            rewrite -> (eq_pred_pm_pred_pn_to_eq_mn
                          px py nz (H_to_lt_x_z H_ltb_px_nz)
                          (H_to_lt_y_z H_ltb_py_nz) H_eq).
            exact (sint_eq_refl (P py)).
         ++ contradiction H_eq.
         ++ contradiction H_eq.
         ++ assert (H_neq_x_z :=
                      (Nat.neq_sym
                         px nz (beq_nat_false px nz H_eqb_px_nz)));
              assert (H_neq_y_z :=
                        (Nat.neq_sym
                           py nz (beq_nat_false py nz H_eqb_py_nz)));
              clear H_eqb_px_nz; clear H_eqb_py_nz.
            destruct (Nat.ltb_ge px nz) as [H_to_ge_x_z _];
              destruct (Nat.ltb_ge py nz) as [H_to_ge_y_z _].
            assert (H_ge_x_z := H_to_ge_x_z H_ltb_px_nz);
              assert (H_ge_y_z := H_to_ge_y_z H_ltb_py_nz);
              clear H_to_ge_x_z; clear H_to_ge_y_z;
                clear H_ltb_px_nz; clear H_ltb_py_nz.
            destruct (Nat.le_neq nz px) as [_ H_to_lt_z_x];
              destruct (Nat.le_neq nz py) as [_ H_to_lt_z_y].
            assert (H_lt_z_x := H_to_lt_z_x (conj H_ge_x_z H_neq_x_z));
              assert (H_lt_z_y := H_to_lt_z_y (conj H_ge_y_z H_neq_y_z)).
            rewrite -> (eq_pred_mp_pred_np_to_eq_mn
                          px py nz H_lt_z_x H_lt_z_y H_eq).
            exact (sint_eq_refl (P py)).
    + unfold sint_add, sint_eq in H_eq.
      case (px =? nz) as [ | ] eqn:H_eqb_px_nz.
      -- contradiction H_eq.
      -- case (px <? nz) as [ | ] eqn:H_ltb_px_nz.
         ++ destruct (Nat.ltb_lt px nz) as [H_ltb_lt _].
            contradiction (neq_pred_mn_m
                             nz px (H_ltb_lt H_ltb_px_nz) H_eq).
         ++ contradiction H_eq.
    + unfold sint_add, sint_eq in H_eq.
      case (px =? nz) as [ | ] eqn:H_eqb_px_nz.
      -- contradiction H_eq.
      -- case (px <? nz) as [ | ] eqn:H_ltb_px_nz.
         ++ destruct (Nat.ltb_lt px nz) as [H_ltb_lt _].
            contradiction (neq_Smn_pred_np
                             ny nz px (H_ltb_lt H_ltb_px_nz) (eq_sym H_eq)).
         ++ contradiction H_eq.
    + unfold sint_add, sint_eq in H_eq.
      case (py =? nz) as [ | ] eqn:H_eqb_py_nz.
      -- contradiction H_eq.
      -- case (py <? nz) as [ | ] eqn:H_ltb_py_nz.
         ++ destruct (Nat.ltb_lt py nz) as [H_ltb_lt _].
            contradiction (neq_pred_mn_m
                             nz py (H_ltb_lt H_ltb_py_nz) (eq_sym H_eq)).
         ++ contradiction H_eq.
    + exact (sint_eq_refl Z).
    + unfold sint_add, sint_eq in H_eq.
      exact (neq_Smn_n ny nz (eq_sym H_eq)).
    + unfold sint_add, sint_eq in H_eq.
      case (py =? nz) as [ | ] eqn:H_eqb_py_nz.
      -- contradiction H_eq.
      -- case (py <? nz) as [ | ] eqn:H_ltb_py_nz.
         ++ destruct (Nat.ltb_lt py nz) as [H_ltb_lt _].
            contradiction (neq_Smn_pred_np
                             nx nz py (H_ltb_lt H_ltb_py_nz) H_eq).
         ++ contradiction H_eq.
    + unfold sint_add, sint_eq in H_eq.
      exact (neq_Smn_n nx nz H_eq).
    + unfold sint_add, sint_eq in H_eq.
      rewrite -> (eq_Smp_Snp_to_eq_mn nx ny nz H_eq).
      exact (sint_eq_refl (N ny)).
Qed.

Lemma sint_neq_plus_both_sides :
  forall x y z : sint,
    sint_neq x y -> sint_neq (sint_add x z) (sint_add y z).
Proof.
  intros x y z H_neq.
  Check (not_sint_eq_is_sint_neq (sint_add x z) (sint_add y z)).
  apply (not_sint_eq_is_sint_neq (sint_add x z) (sint_add y z)).
  intro H_eq.
  Check (sint_add_cancel_r x y z H_eq).
  exact (sint_neq_and_eq_false
           x y H_neq (sint_add_cancel_r x y z H_eq)).
Qed.

Proposition sint_gt_plus_both_sides :
  forall x y z : sint,
    sint_gt x y ->
    sint_gt (sint_add x z) (sint_add y z).
Proof.
  unfold sint_gt.
  intros x y z [H_ge H_neq].
  split.
  - exact (sint_ge_plus_both_sides x y z H_ge).
  - exact (sint_neq_plus_both_sides x y z H_neq).
Qed.

Lemma sint_ge_mul_both_sides :
  forall x y : sint,
    sint_ge x y ->
    forall n : nat,
      sint_ge (sint_mul x (P n)) (sint_mul y (P n)).
Proof.
  unfold sint_ge.
  intros x y H_ge n.
  destruct H_ge as [n' [H_eq | H_eq_Z]].
  - exists (S n' * S n - 1).
    (* y*Pn + Pn'*Pn = y*Pn + Pn'*Pn *)
    left.
    Check (sint_mul_add_distr_r (P n) y (P n')).
    assert (H_tmp := sint_eq_trans
                       (sint_mul x (P n))
                       (sint_mul (sint_add y (P n')) (P n))
                       (sint_add (sint_mul y (P n)) (sint_mul (P n') (P n)))
                       (sint_mul_eq_l x (sint_add y (P n')) (P n)
                                      H_eq)
                       (sint_mul_add_distr_r (P n) y (P n'))).
    (* Follow-up: how does this location thing even work... third occurence? *)
    unfold sint_mul in H_tmp at 3.
    exact H_tmp.
  - exists n'.
    right.
    assert (H_lhs := sint_eq_trans
                       (sint_mul x (P n))
                       (sint_mul (sint_add y Z) (P n))
                       (sint_mul y (P n))
                       (sint_mul_eq_l x (sint_add y Z) (P n)
                                      H_eq_Z)
                       (sint_mul_eq_l (sint_add y Z) y (P n)
                                      (sint_add_0_r y))).
    exact (sint_eq_trans
             (sint_mul x (P n))
             (sint_mul y (P n))
             (sint_add (sint_mul y (P n)) Z)
             H_lhs
             (sint_eq_sym
                (sint_add (sint_mul y (P n)) Z)
                (sint_mul y (P n))
                (sint_add_0_r (sint_mul y (P n))))).
Qed.

Lemma neq_mn_to_neq_pred_SmSn_mul_Sp :
  forall m n p : nat,
    m <> n -> 
    S m * S p - 1 <> S n * S p - 1.
Proof.
  unfold not;
    intros m n p H_neq_m_n H_eq.
  apply H_neq_m_n.
  Search (Nat.pred).
  Check (Nat.sub_1_r (S m * S p)).
  rewrite -> 2 Nat.sub_1_r in H_eq.
  Check (Nat.pred_inj (S m * S p) (S n * S p)).
  Search (_ < _ -> _ <= _ -> _ < _).
  assert (H_0_lt_SmSp :=
            Nat.lt_le_trans 0 1 (S m * S p) Nat.lt_0_1 (le_1_SmSn m p)).
  assert (H_0_lt_SnSp :=
            Nat.lt_le_trans 0 1 (S n * S p) Nat.lt_0_1 (le_1_SmSn n p)).
  Search (_ < _ -> _ <> _).
  Search (_ <> _ -> _ <> _).
  Check (Nat.lt_neq 0 (S m * S p) H_0_lt_SmSp).
  assert (H_eq_SmSp_SnSp :=
            Nat.pred_inj (S m * S p) (S n * S p)
                         (Nat.neq_sym
                            0 (S m * S p)
                            (Nat.lt_neq 0 (S m * S p) H_0_lt_SmSp))
                         (Nat.neq_sym
                            0 (S n * S p)
                            (Nat.lt_neq 0 (S n * S p) H_0_lt_SnSp))
                         H_eq);
    clear H_eq; clear H_0_lt_SmSp; clear H_0_lt_SnSp.
  Check (Nat.mul_cancel_r (S m) (S n) (S p)
                          (Nat.neq_sym 0 (S p) (Nat.neq_0_succ p))).
  destruct (Nat.mul_cancel_r (S m) (S n) (S p)
                             (Nat.neq_sym 0 (S p) (Nat.neq_0_succ p)))
    as [H_cancel _].
  assert (H_eq_Sm_Sn := H_cancel H_eq_SmSp_SnSp);
    clear H_eq_SmSp_SnSp; clear H_cancel.
  Search (S _ = S _).
  exact (eq_add_S m n H_eq_Sm_Sn).
Qed.

Lemma sint_neq_mul_both_sides :
  forall x y : sint,
    sint_neq x y ->
    forall n : nat,
      sint_neq (sint_mul x (P n)) (sint_mul y (P n)).
Proof.
  (* wanted: px <> py -> S px * S n - 1 <> S py * S n - 1 *)
  unfold sint_neq, sint_mul, sint_eq;
    intros [px |  | nx] [py |  | ny] H_neq n;
    (exact (neq_mn_to_neq_pred_SmSn_mul_Sp px py n H_neq) ||
     exact H_neq ||
     exact (neq_mn_to_neq_pred_SmSn_mul_Sp nx ny n H_neq)).
Qed.
    
Proposition sint_gt_mul_both_sides :
  forall x y : sint,
    sint_gt x y ->
    forall n : nat,
      sint_gt (sint_mul x (P n)) (sint_mul y (P n)).
Proof.
  unfold sint_gt.
  intros x y [H_ge H_neq] z.
  split.
  - exact (sint_ge_mul_both_sides x y H_ge z).
  - exact (sint_neq_mul_both_sides x y H_neq z).
Qed.

Lemma sint_neg_over_sint_add_aux_1 :
  forall n1 n2 : nat,
    sint_neg (sint_add (P n1) (N n2)) ==
    sint_add (sint_neg (P n1)) (sint_neg (N n2)).
Proof.
  intros n1 n2.
  unfold sint_add, sint_eq, sint_neg.
  case (n1 =? n2) as [ | ] eqn:H_eqb;
    case (n1 <? n2) as [ | ] eqn:H_ltb;
    (exact I || reflexivity).
Qed.

Lemma sint_neg_over_sint_add_aux_2 :
  forall n1 n2 : nat,
    sint_neg (sint_add (N n1) (P n2)) ==
    sint_add (sint_neg (N n1)) (sint_neg (P n2)).
Proof.
  intros n1 n2.
  unfold sint_add, sint_eq, sint_neg.
  case (n1 =? n2) as [ | ] eqn:H_eqb;
    case (n1 <? n2) as [ | ] eqn:H_ltb;
    (exact I || reflexivity).
Qed.

Lemma sint_neg_over_sint_add :
  forall x y : sint,
    sint_neg (sint_add x y) ==
    sint_add (sint_neg x) (sint_neg y).
Proof.
  intros [px |  | nx] [py |  | ny];
    unfold sint_add, sint_eq, sint_neg;
    (exact (sint_neg_over_sint_add_aux_1 px ny) ||
     exact (sint_neg_over_sint_add_aux_2 nx py) ||
     reflexivity).
Qed.
  
Lemma sint_neg_eq :
  forall x y : sint,
    x == y ->
    sint_neg x == sint_neg y.
Proof.
  intros [px |  | nx] [py |  | ny];
    unfold sint_neg, sint_eq; intro H_eq;
      exact H_eq.
Qed.

Lemma sint_ge_to_sint_le_neg :
  forall x y : sint,
    sint_ge x y ->
    sint_le (sint_neg x) (sint_neg y).
Proof.
  unfold sint_le, sint_ge.
  intros x y H_ge.
  destruct H_ge as [n' [H_eq | H_eq_Z]].
  - exists n'.
    (* -y = -(y+Pn') + P_ = -y - Pn' + P_*)
    left.
    apply (sint_eq_sym (sint_add (sint_neg x) (P n')) (sint_neg y)).
    Check (sint_neg_over_sint_add y (P n')).
    assert (H_lhs :=
              sint_eq_trans
                (sint_add (sint_neg x) (P n'))
                (sint_add (sint_neg (sint_add y (P n'))) (P n'))
                (sint_add (sint_add (sint_neg y)
                                    (sint_neg (P n')))
                          (P n'))
                (sint_add_eq_l (sint_neg x)
                               (sint_neg (sint_add y (P n')))
                               (P n')
                               (sint_neg_eq
                                  x (sint_add y (P n')) H_eq))
                (sint_add_eq_l (sint_neg (sint_add y (P n')))
                               (sint_add (sint_neg y) (sint_neg (P n')))
                               (P n')
                               (sint_neg_over_sint_add y (P n')))).
    Check (sint_add_assoc (sint_neg y) (sint_neg (P n')) (P n')).
    assert (H_rhs :=
              sint_eq_trans
                (sint_add (sint_add
                             (sint_neg y)
                             (sint_neg (P n')))
                          (P n'))
                (sint_add (sint_neg y)
                          (sint_add (sint_neg (P n')) (P n')))
                (sint_add (sint_neg y) Z)
                (sint_add_assoc (sint_neg y) (sint_neg (P n')) (P n'))
                (sint_add_eq_r
                   (sint_add (sint_neg (P n')) (P n'))
                   Z
                   (sint_neg y)
                   (sint_add_neg_of_itself_l (P n')))).
    assert (H_ltr :=
              sint_eq_trans
                (sint_add (sint_neg x) (P n'))
                (sint_add (sint_add
                             (sint_neg y)
                             (sint_neg (P n')))
                          (P n'))
                (sint_add (sint_neg y) Z)
                H_lhs H_rhs);
      clear H_lhs; clear H_rhs.
    exact (sint_eq_trans
             (sint_add (sint_neg x) (P n'))
             (sint_add (sint_neg y) Z)
             (sint_neg y)
             H_ltr (sint_add_0_r (sint_neg y))).
  - exists 0.
    right.
    Check (sint_neg_eq x y).
    assert (H_eq := sint_eq_trans x (sint_add y Z) y
                                  H_eq_Z (sint_add_0_r y)).
    exact (sint_eq_trans
             (sint_neg y)
             (sint_add (sint_neg y) Z)
             (sint_add (sint_neg x) Z)
             (sint_eq_sym
                (sint_add (sint_neg y) Z)
                (sint_neg y)
                (sint_add_0_r (sint_neg y)))
             (sint_add_eq_l
                (sint_neg y) (sint_neg x) Z
                (sint_eq_sym (sint_neg x) (sint_neg y) 
                             (sint_neg_eq x y H_eq)))).
Qed.

Lemma sint_neq_to_sint_neq_neg :
  forall x y : sint,
    sint_neq x y ->
    sint_neq (sint_neg x) (sint_neg y).
Proof.
  intros [px |  | nx] [py |  | ny];
    unfold sint_neq, sint_neg, sint_eq;
    intro H_neq;
    (exact H_neq || exact I || contradiction H_neq).
Qed.

Proposition sint_gt_to_sint_lt_neg :
  forall x y : sint,
    sint_gt x y ->
    sint_lt (sint_neg x) (sint_neg y).
Proof.
  unfold sint_gt.
  intros x y [H_ge H_neq].
  split.
  - exact (sint_ge_to_sint_le_neg x y H_ge).
  - exact (sint_neq_to_sint_neq_neg x y H_neq).
Qed.

Lemma sint_ge_trans :
  forall x y z : sint,
    sint_ge x y ->
    sint_ge y z ->
    sint_ge x z.
Proof.
  unfold sint_ge.
  intros x y z H_ge_x_y H_ge_y_z.
  destruct H_ge_x_y as [n1 [H_eq_x_y | H_eq_x_yZ]];
    destruct H_ge_y_z as [n2 [H_eq_y_z | H_eq_y_zZ]].
  - exists (n2 + n1 + 1).
    left.
    assert (H_x_to_z := sint_eq_trans
                          x
                          (sint_add y (P n1))
                          (sint_add (sint_add z (P n2)) (P n1))
                          H_eq_x_y
                          (sint_add_eq_l
                             y (sint_add z (P n2)) (P n1)
                             H_eq_y_z));
      clear H_eq_x_y; clear H_eq_y_z.
    Check (sint_add_assoc z (P n2) (P n1)).
    assert (H_tmp := sint_eq_trans
                       x
                       (sint_add (sint_add z (P n2)) (P n1))
                       (sint_add z (sint_add (P n2) (P n1)))
                       H_x_to_z (sint_add_assoc z (P n2) (P n1))).
    unfold sint_add at 2 in H_tmp.
    exact H_tmp.
  - exists n1.
    left.
    assert (H_x_to_z := sint_eq_trans
                          x
                          (sint_add y (P n1))
                          (sint_add (sint_add z Z) (P n1))
                          H_eq_x_y
                          (sint_add_eq_l
                             y (sint_add z Z) (P n1)
                             H_eq_y_zZ));
      clear H_eq_x_y; clear H_eq_y_zZ.
    exact (sint_eq_trans x
                         (sint_add (sint_add z Z) (P n1))
                         (sint_add z (P n1))
                         H_x_to_z
                         (sint_add_eq_l
                            (sint_add z Z) z (P n1)
                            (sint_add_0_r z))).
  - exists n2.
    left.
    assert (H_x_to_z := sint_eq_trans
                          x
                          (sint_add y Z)
                          (sint_add (sint_add z (P n2)) Z)
                          H_eq_x_yZ
                          (sint_add_eq_l
                             y (sint_add z (P n2)) Z
                             H_eq_y_z));
      clear H_eq_x_yZ; clear H_eq_y_z.
    exact (sint_eq_trans x
                         (sint_add (sint_add z (P n2)) Z)
                         (sint_add z (P n2))
                         H_x_to_z
                         (sint_add_0_r (sint_add z (P n2)))).    
  - exists 0.
    right.
    assert (H_x_to_z := sint_eq_trans
                          x (sint_add y Z) y
                          H_eq_x_yZ
                          (sint_add_0_r y)).
    exact (sint_eq_trans
             x y (sint_add z Z)
             H_x_to_z H_eq_y_zZ).
Qed.

Lemma sint_neq_eq_l :
  forall x y z : sint,
    x == y ->
    sint_neq x z ->
    sint_neq y z.
Proof.
  intros [px |  | nx] [py |  | ny] [pz |  | nz];
    unfold sint_eq, sint_neq;
    intros H_eq H_neq_x_z;
    ((rewrite -> H_eq in H_neq_x_z; exact H_neq_x_z) ||
     exact H_neq_x_z || contradiction H_eq || contradiction H_neq_x_z).
Qed.

Lemma sint_add_pos_eq_itself_is_false_r :
  forall x : sint,
  forall n : nat,
    x == sint_add x (P n) ->
    (* sint_neq x x. *)
    False.
Proof.
  intros x n H_eq.
  Check (sint_add_cancel_r Z (P n) x).
  assert (H_lhs := sint_eq_trans
                     (sint_add Z x) x (sint_add x (P n))
                     (sint_add_0_l x) H_eq).
  assert (H_tmp := sint_eq_trans
                     (sint_add Z x)
                     (sint_add x (P n))
                     (sint_add (P n) x)
                     H_lhs (sint_add_comm x (P n)));
    clear H_lhs.
  assert (H_absurd := sint_add_cancel_r Z (P n) x H_tmp).
  unfold sint_eq in H_absurd.
  exact H_absurd.
Qed.

Proposition sint_gt_trans :
  forall x y z : sint,
    sint_gt x y ->
    sint_gt y z ->
    sint_gt x z.
Proof.
  unfold sint_gt.
  intros x y z [H_ge_x_y H_neq_x_y] [H_ge_y_z H_neq_y_z].
  split.
  - exact (sint_ge_trans x y z H_ge_x_y H_ge_y_z).
  - destruct H_ge_x_y as [n1 [H_eq1 | H_eq1_Z]];
      destruct H_ge_y_z as [n2 [H_eq2 | H_eq2_Z]].
    + assert (H_lhs := sint_eq_trans
                         x
                         (sint_add y (P n1))
                         (sint_add (sint_add z (P n2)) (P n1))
                         H_eq1
                         (sint_add_eq_l
                            y (sint_add z (P n2)) (P n1) H_eq2)).
      Check (sint_add_assoc z (P n2) (P n1)).
      assert (H_rhs := sint_eq_trans
                         x
                         (sint_add (sint_add z (P n2)) (P n1))
                         (sint_add z (sint_add (P n2) (P n1)))
                         H_lhs
                         (sint_add_assoc z (P n2) (P n1))).
      unfold sint_add at 2 in H_rhs.
      apply (sint_neq_eq_l
               (sint_add z (P (n2 + n1 + 1))) x z
               (sint_eq_sym x (sint_add z (P (n2 + n1 + 1))) H_rhs)).
      apply (not_sint_eq_is_sint_neq
               (sint_add z (P (n2 + n1 + 1))) z).
      intro H_eq_absurd.
      exact (sint_add_pos_eq_itself_is_false_r
               z (n2 + n1 + 1)
               (sint_eq_sym (sint_add z (P (n2 + n1 + 1)))
                            z H_eq_absurd)).
    + assert (H_absurd := sint_eq_trans
                            y (sint_add z Z) z
                            H_eq2_Z (sint_add_0_r z)).
      contradiction (sint_neq_and_eq_false
                       y z H_neq_y_z H_absurd).
    (* x == sint_add z (P n1) -> sint_neq x z *)
    + assert (H_absurd := sint_eq_trans
                            x (sint_add y Z) y
                            H_eq1_Z (sint_add_0_r y)).
      contradiction (sint_neq_and_eq_false
                       x y H_neq_x_y H_absurd).
    (* x == sint_add z (P n2) -> sint_neq x z *)
    + assert (H_absurd := sint_eq_trans
                            x (sint_add y Z) y
                            H_eq1_Z
                            (sint_add_0_r y)).
      contradiction (sint_neq_and_eq_false
                       x y H_neq_x_y H_absurd).
Qed.
    
Proposition sint_ge_sym_eq :
  forall x y : sint,
    sint_ge x y ->
    sint_ge y x ->
    x == y.
Proof.
  unfold sint_ge;
    intros x y H_ge_x_y H_ge_y_x.
  destruct H_ge_x_y as [n1 [H_ge_x_y | H_eq_x_y]];
    destruct H_ge_y_x as [n2 [H_ge_y_x | H_eq_y_x]].
  - assert (H_tmp := sint_eq_trans
                       x
                       (sint_add y (P n1))
                       (sint_add (sint_add x (P n2)) (P n1))
                       H_ge_x_y
                       (sint_add_eq_l
                          y (sint_add x (P n2)) (P n1)
                          H_ge_y_x)).
    Check (sint_add_assoc x (P n2) (P n1)).
    assert (H_absurd := sint_eq_trans
                          x
                          (sint_add (sint_add x (P n2)) (P n1))
                          (sint_add x (sint_add (P n2) (P n1)))
                          H_tmp
                          (sint_add_assoc x (P n2) (P n1)));
      clear H_tmp.
    unfold sint_add at 2 in H_absurd.
    Check (sint_add_pos_eq_itself_is_false_r x (n2 + n1 + 1)).
    contradiction (sint_add_pos_eq_itself_is_false_r
                     x (n2 + n1 + 1) H_absurd).
  - (* Follow-up: if there's a contradiction in the assumptions, 
     * is it problematic to prove this subgoal as "true" instead of contradiction? *)
    Check (sint_add_pos_eq_itself_is_false_r x n1).
    apply (sint_eq_sym y x).
    exact (sint_eq_trans
             y (sint_add x Z) x
             H_eq_y_x (sint_add_0_r x)).
  - assert (H_tmp := sint_eq_trans
                       x (sint_add y Z) y
                       H_eq_x_y (sint_add_0_r y)).
    assert (H_absurd := sint_eq_trans
                          x y (sint_add x (P n2))
                          H_tmp H_ge_y_x).
    Check (sint_add_pos_eq_itself_is_false_r x n2).
    contradiction (sint_add_pos_eq_itself_is_false_r
                     x n2 H_absurd).
  - exact (sint_eq_trans
             x (sint_add y Z) y
             H_eq_x_y (sint_add_0_r y)).
Qed.

(* ********** *)

(* end of sint.v *)
