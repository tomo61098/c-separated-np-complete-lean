Require Import Reals.
Require Import Lra Lia.
Require Import Ring.
Require Import Vector.
Require Import Coq.Logic.Eqdep_dec.
Require Import Field.

Import VectorNotations.
Open Scope R_scope.

(* -------- Convexity -------- *)

Definition convex_set (P: R -> Prop) :=
  (forall x y, P x -> P y -> forall t, 0 <= t <= 1 -> P (t * x + (1-t)*y))
.

Definition cond_convex (P: R -> Prop) (f : R -> R) : Prop :=
  convex_set P ->
  forall x y,
    P x -> P y -> forall t,
    0 <= t <= 1 ->
    f (t * x + (1 - t) * y) <= t * f x + (1 - t) * f y.

Definition cond_strict_convex (P: R -> Prop) (f : R -> R) : Prop :=
  convex_set P ->
  forall x y,
    P x -> P y ->
    x <> y ->
    forall t,
    0 < t < 1 ->
    f (t * x + (1 - t) * y) < t * f x + (1 - t) * f y.


Lemma cond_strict_convex_convex: forall P (f: R -> R),
  cond_strict_convex P f -> cond_convex P f
.
Proof.
  intros P f St Hp x y Px Py t N.
  destruct (Req_dec 0 t).
  { subst. rewrite (Rminus_0_r). rewrite ! (Rmult_0_l).
    rewrite ! Rplus_0_l. rewrite ! Rmult_1_l. right. trivial. }
  destruct (Req_dec 1 t).
  { subst. rewrite Rminus_diag. rewrite ! Rmult_1_l. rewrite ! Rmult_0_l.
    rewrite ! Rplus_0_r. right. trivial. }
  destruct (Req_dec x y).
  { subst. field_simplify. replace (t * y + (1 - t)*y) with y by lra.
    right. trivial. }
  left.
  apply St; auto.
  lra.
Qed.

Definition secant_slope (f : R -> R) (x y : R) : R :=
  (f y - f x) / (y - x).

(* -------- Pure Vector.t utilities -------- *)

Fixpoint sumV {n : nat} (v : Vector.t R n) : R :=
  match v with
  | [] => 0
  | x :: xs => x + sumV xs
  end.

(* Sum of all entries of a vector *)
Fixpoint vsum {n : nat} (v : Vector.t R n) : R :=
  match v with
  | [] => 0
  | x :: xs => x + vsum xs
  end.

(* Sum of the first [k] entries of a vector.
   If [k] is bigger than the length, this just returns the full sum. *)
Fixpoint prefix_sum {n : nat} (k : nat) (v : Vector.t R n) : R :=
  match k, v with
  | 0, _ => 0
  | S _, [] => 0
  | S k', x :: xs => x + prefix_sum k' xs
  end.

(* Descending sortedness on vectors *)
Inductive sorted_desc : forall n, Vector.t R n -> Prop :=
| sorted_desc_nil :
    sorted_desc 0 []
| sorted_desc_single :
    forall x,
      sorted_desc 1 [x]
| sorted_desc_cons :
    forall n x y (v : Vector.t R n),
      x >= y ->
      sorted_desc (S n) (y :: v) ->
      sorted_desc (S (S n)) (x :: y :: v).

(* Weak prefix-majorization: no equal-total-sum requirement *)
Definition weak_majorized_raw {n : nat} (v w : Vector.t R n) : Prop :=
  forall k, prefix_sum k v >= prefix_sum k w.

(* Weak majorization with both vectors sorted descending *)
Definition weak_majorized {n : nat} (v w : Vector.t R n) : Prop :=
  sorted_desc n v /\
  sorted_desc n w /\
  weak_majorized_raw v w.

(* Prefix-majorization + equal total sum *)
Definition majorized_raw {n : nat} (v w : Vector.t R n) : Prop :=
  weak_majorized_raw v w /\
  vsum v = vsum w.

(* Standard majorization usually assumes both vectors are sorted descending *)
Definition majorized {n : nat} (v w : Vector.t R n) : Prop :=
  sorted_desc n v /\
  sorted_desc n w /\
  majorized_raw v w.

Lemma majorized_raw_tails :
  forall (n : nat) (h : R) (v w : Vector.t R n),
    majorized_raw (h :: v) (h :: w) ->
    majorized_raw v w.
Proof.
  intros n h v w [Hpref Hsum].
  split.
  - intros k.
    specialize (Hpref (S k)).
    simpl in Hpref.
    lra.
  - simpl in Hsum.
    lra.
Qed.

Lemma weak_majorized_raw_tails :
  forall (n : nat) (h : R) (v w : Vector.t R n),
    weak_majorized_raw (h :: v) (h :: w) ->
    weak_majorized_raw v w.
Proof.
  intros n h v w Hpref.
  intros k.
  specialize (Hpref (S k)).
  simpl in Hpref.
  lra.
Qed.

Ltac inv H := inversion H; subst.
Ltac app_inj_nat H := apply (inj_pair2_eq_dec _ Nat.eq_dec) in H; subst.


Lemma sorted_desc_tail :
  forall (n : nat) (h : R) (v : Vector.t R n),
    sorted_desc (S n) (h :: v) ->
    sorted_desc n v.
Proof.
  intros n h v H.
  destruct v as [| x n' v'].
  - inversion H. constructor.
  - inv H. app_inj_nat H4.
    exact H5.
Qed.

Lemma majorized_tails :
  forall (n : nat) (h : R) (v w : Vector.t R n),
    majorized (h :: v) (h :: w) ->
    majorized v w.
Proof.
  intros n h v w [Hs1 [Hs2 Hmaj]].
  repeat split.
  - apply sorted_desc_tail with (h := h). exact Hs1.
  - apply sorted_desc_tail with (h := h). exact Hs2.
  - apply majorized_raw_tails with (h := h). exact Hmaj.
  - inv Hmaj. simpl in H0. lra.
Qed.

Lemma weak_majorized_tails :
  forall (n : nat) (h : R) (v w : Vector.t R n),
    weak_majorized (h :: v) (h :: w) ->
    weak_majorized v w.
Proof.
  intros n h v w [Hv [Hw Hmaj]].
  repeat split.
  - apply (sorted_desc_tail _ _ _ Hv).
  - apply (sorted_desc_tail _ _ _ Hw).
  - apply (weak_majorized_raw_tails _ h _ _ Hmaj).
Qed.

Inductive sorted_asc : forall n, Vector.t R n -> Prop :=
| sorted_asc_nil :
    sorted_asc 0 []
| sorted_asc_single :
    forall x,
      sorted_asc 1 [x]
| sorted_asc_cons :
    forall n x y (v : Vector.t R n),
      x <= y ->
      sorted_asc (S n) (y :: v) ->
      sorted_asc (S (S n)) (x :: y :: v).

Lemma sorted_asc_tail : forall n (u: Vector.t R (S n)),
  sorted_asc (S n) u -> sorted_asc n (tl u)
.
Proof.
  intros n u H.
  inv H.
  + app_inj_nat H3. constructor.
  + app_inj_nat H2.
    simpl tl. apply H4.
Qed. 

Fixpoint inv_weak_majorized_raw {n : nat} (u v: Vector.t R n) : Prop.
destruct n.
  - apply True.
  - apply (vsum u >= vsum v /\ inv_weak_majorized_raw n (tl u) (tl v)).
Defined.

Lemma vsum_pref_sum: forall n k (u: Vector.t R n),
  prefix_sum (k + n) u = vsum u
.
Proof.
  induction n; intros k u.
    - rewrite (nil_spec u). destruct k; trivial.
    - rewrite (eta u). rewrite Nat.add_succ_r. simpl. f_equal. apply IHn.
Qed.

Lemma prefix_sum_shiftin_leq: forall n k (x: R) (u: Vector.t R n),
  (k <= n)%nat -> prefix_sum k (shiftin x u) = prefix_sum k u
.
Proof.
  induction n, k.
  - trivial.
  - intros. lia.
  - trivial.
  - intros.
    rewrite (eta u). simpl.
    rewrite IHn by lia.
    lra.
Qed.

Lemma vsum_shift : forall n x (u: Vector.t R n),
  vsum (shiftin x u) = vsum u + x
.
Proof.
  induction n; intros x u.
  - rewrite (nil_spec u). simpl. lra.
  - rewrite (eta u).
    simpl. rewrite IHn. lra.
Qed.

Lemma weak_majorized_raw_shiftin : forall n (x y: R) (u v: Vector.t R n),
  weak_majorized_raw (shiftin x u) (shiftin y v)
  -> weak_majorized_raw u v
.
Proof.
  intros n x y u v Hf k.
  destruct (Compare_dec.le_dec k n).
  - specialize (Hf k).
    rewrite 2 (prefix_sum_shiftin_leq _ _ _ _ l) in Hf.
    apply Hf.
  - assert (N: forall a b, (a < b -> exists c, b = c + S a)%nat).
    { induction a, b; intros L.
      + exists O. lia.
      + exists (b). lia.
      + lia.
      + assert (E: (a < b)%nat) by lia.
        destruct (IHa _ E). exists x0. lia.
    }
    assert (E: (n < k)%nat) by lia.
    destruct (N _ _ E).
    assert (F2:= Hf n).
    rewrite 2 prefix_sum_shiftin_leq in F2 by lia.
    subst k.
    rewrite <- (Nat.add_succ_comm).
    rewrite 2 (vsum_pref_sum n (S x0)).
    assert (M:= vsum_pref_sum n O).
    simpl in M.
    rewrite 2 M in F2.
    lra.
Qed.

Lemma weak_majorized_raw_rev : forall n (u v: Vector.t R (S n)),
  weak_majorized_raw (rev u) (rev v) ->
  weak_majorized_raw (rev (tl u)) (rev (tl v))
.
Proof.
  intros n u v H k.
  rewrite (eta u), (eta v) in H.
  rewrite 2 rev_cons in H.
  simpl in H.
  apply weak_majorized_raw_shiftin in H.
  apply H.
Qed.

Lemma vsum_rev: forall n (u: Vector.t R n),
  vsum (rev u) = vsum u
.
Proof.
  induction n; intros u.
  - rewrite (nil_spec (rev u)), (nil_spec u). trivial.
  - rewrite (eta u).
    rewrite rev_cons.
    simpl. rewrite vsum_shift. rewrite IHn. lra.
Qed.

Lemma majorized_raw_if_inv_majorized_raw :
  forall n (u v: Vector.t R n),
  weak_majorized_raw (rev u) (rev v) -> inv_weak_majorized_raw u v
.
Proof.
  induction n; intros u v Hw.
  - exact I.
  - simpl. split.
    + specialize (Hw (S n)).
      assert (Hww:= vsum_pref_sum (S n) O).
      simpl plus in Hww.
      rewrite 2 (Hww) in Hw.
      rewrite 2 vsum_rev in Hw. apply Hw.
    + apply IHn.
      apply weak_majorized_raw_rev.
      apply Hw.
Qed.

Lemma inv_majorized_raw_if_majorized_raw :
  forall n (u v: Vector.t R n),
  inv_weak_majorized_raw u v -> weak_majorized_raw (rev u) (rev v).
Proof.
  induction n; intros u v Hf k.
  - rewrite 2 (nil_spec (rev _)). destruct k; right; trivial.
  - rewrite (eta u), (eta v). rewrite 2 rev_cons.
    destruct (Compare_dec.le_dec k n).
    + rewrite 2 (prefix_sum_shiftin_leq _ _ _ _ l).
      apply IHn. apply Hf.
    + assert (N: forall a b, (a < b -> exists c, b = c + S a)%nat).
    { induction a, b; intros L.
      + exists O. lia.
      + exists (b). lia.
      + lia.
      + assert (E: (a < b)%nat) by lia.
        destruct (IHa _ E). exists x. lia.
    }
    assert (E: (n < k)%nat) by lia.
    destruct (N _ _ E).
    rewrite H.
    rewrite 2 vsum_pref_sum.
    rewrite 2 vsum_shift.
    destruct Hf as [L Hf].
    rewrite 2 vsum_rev.
    rewrite (eta u), (eta v) in L.
    simpl in L. lra.
Qed.

Lemma vsum_singleout : forall n x (u : Vector.t R n),
  vsum (x :: u) - vsum u = x.
Proof. intros. simpl. lra. Qed.

Fixpoint Ksum {n : nat} (f : R -> R) (u v: Vector.t R n) : R .
destruct n.
  - apply 0.
  - apply (f (hd u) - f (hd v) + Ksum n f (tl u) (tl v)).
Defined.

Fixpoint Ksum_delta {n : nat} (f : R -> R) (u v: Vector.t R n) : R .
destruct n.
  - apply 0.
  - apply (secant_slope f (hd u) (hd v) * (hd u - hd v) + Ksum_delta n f (tl u) (tl v)).
Defined.

Lemma Ksum_to_Ksum_delta : forall n f (u v: Vector.t R n),
  Ksum f u v = Ksum_delta f u v.
Proof.
  induction n.
  - trivial.
  - intros f u v.
    simpl. unfold secant_slope.
    destruct (Req_dec (hd u) (hd v)); rewrite IHn.
    + rewrite H. lra.
    + field. lra.
Qed.

Fixpoint KPsum {n : nat} (f : R -> R) (u v: Vector.t R n): R.
destruct n.
  - apply 0.
  - apply (secant_slope f (hd u) (hd v) * (vsum u - vsum v) + KPsum n f (tl u) (tl v)).
Defined.

Fixpoint KPSsum {n : nat} (f : R -> R) (u v: Vector.t R n): R.
destruct n.
  - apply 0.
  - apply (secant_slope f (hd u) (hd v) * (vsum (tl u) - vsum (tl v)) + KPSsum n f (tl u) (tl v)).
Defined.

Lemma Ksum_delta_to_KPsumS : forall n f (u v: Vector.t R n),
  Ksum_delta f u v = KPsum f u v - KPSsum f u v
.
Proof.
  induction n.
  - simpl. intros. lra.
  - intros f u v.
    simpl. rewrite IHn.
    replace (vsum u - vsum v) with (hd u - hd v + vsum (tl u) - vsum (tl v)).
    2:{ rewrite (eta u), (eta v). simpl. lra. }
    lra.
Qed.


Fixpoint KPSsum_deltaS {n : nat} (f: R -> R) (u v: Vector.t R (S n)) {struct n}: R.
destruct n.
  + apply 0.
  + apply ((secant_slope f (hd (tl u)) (hd (tl v)) - secant_slope f (hd u) (hd v)) * (vsum (tl u) - vsum (tl v)) + KPSsum_deltaS (n) f (tl u) (tl v)).
Defined.

Lemma KPSsumS_to_KPSsum_deltaS : forall n f (u v: Vector.t R (S n)),
  KPsum f u v - KPSsum f u v = (secant_slope f (hd u) (hd v)) * (vsum u - vsum v) + KPSsum_deltaS f u v.
Proof.
  induction n; intros f u v.
  - rewrite (eta u), (eta v). rewrite (nil_spec (VectorDef.tl u)), (nil_spec (VectorDef.tl v)). simpl. lra.
  - simpl. field_simplify.
    replace (
      secant_slope f (hd u) (hd v) * vsum u -
      secant_slope f (hd u) (hd v) * vsum v -
      secant_slope f (hd u) (hd v) * vsum (tl u) +
      secant_slope f (hd u) (hd v) * vsum (tl v) +
      secant_slope f (hd (tl u)) (hd (tl v)) * vsum (tl u) -
      secant_slope f (hd (tl u)) (hd (tl v)) * vsum (tl v) +
      KPSsum_deltaS f (tl u) (tl v)
    ) with
    (
      secant_slope f (hd u) (hd v) * vsum u -
      secant_slope f (hd u) (hd v) * vsum v -
      secant_slope f (hd u) (hd v) * vsum (tl u) +
      secant_slope f (hd u) (hd v) * vsum (tl v) +
      (secant_slope f (hd (tl u)) (hd (tl v)) * (vsum (tl u) -
      vsum (tl v)) +
      KPSsum_deltaS f (tl u) (tl v))
    ) by lra.
    rewrite <- IHn. simpl.
    lra.
Qed.

Lemma Ksum_to_KPSsum_deltaS : forall n f (u v: Vector.t R (S n)),
  Ksum f u v = (secant_slope f (hd u) (hd v)) * (vsum u - vsum v) + KPSsum_deltaS f u v
.
Proof.
  intros.
  rewrite Ksum_to_Ksum_delta.
  rewrite Ksum_delta_to_KPsumS.
  apply KPSsumS_to_KPSsum_deltaS.
Qed.

Lemma Ksum_to_KPSsum_deltaS_neg :
  forall n f (u v: Vector.t R (S n)),
  Ksum f u v - (secant_slope f (hd u) (hd v)) * (vsum u - vsum v) = KPSsum_deltaS f u v
.
Proof. intros. rewrite Ksum_to_KPSsum_deltaS. lra. Qed.

Lemma Ksum_head: forall n f x (u v: Vector.t R n),
  Ksum f (x::u) (x::v) = Ksum f u v
.
Proof. intros. simpl. lra. Qed.

Lemma KPSum_deltaS_head : forall n f x (u v: Vector.t R (S n)),
  KPSsum_deltaS f (x::u) (x::v) = secant_slope f (hd u) (hd v) * (vsum u - vsum v) + KPSsum_deltaS f u v
.
Proof.
  intros n f x u v.
  rewrite <- 1 Ksum_to_KPSsum_deltaS_neg.
  rewrite Ksum_head.
  simpl hd. unfold secant_slope at 1.
  rewrite ! Rminus_diag.
  rewrite Rdiv_0_r.
  rewrite Rmult_0_l.
  rewrite Rminus_0_r.
  apply Ksum_to_KPSsum_deltaS.
Qed.
  

Definition inv_weak_majorized {n : nat} (u v: Vector.t R n) :=
  sorted_asc n u /\
  sorted_asc n v /\
  inv_weak_majorized_raw u v
.

Definition inv_majorized {n : nat} (u v: Vector.t R n) :=
  inv_weak_majorized u v /\
  vsum u = vsum v
.

(* Convexity *)

Lemma frac_between_0_1 :
  forall x y z : R,
    x < y < z ->
    0 < (z - y) / (z - x) < 1.
Proof.
  intros x y z H.
  destruct H as [Hxy Hyz].
  assert (Hzx : 0 < z - x) by lra.
  split.
  - apply Rdiv_lt_0_compat; lra.
  - apply (Rmult_lt_reg_l (z - x)); try lra.
    rewrite Rmult_1_r.
    rewrite Rmult_comm.
    rewrite <- Rmult_div_swap.
    rewrite Rmult_div_l; lra.
Qed.

Lemma strict_convex_secant_mono_l_l :
  forall P (f : R -> R),
    convex_set P ->
    cond_strict_convex P f ->
    forall x y z,
      P x -> P y -> P z ->
      x < y < z ->
      secant_slope f x y < secant_slope f x z.
Proof.
  intros P f Hp Hconv x y z Px Py Pz Hxyz.
  destruct Hxyz as [Hxy Hyz].

  set (t := (z - y) / (z - x)).

  assert (Ht : 0 < t < 1).
  { apply frac_between_0_1; lra. }

  assert (Hy :
    y = t * x + (1 - t) * z).
  {
    unfold t.
    field.
    lra.
  }

  assert (Hc : f y < t * f x + (1 - t) * f z).
  {
    rewrite Hy.
    apply Hconv; auto.
    lra.
  }

  assert (Ht' : 1 - t = (y - x) / (z - x)).
  {
    unfold t.
    field.
    lra.
  }

  assert (Hstep :
    f y - f x < ((y - x) / (z - x)) * (f z - f x)).
  {
    replace (t * f x) with ((1 - (1 - t)) * f x) in Hc by lra.
    rewrite (Rmult_minus_distr_r (f x)) in Hc.
    rewrite Rmult_1_l in Hc.
    rewrite Ht' in Hc.
    unfold t in Hc.
    lra.
  }

  unfold secant_slope.
  apply (Rmult_lt_reg_r (y - x)).
  { lra. }

  replace (((f y - f x) / (y - x)) * (y - x)) with (f y - f x).
  2:{
    field.
    lra.
  }

  replace (((f z - f x) / (z - x)) * (y - x))
    with (((y - x) / (z - x)) * (f z - f x)).
  2:{
    field.
    lra.
  }

  exact Hstep.
Qed.

Lemma convex_secant_mono_l_l :
  forall P (f : R -> R),
    convex_set P ->
    cond_convex P f ->
    forall x y z,
      P x -> P y -> P z ->
      x < y < z ->
      secant_slope f x y <= secant_slope f x z.
Proof.
  intros P f Hp Hconv x y z Px Py Pz Hxyz.
  destruct Hxyz as [Hxy Hyz].

  set (t := (z - y) / (z - x)).

  assert (Ht : 0 < t < 1).
  { apply frac_between_0_1; lra. }

  assert (Hy :
    y = t * x + (1 - t) * z).
  {
    unfold t.
    field.
    lra.
  }

  assert (Hc : f y <= t * f x + (1 - t) * f z).
  {
    rewrite Hy.
    apply Hconv; auto.
    lra.
  }

  assert (Ht' : 1 - t = (y - x) / (z - x)).
  {
    unfold t.
    field.
    lra.
  }

  assert (Hstep :
    f y - f x <= ((y - x) / (z - x)) * (f z - f x)).
  {
    replace (t * f x) with ((1 - (1 - t)) * f x) in Hc by lra.
    rewrite (Rmult_minus_distr_r (f x)) in Hc.
    rewrite Rmult_1_l in Hc.
    rewrite Ht' in Hc.
    unfold t in Hc.
    lra.
  }

  unfold secant_slope.
  apply (Rmult_le_reg_r (y - x)).
  { lra. }

  replace (((f y - f x) / (y - x)) * (y - x)) with (f y - f x).
  2:{
    field.
    lra.
  }

  replace (((f z - f x) / (z - x)) * (y - x))
    with (((y - x) / (z - x)) * (f z - f x)).
  2:{
    field.
    lra.
  }

  exact Hstep.
Qed.


Lemma sub_div_sym_explicit :
  forall a b c d : R,
    (a - b) / (c - d) = (b - a) / (d - c).
Proof.
  intros a b c d.
  unfold Rdiv.
  replace (b - a) with (-(a - b)) by lra.
  replace (d - c) with (-(c - d)) by lra.
  rewrite Rinv_opp.
  ring.
Qed.

Lemma convex_secant_mono_l_m :
  forall P (f : R -> R),
    convex_set P ->
    cond_convex P f ->
    forall x y z,
      P x -> P y -> P z ->
      y < x < z ->
      secant_slope f x y <= secant_slope f x z.
Proof.
  intros P f Hp Hconv x y z Px Py Pz [Hyx Hxz].
  unfold secant_slope.

  assert (Hyz : y < z) by lra.

  assert
    (Haux :
      (z - y) * f x <= (z - x) * f y + (x - y) * f z).
  {
    specialize (Hconv Hp y z Py Pz ((z - x) / (z - y))).
    assert (Ht : 0 <= (z - x) / (z - y) <= 1).
    { assert (0 < (z - x) / (z - y) < 1) by (apply frac_between_0_1; lra). lra. }
    specialize (Hconv Ht).

    replace
      (((z - x) / (z - y)) * y +
       (1 - (z - x) / (z - y)) * z)
    with x in Hconv.
    2:{ field; lra. }

    replace
      ((z - x) / (z - y) * f y +
       (1 - (z - x) / (z - y)) * f z)
    with
      (((z - x) * f y + (x - y) * f z) / (z - y)) in Hconv.
    2:{ field; lra. }

    apply (Rmult_le_compat_l (z - y)) in Hconv; [|lra].
    field_simplify in Hconv; lra.
  }

  apply (Rmult_le_reg_l ((x - y) * (z - x))).
  { nra. }
  rewrite (sub_div_sym_explicit _ _ y x).
  field_simplify; nra.
Qed.

Lemma strict_convex_secant_mono_l_m :
  forall P (f : R -> R),
    convex_set P ->
    cond_strict_convex P f ->
    forall x y z,
      P x -> P y -> P z ->
      y < x < z ->
      secant_slope f x y < secant_slope f x z.
Proof.
  intros P f Hp Hconv x y z Px Py Pz [Hyx Hxz].
  unfold secant_slope.

  assert (Hyz : y < z) by lra.

  assert
    (Haux :
      (z - y) * f x < (z - x) * f y + (x - y) * f z).
  {
    assert (y <> z) by lra.
    specialize (Hconv Hp y z Py Pz H ((z - x) / (z - y))).
    assert (Ht: 0 < (z - x) / (z - y) < 1) by (apply frac_between_0_1; lra).
    specialize (Hconv Ht).

    replace
      (((z - x) / (z - y)) * y +
       (1 - (z - x) / (z - y)) * z)
    with x in Hconv.
    2:{ field; lra. }

    replace
      ((z - x) / (z - y) * f y +
       (1 - (z - x) / (z - y)) * f z)
    with
      (((z - x) * f y + (x - y) * f z) / (z - y)) in Hconv.
    2:{ field; lra. }

    apply (Rmult_lt_compat_l (z - y)) in Hconv; [|lra].
    field_simplify in Hconv; lra.
  }

  apply (Rmult_lt_reg_l ((x - y) * (z - x))).
  { nra. }
  rewrite (sub_div_sym_explicit _ _ y x).
  field_simplify; nra.
Qed.

Lemma convex_secant_mono_l_r :
  forall P (f : R -> R),
    convex_set P ->
    cond_convex P f ->
    forall x y z,
      P x -> P y -> P z ->
      y < z < x ->
      secant_slope f x y <= secant_slope f x z.
Proof.
  intros P f Hp Hconv x y z Px Py Pz [Hyz Hzx].
  unfold secant_slope.

  assert (Hyx : y < x) by lra.

  assert
    (Haux :
      (x - y) * f z <= (x - z) * f y + (z - y) * f x).
  {
    specialize (Hconv Hp y x Py Px ((x - z) / (x - y))).
    assert (Ht : 0 <= (x - z) / (x - y) <= 1).
    { assert (0 < (x - z) / (x - y) < 1) by (apply frac_between_0_1; lra). lra. }
    specialize (Hconv Ht).

    replace
      (((x - z) / (x - y)) * y +
       (1 - (x - z) / (x - y)) * x)
    with z in Hconv.
    2:{ field; lra. }

    replace
      ((x - z) / (x - y) * f y +
       (1 - (x - z) / (x - y)) * f x)
    with
      (((x - z) * f y + (z - y) * f x) / (x - y)) in Hconv.
    2:{ field; lra. }

    apply (Rmult_le_compat_l (x - y)) in Hconv; [|lra].
    field_simplify in Hconv; lra.
  }

  apply (Rmult_le_reg_l ((x - y) * (x - z))); [nra|].
  rewrite 2 (sub_div_sym_explicit _ _ _ x).
  field_simplify; nra.
Qed.

Lemma strict_convex_secant_mono_l_r :
  forall P (f : R -> R),
    convex_set P ->
    cond_strict_convex P f ->
    forall x y z,
      P x -> P y -> P z ->
      y < z < x ->
      secant_slope f x y < secant_slope f x z.
Proof.
  intros P f Hp Hconv x y z Px Py Pz [Hyz Hzx].
  unfold secant_slope.

  assert (Hyx : y < x) by lra.

  assert
    (Haux :
      (x - y) * f z < (x - z) * f y + (z - y) * f x).
  {
    assert (y <> x) by lra.
    specialize (Hconv Hp y x Py Px H ((x - z) / (x - y))).
    assert (Ht : 0 < (x - z) / (x - y) < 1).
    { apply frac_between_0_1. lra. }
    specialize (Hconv Ht).

    replace
      (((x - z) / (x - y)) * y +
       (1 - (x - z) / (x - y)) * x)
    with z in Hconv.
    2:{ field; lra. }

    replace
      ((x - z) / (x - y) * f y +
       (1 - (x - z) / (x - y)) * f x)
    with
      (((x - z) * f y + (z - y) * f x) / (x - y)) in Hconv.
    2:{ field; lra. }

    apply (Rmult_lt_compat_l (x - y)) in Hconv; [|lra].
    field_simplify in Hconv; lra.
  }

  apply (Rmult_lt_reg_l ((x - y) * (x - z))); [nra|].
  rewrite 2 (sub_div_sym_explicit _ _ _ x).
  field_simplify; nra.
Qed.


Lemma secant_sym :
  forall (f : R -> R) x y,
    secant_slope f x y = secant_slope f y x.
Proof.
  intros f x y.
  unfold secant_slope.
  apply sub_div_sym_explicit.
Qed.

Lemma convex_secant_mono_r_l :
  forall P (f : R -> R),
    convex_set P ->
    cond_convex P f ->
    forall x y z,
      P x -> P y -> P z ->
      x < y < z ->
      secant_slope f y x <= secant_slope f z x.
Proof.
  intros P f Hp Hconv x y z Px Py Pz Hxyz.
  rewrite (secant_sym f y x) by lra.
  rewrite (secant_sym f z x) by lra.
  apply (convex_secant_mono_l_l P); auto.
Qed.

Lemma strict_convex_secant_mono_r_l :
  forall P (f : R -> R),
    convex_set P ->
    cond_strict_convex P f ->
    forall x y z,
      P x -> P y -> P z ->
      x < y < z ->
      secant_slope f y x < secant_slope f z x.
Proof.
  intros P f Hp Hconv x y z Px Py Pz Hxyz.
  rewrite (secant_sym f y x) by lra.
  rewrite (secant_sym f z x) by lra.
  apply (strict_convex_secant_mono_l_l P); auto.
Qed.

Lemma convex_secant_mono_r_m :
  forall P (f : R -> R),
    convex_set P ->
    cond_convex P f ->
    forall x y z,
      P x -> P y -> P z ->
      y < x < z ->
      secant_slope f y x <= secant_slope f z x.
Proof.
  intros P f Hconv Hp x y z Px Py Pz Hxyz.
  rewrite (secant_sym f y x) by lra.
  rewrite (secant_sym f z x) by lra.
  apply (convex_secant_mono_l_m P); assumption.
Qed.

Lemma strict_convex_secant_mono_r_m :
  forall P (f : R -> R),
    convex_set P ->
    cond_strict_convex P f ->
    forall x y z,
      P x -> P y -> P z ->
      y < x < z ->
      secant_slope f y x < secant_slope f z x.
Proof.
  intros P f Hconv Hp x y z Px Py Pz Hxyz.
  rewrite (secant_sym f y x) by lra.
  rewrite (secant_sym f z x) by lra.
  apply (strict_convex_secant_mono_l_m P); assumption.
Qed.

Lemma convex_secant_mono_r_r :
  forall P (f : R -> R),
    convex_set P ->
    cond_convex P f ->
    forall x y z,
      P x -> P y -> P z ->
      y < z < x ->
      secant_slope f y x <= secant_slope f z x.
Proof.
  intros P f Hconv Hp x y z Px Py Pz Hxyz.
  rewrite (secant_sym f y x) by lra.
  rewrite (secant_sym f z x) by lra.
  apply (convex_secant_mono_l_r P); assumption.
Qed.

Lemma strict_convex_secant_mono_r_r :
  forall P (f : R -> R),
    convex_set P ->
    cond_strict_convex P f ->
    forall x y z,
      P x -> P y -> P z ->
      y < z < x ->
      secant_slope f y x < secant_slope f z x.
Proof.
  intros P f Hconv Hp x y z Px Py Pz Hxyz.
  rewrite (secant_sym f y x) by lra.
  rewrite (secant_sym f z x) by lra.
  apply (strict_convex_secant_mono_l_r P); assumption.
Qed.

Lemma convex_secant_mono_l :
  forall P (f : R -> R),
    convex_set P ->
    cond_convex P f ->
    forall x y z,
      P x -> P y -> P z ->
      x <> y ->
      x <> z ->
      y < z ->
      secant_slope f x y <= secant_slope f x z.
Proof.
  intros P f Hconv Hp x y z Px Py Pz Hxy Hxz Hyz.
  destruct (Rtotal_order x y) as [H1|[H1|H1]];
  destruct (Rtotal_order x z) as [H2|[H2|H2]];
  try lra;
  [
    apply (convex_secant_mono_l_l P)|
    apply (convex_secant_mono_l_m P)|
    apply (convex_secant_mono_l_r P)
  ]; auto; lra.
Qed.

Lemma strict_convex_secant_mono_l :
  forall P (f : R -> R),
    convex_set P ->
    cond_strict_convex P f ->
    forall x y z,
      P x -> P y -> P z ->
      x <> y ->
      x <> z ->
      y < z ->
      secant_slope f x y < secant_slope f x z.
Proof.
  intros P f Hconv Hp x y z Px Py Pz Hxy Hxz Hyz.
  destruct (Rtotal_order x y) as [H1|[H1|H1]];
  destruct (Rtotal_order x z) as [H2|[H2|H2]];
  try lra;
  [
    apply (strict_convex_secant_mono_l_l P) |
    apply (strict_convex_secant_mono_l_m P) |
    apply (strict_convex_secant_mono_l_r P)
  ]; auto; lra.
Qed.

Lemma convex_secant_mono_r :
  forall P (f : R -> R),
    convex_set P ->
    cond_convex P f ->
    forall x y z,
      P x -> P y -> P z ->
      x <> y ->
      x <> z ->
      y < z ->
      secant_slope f y x <= secant_slope f z x.
Proof.
  intros P f Hconv Hp x y z Px Py Pz Hxy Hxz Hyz.
  destruct (Rtotal_order x y) as [H1|[H1|H1]];
  destruct (Rtotal_order x z) as [H2|[H2|H2]];
  try lra;
  [
    apply (convex_secant_mono_r_l P) |
    apply (convex_secant_mono_r_m P) |
    apply (convex_secant_mono_r_r P)
  ]; auto; lra.
Qed.

Lemma strict_convex_secant_mono_r :
  forall P (f : R -> R),
    convex_set P ->
    cond_strict_convex P f ->
    forall x y z,
      P x -> P y -> P z ->
      x <> y ->
      x <> z ->
      y < z ->
      secant_slope f y x < secant_slope f z x.
Proof.
  intros P f Hconv Hp x y z Px Py Pz Hxy Hxz Hyz.
  destruct (Rtotal_order x y) as [H1|[H1|H1]];
  destruct (Rtotal_order x z) as [H2|[H2|H2]];
  try lra;
  [
    apply (strict_convex_secant_mono_r_l P) |
    apply (strict_convex_secant_mono_r_m P) |
    apply (strict_convex_secant_mono_r_r P)
  ]; auto; lra.
Qed.

Lemma convex_secant_mono : forall P f x1 x2 y1 y2,
  convex_set P ->
  cond_convex P f ->
  P x1 -> P x2 -> P y1 -> P y2 ->
  x1 <> y1 ->
  x2 <> y2 ->
  x1 < x2 ->
  y1 < y2 ->
  secant_slope f x1 y1 <= secant_slope f x2 y2
.
Proof.
  intros.
  destruct (Req_dec x1 y2).
  - subst.
    rewrite secant_sym.
    apply (convex_secant_mono_r P); auto.
    lra.
  - assert (A:= convex_secant_mono_l P f H H0 x1 y1 y2 H1 H3 H4 H5 H9 H8).
    assert (B:= convex_secant_mono_r P f H H0 y2 x1 x2 H4 H1 H2).
    lra.
Qed.

Lemma strict_convex_secant_mono : forall P f x1 x2 y1 y2,
  convex_set P ->
  cond_strict_convex P f ->
  P x1 -> P x2 -> P y1 -> P y2 ->
  x1 <> y1 ->
  x2 <> y2 ->
  x1 < x2 ->
  y1 < y2 ->
  secant_slope f x1 y1 < secant_slope f x2 y2
.
Proof.
  intros.
  destruct (Req_dec x1 y2).
  - subst.
    rewrite secant_sym.
    apply (strict_convex_secant_mono_r P); auto.
    lra.
  - assert (A:= strict_convex_secant_mono_l P f H H0 x1 y1 y2 H1 H3 H4 H5 H9 H8).
    assert (B:= strict_convex_secant_mono_r P f H H0 y2 x1 x2 H4 H1 H2).
    lra.
Qed.


(* Karamata *)

Fixpoint all_neq {n : nat} (u v: Vector.t R n): Prop.
destruct n.
  - apply True.
  - apply ((hd u) <> (hd v) /\ all_neq n (tl u) (tl v)).
Defined.

Theorem inv_Karamata_neq : forall n P f (u v: Vector.t R (S n)),
  convex_set P ->
  Forall P u ->
  Forall P v ->
  cond_convex P f ->
  all_neq u v ->
  inv_weak_majorized u v ->
  0 <= KPSsum_deltaS f u v
.
Proof.
  induction n; intros P f u v Hp Pu Pv Hconv [Huv Hneq] [Hu [Hv Hmajo]].
  - right. trivial.
  - simpl.
    assert (Phu: P (hd u)).
    { inv Pu. app_inj_nat H0. auto. }
    assert (Ptu: Forall P (tl u)).
    { inv Pu. app_inj_nat H0. auto. }
    assert (Phv: P (hd v)).
    { inv Pv. app_inj_nat H0. auto. }
    assert (Ptv: Forall P (tl v)).
    { inv Pv. app_inj_nat H0. auto. }
    specialize (IHn P f (tl u) (tl v) Hp Ptu Ptv Hconv Hneq).
    destruct Hmajo as [L1 Hmajo].
    destruct Hneq as [Huv1 Hneq].
    inv Hu. app_inj_nat H0.
    inv Hv. app_inj_nat H0.
    assert (IHn2 : 0 <= KPSsum_deltaS f (y::v0) (y0::v1)).
    { apply IHn. split; auto. }
    destruct Hmajo as [L Hmajo].
    simpl. simpl in Hmajo, L.
    simpl hd in *.
    simpl tl in *.
    assert (Py: P y).
    { inv Ptu. app_inj_nat H5. auto. }
    assert (Py0: P y0).
    { inv Ptv. app_inj_nat H5. auto. }
    destruct H1, H3; subst.
    + assert (A:= convex_secant_mono P f x y x0 y0 Hp Hconv Phu Py Phv Py0 Huv Huv1 H H0).
      apply Rplus_le_le_0_compat; [|lra].
      apply Rmult_le_pos; lra.
    + assert (A:= convex_secant_mono_r P f Hp Hconv y0 x y Py0 Phu Py (not_eq_sym Huv) (not_eq_sym Huv1) H).
      apply Rplus_le_le_0_compat; [|lra].
      apply Rmult_le_pos; lra.
    + assert (A:= convex_secant_mono_l P f Hp Hconv y x0 y0 Py Phv Py0 Huv Huv1 H0).
      apply Rplus_le_le_0_compat; [|lra].
      apply Rmult_le_pos; lra.
    + rewrite Rminus_diag. rewrite Rmult_0_l. rewrite Rplus_0_l.
      apply IHn2.
Qed.


Definition lt_all {n: nat} x (u: Vector.t R n):=
  Forall (fun y => x <= y) u
.

Lemma lt_all_trans : forall x y,
  x <= y -> forall n u,
  @lt_all n y u -> @lt_all n x u
.
Proof.
  intros.
  assert (C: forall a, y <= a -> x <= a).
  { intros. lra. }
  assert (B:= Forall_impl R (fun a => y <= a) (fun a => x <= a) C n u).
  apply B. apply H0.
Qed.

Lemma sorted_asc_lt_all_head : forall n (u: Vector.t R (S n)),
  sorted_asc _ u -> lt_all (hd u) (tl u)
.
Proof.
  induction n; intros u A.
  - rewrite (nil_spec). constructor.
  - rewrite (eta (tl u)).
    inv A. app_inj_nat H0.
    simpl in *.
    constructor.
    -- apply H1.
    -- specialize (IHn (y :: v) H2).
       simpl in IHn.
       apply (lt_all_trans x y); auto.
Qed.

Lemma lt_all_sorted_asc : forall n x (u: Vector.t R n),
  sorted_asc n u -> lt_all x u -> sorted_asc (S n) (x::u)
.
Proof.
  induction n; intros x u A B.
  - rewrite (nil_spec u); constructor.
  - rewrite (eta u). constructor.
    -- inv B. app_inj_nat H0.
       auto.
    -- apply IHn.
      + apply (sorted_asc_tail _ _ A).
      + apply sorted_asc_lt_all_head. auto.
Qed.

Lemma in_tl_in : forall n (u: Vector.t R (S n)) x,
  In x (tl u) -> In x u
.
Proof. intros. rewrite (eta u). constructor. apply H. Qed.

Lemma in_tl_or : forall n x (u: Vector.t R (S n)),
  In x u -> x = hd u \/ In x (tl u)
.
Proof.
  intros. rewrite (eta u) in H.
  destruct (Req_dec x (hd u)).
  - left. apply H0.
  - right. inv H.
    + contradiction.
    + app_inj_nat H4. apply H3.
Qed.

Lemma lt_in_step: forall n x y (u: Vector.t R n),
  lt_all x u -> In y u -> x <= y
.
Proof.
  induction n; intros x y u A B.
  - rewrite (nil_spec u) in B. inv B.
  - rewrite (eta u) in A, B.
    inv B; app_inj_nat H2; inv A.
    + auto.
    + app_inj_nat H2. apply (IHn _ _ _ H4 H1).
Qed.

Lemma lt_in_all: forall m n x (u: Vector.t R n) (v: Vector.t R m),
  Forall (fun a => In a u) v ->
  lt_all x u -> lt_all x v
.
Proof.
  induction m; intros n x u v F L.
    - rewrite (nil_spec v). constructor.
    - rewrite (eta v). constructor.
      -- apply (lt_in_step n _ _ u).
        + apply L.
        + inv F. app_inj_nat H0. auto.
      -- apply (IHm _ x u).
        + rewrite (eta v) in F.
          inv F. app_inj_nat H1.
          auto.
        + apply L.
Qed.

Lemma inv_weak_majorized_raw_vsum: forall n (u v: Vector.t R n),
  inv_weak_majorized_raw u v -> vsum u >= vsum v
.
Proof.
  destruct n; intros u v M.
  - rewrite (nil_spec u), (nil_spec v). lra.
  - destruct M as [L _].
    apply L.
Qed.

Lemma Rge_left: forall x y a b,
  a + b >= x + y <-> a + b - y >= x
.
Proof.
  intros.
  split; lra.
Qed.

Lemma exist_Ksum_prime : forall n f (u v: Vector.t R n),
  exists m u' v',
  @all_neq m u' v' /\
  (Forall (fun a => In a u) u') /\
  (Forall (fun a => In a v) v') /\
  (sorted_asc _ u -> sorted_asc _ u') /\
  (sorted_asc _ v -> sorted_asc _ v') /\
  (inv_weak_majorized_raw u v -> inv_weak_majorized_raw u' v') /\
  (vsum u - vsum v = vsum u' - vsum v') /\
  Ksum f u v = Ksum f u' v'
.
Proof.
  induction n; intros f u v.
  - exists O, [], [].
    rewrite (nil_spec u), (nil_spec v).
    repeat constructor.
  - specialize (IHn f (tl u) (tl v)).
    destruct IHn as [m [u' [v' [Nuv [Au [Av [Su [Sv [W [V K]]]]]]]]]].
    destruct (Req_dec (hd u) (hd v)).
    + exists m, u', v'.
      repeat constructor.
      * auto.
      * apply (Forall_impl R (fun a => In a (tl u)) (fun a => In a u) (in_tl_in _ _) _ u').
        auto.
      * apply (Forall_impl R (fun a => In a (tl v)) (fun a => In a v) (in_tl_in _ _) _ v').
        auto.
      * intros A. apply Su.
        apply sorted_asc_tail, A.
      * intros A. apply Sv.
        apply sorted_asc_tail, A.
      * intros [L A].
        apply (W A).
      * rewrite (eta u), (eta v).
        rewrite H. simpl. lra.
      * simpl. rewrite H. lra.
    + exists _, (hd u :: u'), (hd v :: v').
      repeat (split).
      * apply H.
      * apply Nuv.
      * constructor.
        ** rewrite (eta u). constructor.
        **
       apply (Forall_impl R (fun a => In a (tl u)) (fun a => In a u) (in_tl_in _ _) _ u').
        auto.
      * constructor.
        ** rewrite (eta v). constructor.
        ** apply (Forall_impl R (fun a => In a (tl v)) (fun a => In a v) (in_tl_in _ _) _ v').
        auto.
      * intros A.
        specialize (Su (sorted_asc_tail _ _ A)).
        assert (B:=sorted_asc_lt_all_head _ _ A).
        apply lt_all_sorted_asc.
        -- apply Su.
        -- apply (lt_in_all _ _ _ (tl u)); auto.
      * intros A.
        specialize (Sv (sorted_asc_tail _ _ A)).
        assert (B:=sorted_asc_lt_all_head _ _ A).
        apply lt_all_sorted_asc.
        -- apply Sv.
        -- apply (lt_in_all _ _ _ (tl v)); auto.
      * simpl.
        destruct H0 as [L A].
        specialize (W A).
        assert (B:= inv_weak_majorized_raw_vsum _ _ _ W).
        assert (D: vsum (tl u) >= vsum (tl v)) by lra.
        apply Rge_left.
        rewrite <- Rplus_minus_assoc.
        rewrite <- V.
        rewrite Rplus_minus_assoc.
        apply Rge_left.
        rewrite (eta u), (eta v) in L.
        simpl in L. lra.
      * simpl. apply W.
        destruct H0. apply H1.
      * rewrite (eta u), (eta v). simpl. lra.
      * simpl. lra.
Qed.

Lemma Forall_P_In: forall n (P: R -> Prop) x (u: Vector.t R n),
  Forall P u -> In x u -> P x
.
Proof.
  induction n; intros P x u Fu Ix.
  - rewrite (nil_spec) in Ix. inv Ix.
  - rewrite (eta u) in Fu, Ix.
    inv Fu. app_inj_nat H1.
    inv Ix; app_inj_nat H4.
    + apply H2.
    + apply (IHn _ _ (tl u)); auto.
Qed.

Lemma Forall_P_Forall_In: forall n m (P: R -> Prop) (u: Vector.t R n) (v: Vector.t R m),
  Forall P u ->
  Forall (fun a => In a u) v ->
  Forall P v
.
Proof.
  intros n m. revert n.
  induction m; intros n P u v Pu Iv.
  - rewrite (nil_spec). constructor.
  - rewrite (eta v).
    inv Iv. app_inj_nat H0.
    constructor; auto.
    + apply (Forall_P_In _ _ _ u); auto.
    + apply (IHm n _ u); auto.
Qed.

Theorem inv_Karamata_Ksum : forall n P f (u v: Vector.t R n),
  convex_set P ->
  cond_convex P f ->
  Forall P u ->
  Forall P v ->
  inv_majorized u v ->
  0 <= Ksum f u v
.
Proof.
  intros n P f u v Hp Hconv Pu Pv Hmajo.
  destruct (exist_Ksum_prime n f u v) as [m [u' [v' [Neq [Iu [Iv [Su [Sv [Raw [Vs Ks]]]]]]]]]].
  rewrite Ks.
  destruct m.
  -- rewrite (nil_spec u'), (nil_spec v').
     simpl. lra.
  -- rewrite (Ksum_to_KPSsum_deltaS _ f u' v').
     rewrite <- Vs.
     assert (vsum u = vsum v) by (destruct Hmajo; auto).
     rewrite H.
     rewrite Rminus_diag.
     rewrite Rmult_0_r.
     rewrite Rplus_0_l.
     destruct Hmajo as [[U [V Hmajo]] _].
     apply (inv_Karamata_neq _ P); auto.
     + apply (Forall_P_Forall_In _ _ _ u); auto.
     + apply (Forall_P_Forall_In _ _ _ v); auto.
     + split; auto.
Qed.

Lemma Ksum_to_vsum : forall n f (u v: Vector.t R n),
  Ksum f u v = vsum (map f u) - vsum (map f v)
.
Proof.
  induction n; intros f u v.
  - rewrite (nil_spec u), (nil_spec v). simpl. lra.
  - rewrite (eta u), (eta v). simpl.
    rewrite IHn.
    lra.
Qed.

Theorem inv_Karamata : forall n P f (u v: Vector.t R n),
  convex_set P ->
  cond_convex P f ->
  Forall P u ->
  Forall P v ->
  inv_majorized u v ->
  vsum (map f u) >= vsum (map f v)
.
Proof.
  intros n P f u v Hp Hconv Pu Pv Hmajo.
  apply Rminus_ge.
  apply Rle_ge.
  rewrite <- Ksum_to_vsum.
  apply (inv_Karamata_Ksum n P); auto.
Qed.

Definition gt_all {n: nat} x (u: Vector.t R n):=
  Forall (fun a => a <= x) u
.

Lemma sorted_desc_shiftin_hd: forall n x u,
  sorted_desc (S (S n)) (shiftin x u) -> x <= (hd u)
.
Proof.
  induction n; intros x u A.
  - rewrite (eta u) in A.
    rewrite (nil_spec (tl _)) in A.
    inv A. app_inj_nat H3.
    lra.
  - rewrite (eta u) in A.
    simpl in A.
    assert (B:= sorted_desc_tail _ _ _ A).
    rewrite (eta (tl u)) in A.
    simpl in A.
    inv A. app_inj_nat H3.
    cut (x <= hd (tl u)); [lra|].
    apply IHn.
    apply B.
Qed.

Lemma gt_all_shiftin : forall n x u,
  sorted_desc (S n) (shiftin x u) -> lt_all x u
.
Proof.
  induction n; intros x u A.
  - rewrite (nil_spec _). constructor.
  - rewrite (eta u). constructor.
    ++ apply sorted_desc_shiftin_hd. auto.
    ++ apply IHn.
       apply (sorted_desc_tail _ (hd u)).
       rewrite (eta u) in A.
       apply A.
Qed.

Lemma sorted_desc_shift_tl: forall n x (u: Vector.t R n),
  sorted_desc _ (shiftin x u) -> sorted_desc n u
.
Proof.
  induction n; intros x u A.
  - rewrite (nil_spec). constructor.
  - rewrite (eta u) in A.
    simpl in A.
    assert (B:= sorted_desc_tail _ _ _ A).
    specialize (IHn _ _ B).
    destruct n.
    ++ rewrite (eta u). rewrite (nil_spec (tl _)). constructor.
    ++ rewrite (eta u).
       rewrite (eta (tl u)).
       constructor.
       -- rewrite (eta (tl u)) in A.
          simpl in A.
          inv A. app_inj_nat H3.
          apply H2.
       -- rewrite (eta (tl u)) in IHn. apply IHn.
Qed.

Lemma sorted_asc_if_sorted_desc : forall n (u: Vector.t R n),
  sorted_desc n (rev u) -> sorted_asc n u
.
Proof.
  induction n; intros u A.
  - rewrite (nil_spec). constructor.
  - rewrite (eta u) in A.
    rewrite rev_cons in A.
    assert (B:= gt_all_shiftin _ _ _ A).
    rewrite (eta u).
    apply lt_all_sorted_asc.
    ++ apply IHn. apply (sorted_desc_shift_tl _ _ _ A).
    ++ apply Forall_rev. apply B.
Qed.

Lemma majo_inv_majo : forall n (u v: Vector.t R n),
  majorized (rev u) (rev v) -> inv_majorized u v
.
Proof.
  intros n u v [Su [Sv [L D]]].
  rewrite 2 vsum_rev in D.
  apply sorted_asc_if_sorted_desc in Su, Sv.
  apply majorized_raw_if_inv_majorized_raw in L.
  split; auto.
  split; auto.
Qed.


Theorem Karamata_inequality: forall n P f (u v: Vector.t R n),
  convex_set P ->
  cond_convex P f ->
  Forall P u ->
  Forall P v ->
  majorized u v ->
  vsum (map f u) >= vsum (map f v)
.
Proof.
  intros n P f u v Hp Hconv Pu Pv Hmajo.
  rewrite <- 2 (vsum_rev _ (map _ _)).
  rewrite <- 2 map_rev.
  rewrite <- (rev_rev _ _ u), <- (rev_rev _ _ v) in Hmajo.
  apply majo_inv_majo in Hmajo.
  apply (inv_Karamata _ P); auto;
  apply Forall_rev; auto.
Qed.

Lemma vsum_const_mult: forall n x u,
  u = const x n ->
  vsum u = INR n * x
.
Proof.
  induction n; intros x u C.
  - rewrite (nil_spec u). simpl. lra.
  - specialize (IHn _ _ (f_equal tl C)).
    apply (f_equal hd) in C.
    rewrite (eta u). simpl vsum.
    rewrite IHn.
    rewrite C. rewrite S_INR.
    simpl. lra.
Qed.

Lemma vsum_const : forall n x y u v,
  u = const x (S n) ->
  v = const y (S n) ->
  vsum u = vsum v ->
  x = y
.
Proof.
  intros n x y u v U V Suv.
  apply vsum_const_mult in U, V.
  rewrite U, V in Suv.
  assert (INR (S n) <> 0).
  { apply not_0_INR. lia. }
  apply (Rmult_eq_reg_l) in Suv; auto.
Qed.

Theorem KPSsum_deltaS_0 : forall n P f (u v: Vector.t R (S n)),
  convex_set P ->
  cond_strict_convex P f ->
  Forall P u ->
  Forall P v ->
  all_neq u v ->
  inv_weak_majorized u v ->
  KPSsum_deltaS f u v = 0 ->
  exists x y, u = const x _ /\ v = const y _
.
Proof.
  induction n; intros P f u v Hp Hconv Pu Pv [Huv Hneq] [Hu [Hv [V Hmajo]]] K.
  - exists (hd u), (hd v). rewrite (eta u), (eta v).
    simpl. rewrite 2 (nil_spec (tl _)). split; trivial.
  - simpl in K.
    assert (Mm: inv_weak_majorized (tl u) (tl v)).
    { split.
      -- apply sorted_asc_tail. apply Hu.
      -- split.
      + apply sorted_asc_tail. apply Hv.
      + apply Hmajo. }
    assert (Phu: P (hd u)).
    { inv Pu. app_inj_nat H0. auto. }
    assert (Ptu: Forall P (tl u)).
    { inv Pu. app_inj_nat H0. auto. }
    assert (Phtu: P (hd (tl u))).
    { inv Ptu. app_inj_nat H0. rewrite <- H0. auto. }
    assert (Phv: P (hd v)).
    { inv Pv. app_inj_nat H0. auto. }
    assert (Ptv: Forall P (tl v)).
    { inv Pv. app_inj_nat H0. auto. }
    assert (Phtv: P (hd (tl v))).
    { inv Ptv. app_inj_nat H0. rewrite <- H0. auto. }
    assert (A: 0 <= KPSsum_deltaS f (tl u) (tl v)).
    { apply (inv_Karamata_neq _ P); auto.
      apply cond_strict_convex_convex, Hconv. }
    apply inv_weak_majorized_raw_vsum in Hmajo.
    rewrite (eta u) in Hu.
    rewrite (eta (tl u)) in Hu.
    inv Hu. app_inj_nat H3.
    rewrite (eta v) in Hv.
    rewrite (eta (tl v)) in Hv.
    inv Hv. app_inj_nat H5.
    assert (E1: 0 <= vsum (tl u) - vsum (tl v)) by lra.
    destruct H2, H3;
 [
      assert (F: secant_slope f (hd u) (hd v) < secant_slope f (hd (tl u)) (hd (tl v)))
      by (destruct Hneq; apply (strict_convex_secant_mono P); auto) |
      assert (F: secant_slope f (hd u) (hd v) < secant_slope f (hd (tl u)) (hd (tl v)))
      by (destruct Hneq; rewrite H0; apply (strict_convex_secant_mono_r P); auto; rewrite <- H0; auto) |
      assert (F: secant_slope f (hd u) (hd v) < secant_slope f (hd (tl u)) (hd (tl v)))
      by (destruct Hneq; rewrite H; apply (strict_convex_secant_mono_l P); auto; rewrite <- H; auto) |
      ].
    1,2,3:
    assert (E22: 0 < secant_slope f (hd (tl u)) (hd (tl v)) -
    secant_slope f (hd u) (hd v)) by lra;
    assert (E2: 0 <= secant_slope f (hd (tl u)) (hd (tl v)) -
    secant_slope f (hd u) (hd v)) by lra;
    assert (E:= Rmult_le_pos _ _ E2 E1);
    destruct (Rplus_eq_0 _ _ E A (K)) as [V2 K2];
    specialize (IHn _ _ _ _ Hp Hconv Ptu Ptv Hneq Mm (K2));
    destruct IHn as [x [y [Cu Cv]]];
    destruct (Rmult_integral _ _ V2); [lra|];
    assert (G: vsum (tl u) = vsum (tl v)) by lra;
    apply (vsum_const _ _ _ _ _ Cu Cv) in G;
    rewrite G in Cu; apply (f_equal hd) in Cu, Cv;
    rewrite (eta u) in Cu; rewrite (eta v) in Cv;
    simpl in Cu, Cv; destruct Hneq; lra.

    rewrite H, H0 in K.
    rewrite Rminus_diag in K.
    rewrite Rmult_0_l in K.
    rewrite Rplus_0_l in K.
    specialize (IHn P _ _ _ Hp Hconv Ptu Ptv Hneq Mm (K)).
    destruct (IHn) as [x [y [Cu Cv]]].
    exists x, y.
    
    assert (Cuh:= f_equal hd Cu).
    assert (Cvh:= f_equal hd Cv).
    rewrite <- H in Cuh.
    rewrite <- H0 in Cvh.
    simpl in Cuh, Cvh.
    rewrite (eta u), (eta v).
    rewrite Cu, Cv,Cuh, Cvh.
    auto.
Qed.

Theorem Karamata_inv_Ksum_0: forall n P f u v,
  convex_set P ->
  cond_strict_convex P f ->
  Forall P u ->
  Forall P v ->
  @inv_majorized n u v ->
  Ksum f u v = 0 ->
  u = v
.
Proof.
  induction n; intros P f u v Hp Hconv Pu Pv [[Su [Sv Hmajo]] V] HKsum.
  - rewrite nil_spec. apply nil_spec.
  - destruct (Req_dec (hd u) (hd v)).
    + rewrite (eta u), (eta v). rewrite H. f_equal.
      apply (IHn P f); auto.
      ++ inv Pu. app_inj_nat H1. auto.
      ++ inv Pv. app_inj_nat H1. auto.
      ++ split.
        ** split. * apply sorted_asc_tail. auto.
           * split. -- apply sorted_asc_tail. auto.
           -- destruct Hmajo. auto.
        ** rewrite (eta u), (eta v) in V.
           rewrite H in V.
           simpl in V. lra.
      ++ simpl in HKsum. rewrite H in HKsum. lra.
    +
    destruct (exist_Ksum_prime _ f (tl u) (tl v)) as [m [u' [v' [N [Iu [Iv [Su' [Sv' [W [Vn HH]]]]]]]]]].
    destruct m.
    { rewrite (nil_spec u'), (nil_spec v') in Vn. simpl in Vn.
      assert (A: vsum (tl u) = vsum (tl v)) by lra.
      rewrite (eta u), (eta v) in V.
      simpl in V. rewrite A in V.
      lra. }

    assert (Pu': Forall P u').
    { apply (Forall_P_Forall_In _ _ P (tl u)); auto.
      inv Pu. app_inj_nat H1. auto. }
    assert (Pv': Forall P v').
    { apply (Forall_P_Forall_In _ _ P (tl v)); auto.
      inv Pv. app_inj_nat H1. auto. }
    assert (Phu: P (hd u)).
    { inv Pu. app_inj_nat H1. auto. }
    assert (Phv: P (hd v)).
    { inv Pv. app_inj_nat H1. auto. }
    specialize (Su' (sorted_asc_tail _ _ Su)).
    specialize (Sv' (sorted_asc_tail _ _ Sv)).
    specialize (W (proj2 Hmajo)).
    assert (HHKsum: Ksum f (hd u :: u') (hd v :: v') = 0).
    { simpl. simpl in HH. rewrite <- HH. simpl in HKsum. rewrite HKsum. trivial. }
    rewrite (Ksum_to_KPSsum_deltaS) in HHKsum.
    assert (A: 0 <= KPSsum_deltaS f u' v').
    { apply (inv_Karamata_neq _ P); auto.
      apply cond_strict_convex_convex, Hconv. split; auto. }
    simpl hd in HHKsum.
    simpl vsum in HHKsum.
    replace (hd u + vsum u' - (hd v + vsum v')) with (hd u + vsum (tl u) - (hd v + vsum (tl v))) in HHKsum by lra.
    rewrite (eta u), (eta v) in V.
    simpl in V. rewrite V in HHKsum.
    rewrite Rminus_diag in HHKsum.
    rewrite Rmult_0_r in HHKsum.
    rewrite Rplus_0_l in HHKsum.
    assert (Vv': vsum (hd u :: u') = vsum (hd v :: v')) by (simpl; lra).
    destruct (KPSsum_deltaS_0 _ P f (hd u :: u') (hd v :: v')) as [x [y [Hl Hr]]]; auto.
    ++ constructor; auto.
    ++ constructor; auto.
    ++ constructor; auto.
    ++ assert (LTu:= sorted_asc_lt_all_head _ _ Su).
       assert (LTv:= sorted_asc_lt_all_head _ _ Sv).
       split.
       +++ apply lt_all_sorted_asc; auto.
           apply (lt_in_all _ _ _ _ _ Iu LTu).
       +++ split; auto.
       --- apply lt_all_sorted_asc; auto.
           apply (lt_in_all _ _ _ _ _ Iv LTv).
       --- split; auto.
           simpl. lra.
    ++ assert (C:= vsum_const _ _ _ _ _ Hl Hr Vv').
    rewrite C in Hl.
    assert (Hlh := f_equal hd Hl).
    assert (Hrh := f_equal hd Hr).
    simpl in Hlh, Hrh.
    lra.
Qed.

Definition strict_convex (f : R -> R) : Prop :=
  forall x y t,
    0 < t < 1 ->
    f (t * x + (1 - t) * y) < t * f x + (1 - t) * f y.

Definition convex (f : R -> R) : Prop :=
  forall x y t,
    0 <= t <= 1 ->
    f (t * x + (1 - t) * y) <= t * f x + (1 - t) * f y.

Theorem Karamata_inequality_original: forall n f (u v: Vector.t R n),
  convex f ->
  majorized u v ->
  vsum (map f u) >= vsum (map f v)
.
Proof.
  intros n f u v Hconv Hmajo.
  assert (A: forall m (a: Vector.t R m), Forall (fun _ => True) a).
  { induction m; intros.
    -- rewrite (nil_spec a). constructor.
    -- rewrite (eta a). constructor; auto. }
  apply (Karamata_inequality n (fun x => True)); auto.
  - unfold convex_set. auto.
  - unfold cond_convex. intros. apply Hconv; auto.
Qed.


Fact gadget_strict_convex: convex_set (fun x => 0 <= x <= 1) /\ cond_strict_convex (fun x => 0 <= x <= 1) (fun x => 1 / (1 + x)).
Proof.
  split.
  - intros x y [Al Ar] [Bl Br] t [Tl Tr].
    split.
    + apply Rplus_le_le_0_compat;
      apply Rmult_le_pos; auto.
      lra.
    + assert (AR: 0 <= 1 - x) by lra.
      assert (BR: 0 <= 1 - y) by lra.
      assert (TR: 0 <= 1 - t) by lra.
      apply Rge_le.
      apply (Rminus_ge 1 (t * x + (1-t)*y)).
      apply Rle_ge.
      assert (AT:= Rmult_le_pos _ _ Tl AR).
      assert (BT:= Rmult_le_pos _ _ TR BR).
      lra.
  - intros _ x y [Hx0 Hx1] [Hy0 Hy1] Nxy t [Ht0 Ht1].
  assert (Hdenm : 0 < 1 + (t * x + (1 - t) * y)) by nra.
  assert (Hdenx : 0 < 1 + x) by nra.
  assert (Hdeny : 0 < 1 + y) by nra.
  assert (Hmul : 0 < (1 + (t * x + (1 - t) * y)) * (1 + x) * (1 + y)).
  {
  apply Rmult_lt_0_compat.
  - apply Rmult_lt_0_compat; assumption.
  - exact Hdeny.
  }
  unfold Rdiv.
  apply (Rmult_lt_reg_r
           ((1 + (t * x + (1 - t) * y)) * (1 + x) * (1 + y)));
    [exact Hmul |].

  rewrite Rmult_assoc.
  replace
    (/ (1 + (t * x + (1 - t) * y)) *
     ((1 + (t * x + (1 - t) * y)) * (1 + x) * (1 + y)))
    with ((1 + x) * (1 + y))
    by (field; nra).
  rewrite ! Rmult_1_l.
  replace
    ((t * / (1 + x) + (1 - t) * / (1 + y)) *
     ((1 + (t * x + (1 - t) * y)) * (1 + x) * (1 + y)))
    with
    (t * (1 + (t * x + (1 - t) * y)) * (1 + y) +
     (1 - t) * (1 + (t * x + (1 - t) * y)) * (1 + x))
    by (field; nra).
  assert
  (D: t * (1 + (t * x + (1 - t) * y)) * (1 + y) +
   (1 - t) * (1 + (t * x + (1 - t) * y)) * (1 + x)
   = t * (1 - t) * (x - y) * (x - y) + (1 + x) * (1 + y)) by nra.
   rewrite D.
   apply (Rplus_lt_reg_r (- ((1+x) * (1+y)))).
   rewrite (Rplus_assoc).
   rewrite Rplus_opp_r.
   rewrite Rplus_0_r.
   clear Hmul.
   rewrite (Rmult_assoc).
   apply Rmult_lt_0_compat; nra.
Qed.
