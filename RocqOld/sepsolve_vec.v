Require Import Reals Lra Coq.Logic.Eqdep_dec.

Import Reals.

Open Scope R_scope.

Declare Scope vec_scope.
Delimit Scope vec_scope with Vec.
Open Scope vec_scope.

Require Import Vector.
Import VectorNotations VectorDef.

Theorem eta0 {A}: forall x: t A O, x = [].
Proof. apply case0. auto. Qed.


Ltac inv_cleanup :=
  repeat match goal with
  | H : existT _ _ _ = existT _ _ _ |- _ =>
      apply (inj_pair2_eq_dec _ Nat.eq_dec) in H; subst; clear H
  end.

Ltac inv_many Hs :=
  lazymatch Hs with
  | (?H, ?Hs') =>
      inversion H; subst; clear H;
      inv_cleanup;
      inv_many Hs'
  | ?H =>
      inversion H; subst; clear H;
      inv_cleanup
  end.

Tactic Notation "inv" constr(Hs) :=
  inv_many Hs.

Lemma hd_app: forall {T n k}
  (A: t T (S n))
  (B: t T k),
  hd (A ++ B) = hd A.
Proof. intros. rewrite (eta A). trivial. Qed.

Lemma tl_app: forall {T n k}
  (A: t T (S n))
  (B: t T k),
  tl (A ++ B) = tl A ++ B.
Proof. intros. rewrite (eta A). simpl. trivial. Qed.

Global Hint Resolve hd_app : vec_scope.
Global Hint Resolve tl_app : vec_scope.

Require Import Lia.

Notation vec := (t R).

(* SPECIAL VEC definitions *)

Fixpoint zerosV {n: nat}: vec n.
destruct n.
  + exact [].
  + apply cons.
    - apply 0%R.
    - apply zerosV.
Defined.

Fixpoint onesV {n: nat}: vec n.
destruct n.
  + exact [].
  + apply cons.
    - apply 1%R.
    - apply onesV.
Defined.

Fixpoint canon_e {n: nat} (m: nat) : vec n :=
  match n with
    | O => []
    | S ns => match m with
                | O => 1 :: @zerosV ns
                | S ms => 0 :: canon_e ms
  end end.

Notation "0" := (zerosV) : vec_scope.
Notation "1" := (onesV) : vec_scope.

(* SPECIAL VEC proofs *)

Lemma canon_e_geq: forall (n x: nat),
  (n <= x)%nat -> @canon_e n x = 0.
Proof.
  induction n; auto.
  intros. simpl.
  destruct x. * inversion H.
  * f_equal. apply IHn. lia.
Qed.

Theorem vec_eq_dec: forall {n} (x y: vec n),
  x = y \/ x <> y.
Proof.
  induction n.
    - intros. rewrite (eta0 x), (eta0 y). auto.
    - intros.
      destruct (IHn (tl x) (tl y)).
      + destruct (Req_dec (hd x) (hd y)).
        * left. rewrite (eta x), (eta y), H, H0. trivial.
        * right. congruence.
      + right. congruence.
Qed.

(* VEC PROP definitions *)

Fixpoint mapvec {n: nat} (f: R -> R) (a: vec n): vec n.
destruct a.
  - apply [].
  - apply cons.
    + apply (f h).
    + apply (mapvec n f a).
Defined.

Definition negvec {n} := @mapvec n (fun x: R => (-x)%R).
Definition multvec {n} (c: R) := @mapvec n (fun x => (c*x)%R).

Notation "- x" := (negvec x) : vec_scope.
Infix "*" := (multvec) : vec_scope.

Fixpoint zipvecs {n: nat} (f: R -> R -> R) (a b: vec n): vec n.
destruct a.
  - apply [].
  - inversion b; subst.
     apply cons.
      + apply f. * apply h. * apply h0.
      + apply zipvecs. * apply f. * apply a. * apply H0.
Defined.

Definition plusvecs {n} := @zipvecs n (fun x y => (x + y)%R).
Definition subvecs {n} := @zipvecs n (fun x y => (x - y)%R).

Infix "+" := (plusvecs) : vec_scope.
Infix "-" := (subvecs) : vec_scope.


(* VEC PROP proof *)

Lemma vec_mult_0: forall {n} (x: vec n),
  0 * x = 0.
Proof.
  induction x; auto.
  cbn. f_equal. { lra. }
  apply IHx.
Qed.

Lemma vec_mult_neg1: forall {n} (x: vec n),
  -1 * x = -x.
Proof.
  induction x; auto.
  cbn. f_equal. { lra. } apply IHx.
Qed.

Global Hint Resolve vec_mult_0 : vec_scope.
Global Hint Resolve vec_mult_neg1 : vec_scope.

Lemma vec_plus_step: forall {n} (x y: vec (S n)),
  x + y = (hd x + hd y)%R :: tl x + tl y.
Proof. intros. rewrite (eta x), (eta y). trivial. Qed.

Lemma vec_plus_app_dist: forall {n} (a b: R) (x y: vec n),
  (a + b)%R :: x + y = (a :: x) + (b :: y).
Proof.
  induction n.
    - intros. rewrite (eta0 x), (eta0 y). rewrite (eta0 _). trivial.
    - intros. rewrite 2 vec_plus_step.
      f_equal. rewrite IHn. simpl tl.
      rewrite <-2 eta. trivial.
Qed.

Lemma vec_plus_sub: forall {n} (x y: vec n),
  x + (-y) = x - y.
Proof.
  induction x; auto.
  intros. rewrite (eta y).
  cbn. f_equal. apply IHx.
Qed.

Lemma vec_neg_0: forall {n: nat}, -0 = (0: vec n).
Proof.
  induction n; auto.
  cbn. f_equal. { lra. } apply IHn.
Qed.

Lemma vec_plus_assoc:
  forall {n: nat}, forall (u v w: vec n),
  u + v + w = u + (v + w).
Proof.
  induction u; auto.
  intros. rewrite (eta v), (eta w).
  cbn. f_equal. { lra. } apply IHu.
Qed.

Lemma vec_plus_comm:
  forall {n: nat}, forall (u v: vec n),
  u + v = v + u.
Proof.
  induction u; intros. { rewrite (@eta0 R). auto. }
  rewrite (eta v).
  cbn. f_equal. { lra. } apply IHu.
Qed.

Lemma vec_plus_0: forall {n} (x: vec n),
  x + 0 = x.
Proof.
  induction x; auto.
  cbn. f_equal. { lra. } apply IHx.
Qed.

Lemma vec_sub_sub: forall {n} (x: vec n),
  x - x = 0.
Proof.
  induction n; intros; cbn.
    - auto using eta0.
    - rewrite (eta x).
      cbn. f_equal. { lra. } apply IHn.
Qed.

Global Hint Resolve vec_plus_assoc : vec_scope.
Global Hint Resolve vec_plus_comm : vec_scope.
Global Hint Resolve vec_plus_0 : vec_scope.
Global Hint Resolve vec_sub_sub : vec_scope.

Lemma vec_mult_dist: forall {n} (l r: R) (x: vec n),
  (l + r) * x = l * x + r * x.
Proof.
  induction x; auto.
  cbn. f_equal. { lra. }
  apply IHx.
Qed.

Lemma vec_neg_neg: forall {n} (x: vec n),
  - - x = x.
Proof.
  induction n; intros.
    - rewrite eta0. apply eta0.
    - rewrite (eta x).
      specialize (IHn (tl x)).
      unfold negvec in IHn.
      cbn. rewrite IHn. f_equal.
      lra.
Qed.

Lemma vec_0_neg: forall {n} (x: vec n),
  0 - x = -x.
Proof.
  induction x.
    - trivial.
    - cbn.
      unfold subvecs in IHx.
      rewrite IHx.
      f_equal. lra.
Qed.

Lemma vec_sub_neg: forall {n: nat}
  (x y: vec n),
  x - - y = x + y
.
Proof.
  induction n; intros.
    - rewrite eta0. apply eta0.
    - rewrite (eta x), (eta y).
      cbn.
      specialize (IHn (tl x) (tl y)).
      unfold subvecs, negvec in IHn.
      rewrite IHn.
      f_equal.
      lra.
Qed.


(* VEC ELEM prop *)

Lemma vec_hd_plus_dist: forall {n}
  (x y: vec (S n)),
  hd (x + y) = (hd x + hd y)%R.
Proof.
  intros. rewrite (eta x), (eta y).
  trivial.
Qed.

Lemma vec_tl_plus_dist: forall {n}
  (x y: vec (S n)),
  tl (x + y) = tl x + tl y.
Proof.
  intros. rewrite (eta x), (eta y).
  trivial.
Qed.

Lemma vec_mult_step: forall {n} (a: R) (x: vec (S n)),
  a * x = (a * hd x)%R :: a * tl x.
Proof. intros. rewrite (eta x). trivial. Qed.

Lemma vec_mult_dist_r: forall {n} (a: R) (x y: vec n),
  a * (x + y) = a * x + a * y.
Proof.
  induction n.
    - intros. rewrite (eta0 _), (eta0). trivial.
    - intros.
      rewrite 3 (vec_mult_step).
      rewrite vec_tl_plus_dist.
      rewrite vec_hd_plus_dist. 
      rewrite (IHn).
      rewrite Rmult_plus_distr_l.
      rewrite vec_plus_app_dist. trivial.
Qed.

Hint Resolve vec_mult_dist : vec_scope.


Definition sqvec {n: nat} := @mapvec n (fun x => x*x)%R.
Definition sqrtvec {n: nat} := @mapvec n (fun x => sqrt x)%R.

Lemma sqvec_step:
  forall {n} (v: vec (S n)),
  sqvec v = (hd v * hd v)%R::sqvec (tl v)
.
Proof. intros. rewrite (eta v). trivial. Qed. 

Lemma sqvec_dist:
  forall {n: nat} (c: R) (v: vec n),
  sqvec (c * v) = (c*c) * sqvec v
.
Proof.
  induction n; intros.
    - rewrite (eta0 (sqvec _)), eta0. trivial.
    - rewrite (eta v).
      rewrite 2sqvec_step.
      specialize (IHn c (tl v)).
      simpl.
      replace (mapvec _ (tl v)) with ((c*tl v)) by auto.
      rewrite IHn.
      rewrite vec_mult_step.
      simpl. f_equal. lra.
Qed.
    

(* DOT definition *)
Fixpoint dot {n} (a b: vec n): R.
destruct a.
  - apply 0%R.
  - inversion b as [|e l c]; subst.
    apply (fun x y => (x + y)%R).
    + apply (h * e)%R.
    + apply (dot n).
      * apply a.
      * apply c.
Defined.

(* DOT proofs *)

Lemma dot_step: forall {n} (a b: vec (S n)),
  dot a b = (hd a * hd b + dot (tl a) (tl b))%R.
Proof. intros. rewrite (eta a), (eta b) at 1. trivial. Qed.

Lemma dot_comm: forall {n} (u v: vec n),
  dot u v = dot v u.
Proof.
  induction v; auto.
    - rewrite (eta0 _). auto.
    - rewrite (eta u). cbn.
      f_equal. { lra. }
      apply IHv.
Qed.

Lemma dot_0: forall {n} (u: vec n),
  dot 0 u = 0%R.
Proof.
  induction u; auto.
  cbn. rewrite IHu. lra.
Qed.

Lemma dot_dist: forall {n} (u v z: vec n),
  dot u (v + z) = (dot u v + dot u z)%R.
Proof.
  induction u; intros; auto.
  + simpl. lra.
  + rewrite (eta v), (eta z).
  cbn. unfold plusvecs in IHu. rewrite IHu. lra.
Qed.

Lemma dot_dist_l: forall {n} (u v z: vec n),
  dot (u + v) z = (dot u z + dot v z)%R.
Proof.
  intros.
  rewrite dot_comm.
  rewrite dot_dist. rewrite 2 (dot_comm z). trivial.
Qed.

Lemma dot_split: forall {n m} (u v: vec n) (x y: vec m),
  dot (u ++ x) (v ++ y) = (dot u v + dot x y)%R.
Proof.
  induction n.
    - intros. rewrite (eta0 u), (eta0 v). simpl. lra.
    - intros. rewrite (eta u), (eta v).
      cbn. rewrite IHn. lra.
Qed.

Hint Resolve dot_0 : vec_scope.
Hint Resolve dot_comm : vec_scope.
Hint Resolve dot_dist : vec_scope.
Hint Resolve dot_split : vec_scope.

Lemma dot_geq0: forall {n} (u: vec n),
  0 <= dot u u.
Proof.
  induction u; auto.
    - simpl. lra.
    - cbn. assert (A:= pow2_ge_0 h).  lra.
Qed.

Lemma dot_eq0: forall {n} (u: vec n),
  dot u u = 0%R -> u = 0.
Proof.
  induction u; auto.
  cbn. intros.
  assert (A: 0 <= h * h). { assert (A:= pow2_ge_0 h). lra. }
  assert (B := dot_geq0 u).
  assert (C0 := Rplus_eq_0_l _ _ A B H).
  rewrite (Rplus_comm) in H.
  assert (C1 := Rplus_eq_0_l _ _ B A H).
  assert (A0: h = 0%R). { apply Rsqr_eq_0. auto using A. }
  f_equal; auto.
Qed.

Lemma dot_mult_dist_r: forall {n} (c:R) (u v: vec n),
  dot u (c * v) = (c * dot u v)%R.
Proof.
  induction n; intros.
    - rewrite (eta0 u). simpl. lra.
    - rewrite (eta v).
      rewrite 2dot_step.
      simpl.
      specialize (IHn c (tl u) (tl v)).
      unfold multvec in IHn.
      rewrite IHn.
      lra.
Qed.

Lemma sqvec_1: forall {n},
  sqvec (1: vec n) = 1.
Proof.
  induction n.
    - auto.
    - simpl.
      cbn. unfold sqvec in IHn.
      rewrite IHn.
      f_equal. lra.
Qed.

Lemma sqvec_neg: forall {n} (x: vec n),
  sqvec (-x) = sqvec x.
Proof.
  induction x.
    - constructor.
    - cbn. unfold negvec, sqvec in IHx.
      rewrite IHx.
      f_equal. lra.
Qed.


Definition is_binary {n: nat} (u: vec n) :=
  Forall (fun x: R => x = 0 \/ x = 1)%R u
.


Definition is_positive {n: nat} (u: vec n) :=
  Forall (fun x => 0 < x)%R u
.


Inductive is_vec_leq : forall {n: nat}, vec n -> vec n -> Prop :=
  | vclq_nil : is_vec_leq [] []
  | vclq_con : forall (n: nat) (a b: R) (x y: vec n),
    a <= b -> is_vec_leq x y -> is_vec_leq (a::x) (b::y)
.

Lemma pos_leq: forall (n: nat) (x: vec n),
  is_positive x -> is_vec_leq 0 x.
Proof.
  induction x.
    - constructor.
    - intros. inv H.
      constructor; auto. lra.
Qed.

Lemma dot_vec_noneg:
  forall (n: nat) (a x y: vec n),
  is_vec_leq 0 a ->
  is_vec_leq x y -> dot a x <= dot a y
.
Proof.
  induction n; intros.
    - rewrite (eta0 _). simpl. lra.
    - inv (H, H0).
      rewrite !dot_step. simpl.
      specialize (IHn _ _ _ H6 H4).
      apply (Rmult_le_compat_l _ _ _ H5) in H3.
      lra.
Qed.

Lemma dot_vec_noneg_0: forall (n: nat) (x y: vec n),
  is_vec_leq 0 x -> is_vec_leq 0 y ->
  0 <= dot x y.
Proof.
  induction n; intros.
    - rewrite (eta0 x). simpl. lra.
    - inv (H, H0).
      subst. rewrite dot_step. simpl.
      specialize (IHn _ _ H6 H7).
      assert (A:= Rmult_le_pos _ _ H5 H4).
      lra.
Qed.

Lemma sqrtvec_dist:
  forall (n: nat) (c: R) (v: vec n),
    (0 <= c) -> (is_vec_leq 0 v) ->
    sqrtvec (c * v) = (sqrt c) * sqrtvec v
.
Proof.
  induction n; intros.
    - rewrite (eta0). apply eta0.
    - rewrite (eta v). cbn.
      specialize (IHn c (tl v)).
      unfold sqrtvec in IHn.
      unfold multvec in IHn.
      rewrite (IHn H).
      f_equal.
      inv H0.
      --
      subst. simpl.
      apply (sqrt_mult _ _ H H5).
      -- inv H0.
         subst. auto.
Qed.

Lemma sq_sqrt_vec: forall (n: nat) (u: vec n),
  is_vec_leq 0 u ->
  sqvec (sqrtvec u) = u
.
Proof.
  induction n; intros.
    - rewrite eta0. apply eta0.
    - inv H.
      subst. cbn.
      specialize (IHn y H5).
      unfold sqvec, sqrtvec in IHn.
      rewrite IHn.
      f_equal. apply sqrt_def. apply H4.
Qed.

Lemma non_neg_dot_1:
  forall {n: nat} (u: vec n),
  is_vec_leq 0 u ->
  0%R <= dot u 1
.
Proof.
  induction u.
  - simpl. lra.
  - intros.
    inv H.
    rewrite dot_step. simpl.
    apply Rplus_le_le_0_compat.
    + lra.
    + apply (IHu H6).
Qed.

Lemma non_neg_dot_0:
  forall {n: nat} (u: vec n),
  is_vec_leq 0 u ->
  dot u 1 = 0%R ->
  u = 0
.
Proof.
  induction u.
  + trivial.
  + rewrite dot_step. simpl.
    intros L D.
    inv L.
    specialize (IHu H5).
    apply non_neg_dot_1 in H5.
    f_equal.
    -- lra.
    -- apply IHu. lra.
Qed.


Inductive perf_square_vec : forall {n}, vec n -> Prop :=
  | perf_square_nil : perf_square_vec []
  | perf_square_step: forall {n: nat} (x: nat) (u: vec n),
    perf_square_vec u -> perf_square_vec ((INR x * INR x)%R :: u)
.

Lemma perf_square_non_neg: forall {n} (u: vec n),
  perf_square_vec u -> is_vec_leq 0 u
.
Proof.
  induction u.
  - constructor.
  - intros A. simpl.
    inv A.
    constructor.
    -- apply Rle_0_sqr.
    -- apply (IHu H1).
Qed.

Lemma vec_sqrt_nonneg:
  forall m c (t: vec m), 0%R <= c -> is_vec_leq 0 t -> is_vec_leq 0 (c * sqrtvec t)
.
Proof.
  induction m; intros c t Hc Ht.
  - rewrite (eta0 t). simpl. constructor.
  - rewrite (eta t) in *.
    inv Ht.
    simpl.
    constructor.
    + apply Rmult_le_pos.
      * exact Hc.
      * apply sqrt_positivity. assumption.
    + apply IHm; assumption.
Qed.

Lemma vec_nonneg_mult_1:
  forall m c,
    0%R <= c -> is_vec_leq 0 (c * (1: vec m))
.
Proof.
  induction m; intros c Hc.
  - simpl. constructor.
  - simpl. constructor.
    + lra.
    + apply IHm. exact Hc.
Qed.

Lemma leq_refl:
  forall (n: nat) (x: vec n),
    is_vec_leq x x
.
Proof. induction x; constructor; [lra|assumption]. Qed.

Fact leq_0_1:
  forall (n: nat),
  @is_vec_leq n 0 1
.
Proof.
  induction n; [constructor|].
  rewrite (eta 0), (eta 1).
  constructor.
  + simpl. lra.
  + apply IHn.
Qed.


Lemma is_binary_nonneg :
  forall {n : nat} (a : vec n),
    is_binary a -> is_vec_leq 0 a.
Proof.
  induction n; intros a Hbin.
  - rewrite nil_spec. constructor.
  - rewrite (eta a) in *.
    inv Hbin.
    rewrite (eta 0).
    constructor.
    + simpl. destruct H2; subst; lra.
    + apply IHn. exact H3.
Qed.

Lemma binary_perf_square_dot_nat :
  forall m (u v : vec m),
    is_binary u -> perf_square_vec v -> exists q, dot u v = INR q.
Proof.
  induction m; intros u v Bi Pe.
  + exists O. rewrite (nil_spec u). trivial.
  + rewrite (eta u) in Bi. rewrite (eta v) in Pe.
    inv (Bi, Pe).
    destruct (IHm _ _ H3 H1).
    destruct H2.
    ++ exists (x0)%nat.
       rewrite dot_step.
       rewrite H, H2, <- H0. lra.
    ++ exists (x * x + x0)%nat.
       rewrite dot_step.
       rewrite H, H2, <- H0.
       rewrite <- mult_INR. rewrite plus_INR. lra.
Qed.

Lemma binary_perf_square_dot_zero_or_ge_1 :
  forall {m : nat} (u v : vec m),
    is_binary u -> perf_square_vec v ->
    dot u v = 0%R \/ 1 <= dot u v.
Proof.
  intros m u v Hu Hv.
  destruct (binary_perf_square_dot_nat m u v Hu Hv) as [q Hq].
  destruct q.
  - left. simpl in Hq. lra.
  - right. rewrite Hq. rewrite S_INR. pose proof (pos_INR q). lra.
Qed.

Lemma sqvec_hd:
  forall (n: nat) (a: vec (S n)),
    hd (sqvec a) = ((hd a) * (hd a))%R
.
Proof. intros. rewrite (eta a). trivial. Qed.

Lemma sqvec_tl:
  forall (n: nat) (a: vec (S n)),
    tl (sqvec a) = sqvec (tl a)
.
Proof. intros. rewrite (eta a). trivial. Qed.

Close Scope vec_scope.
Close Scope R_scope.
