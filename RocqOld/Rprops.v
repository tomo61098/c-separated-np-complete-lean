Require Import Reals Lra.
Import Reals.

Open Scope R_scope.

Declare Scope vec_scope.
Delimit Scope vec_scope with Vec.
Open Scope vec_scope.

Require Import Vector.
Import VectorNotations VectorDef.

Theorem eta0 {A}: forall x: t A O, x = [].
Proof. apply case0. auto. Qed.


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
  * f_equal. apply IHn. intuition.
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
  induction u; intros. { auto using (@eta0 R). }
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
  induction u; intuition.
  rewrite (eta v), (eta z).
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
    - intros. rewrite (eta0 u), (eta0 v). intuition.
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


(* MATRIX *)
Declare Scope mat_scope.
Delimit Scope mat_scope with Mat.
Open Scope mat_scope.

(* SPECIAL MAT defs *)

Notation matrix n m := (t (vec m) n).

Fixpoint zerosM {n m: nat}: matrix n m.
destruct n.
  + exact [].
  + apply cons.
    - apply (zerosV).
    - apply zerosM.
Defined.

Fixpoint onesM {n m: nat}: matrix n m.
destruct n.
  + exact [].
  + apply cons.
    - apply 1%Vec.
    - apply onesM.
Defined.

Fixpoint eyeM (x: nat) {n m: nat} := 
  match n with
    | O => []
    | S ns => @canon_e m x :: @eyeM (S x) ns m end.

Fixpoint col {n} (x: vec n) :=
  match x with
    | [] => []
    | u::us => [u] :: col us end.

Fixpoint emptyM {n} : matrix n O :=
  match n with
    | O => []
    | S m => [] :: @emptyM m end.

Notation "0" := (zerosM) : mat_scope.
Notation "1" := (onesM) : mat_scope.
Local Notation I := (eyeM 0).

(* SPECIAL MAT proofs *)

Lemma eye_0: forall {n m x: nat}, (m <= x)%nat -> @eyeM x n m = 0.
Proof.
  induction n; auto.
   intros. simpl.
   f_equal. { apply (canon_e_geq _ _ H). }
   apply IHn. lia.
Qed.

Require Import Logic.Eqdep_dec.

Theorem mat_eq_dec: forall {n m} (A B: matrix n m),
  A = B \/ A <> B.
Proof.
  induction n.
    - intros. rewrite (eta0 A), (eta0 B). auto.
    - intros. rewrite (eta A), (eta B).
      destruct (vec_eq_dec (hd A) (hd B)).
      + destruct (IHn m (tl A) (tl B)).
        * left. rewrite H, H0. auto.
        * right. intros D. inversion D; subst.
          apply inj_pair2_eq_dec in H3; auto using eq_nat_dec.
      + right. congruence.
Qed.

(* MAT PROPS definition *)

Fixpoint mapmat {n m: nat} (f: vec m -> vec m) (M: matrix n m): matrix n m.
destruct M.
  - apply [].
  - apply cons.
    + apply (f h).
    + apply (mapmat n m f M).
Defined.

Definition negmat {n m} := @mapmat n m (fun x: vec m => (-x)%Vec).
Definition multmat {n m} (c: R) := @mapmat n m (fun x: vec m => (c*x)%Vec).

Fixpoint multmatvec {n m} (M: matrix n m) (v: vec m) :=
  match M with
    | [] => []
    | u::Ms => dot u v :: multmatvec Ms v end.

Notation "- x" := (negmat x) : mat_scope.
Infix "*" := (multmat) : mat_scope.
Infix "@" := (multmatvec) (at level 40, left associativity) : mat_scope.

Fixpoint zipmat {n m: nat} (f: vec m -> vec m -> vec m) (a b: matrix n m): matrix n m.
destruct a.
  - apply [].
  - inversion b; subst.
     apply cons.
      + apply f. * apply h. * apply h0.
      + apply zipmat. * apply f. * apply a. * apply H0.
Defined.

Definition plusmat {n m} := @zipmat n m (fun x y => (x + y)%Vec).
Definition submat {n m} := @zipmat n m (fun x y => (x - y)%Vec).

Infix "+" := (plusmat) : mat_scope.
Infix "-" := (submat) : mat_scope.

(* MAT PROPS proofs *)

Lemma mat_mult_0: forall {n m} (x: matrix n m),
  0 * x = 0.
Proof.
  induction x; auto.
  cbn. f_equal. { intuition. }
  apply IHx.
Qed.

Lemma mat_mult_neg1: forall {n m} (x: matrix n m),
  -1 * x = -x.
Proof.
  induction x; auto.
  cbn. f_equal. { intuition. } apply IHx.
Qed.

Lemma mat_mult_zeros: forall {n m} (M: matrix n m),
  M @ 0%Vec = 0%Vec.
Proof.
  induction M; auto.
  simpl. rewrite dot_comm, dot_0.
  f_equal. auto.
Qed.

Lemma mat_vec_dist: forall {n m} (M: matrix n m) (u v: vec m),
  M @ (u + v)%Vec = (M @ u + M @ v)%Vec.
Proof.
  induction M; auto.
  intros. destruct m; auto.
    - cbn. rewrite (eta0 h), (eta0 u), (eta0 v).
      f_equal. { intuition. }
      cbn. specialize (IHM [] []).
           intuition.
    - cbn. f_equal. { intuition. }
      rewrite IHM. trivial.
Qed.

Hint Resolve mat_mult_zeros : mat_scope.

Lemma eye_mult_vec: forall {k x m n} (u: vec m) (v: vec n),
  (m <= x)%nat -> @eyeM x k _ @ (u ++ v) = eyeM (x - m) @ v.
Proof.
  induction k; auto.
  intros.
  simpl. f_equal. { revert x m n u v H.
  induction x. * intros. assert (m = O) by lia. destruct u; auto. lia.
  * intros. destruct u; auto.
    cbn. rewrite Rmult_0_l. rewrite Rplus_0_l.
    apply IHx. lia. }
  replace (S (x - m)) with ((S x) - m)%nat by lia.
  apply IHk. lia.
Qed.

Lemma vec_mult_I: forall {n} (x: vec n),
  I @ x = x.
Proof.
  induction x; auto.
  cbn. rewrite dot_0. f_equal. { lra. }
  replace (h :: x) with ([h] ++ x) by auto.
  rewrite (eye_mult_vec [h]) by lia.
  auto.
Qed.

Lemma vec_mult_M0: forall {n m} (x: vec n),
  0 @ x = (0: vec m)%Vec.
Proof.
  intros n m. revert n.
  induction m; auto.
  intros. simpl. f_equal. { intuition. }
  auto.
Qed.

Global Hint Resolve mat_mult_0 : mat_scope.
Global Hint Resolve mat_mult_neg1 : mat_scope.
Global Hint Resolve vec_mult_M0 : mat_scope.
Global Hint Resolve vec_mult_I : mat_scope.

Lemma mat_plus_sub: forall {n m} (x y: matrix n m),
  x + (-y) = x - y.
Proof.
  induction x; auto.
  intros. rewrite (eta y).
  cbn. f_equal. { auto using vec_plus_sub. } apply IHx.
Qed.

Lemma mat_neg_0: forall {n m: nat}, -0 = (0: matrix n m).
Proof.
  induction n; auto.
  cbn. intros. f_equal. { auto using vec_neg_0. } apply IHn.
Qed.

Lemma mat_plus_assoc:
  forall {n m: nat}, forall (u v w: matrix n m),
  u + v + w = u + (v + w).
Proof.
  induction u; auto.
  intros. rewrite (eta v), (eta w).
  cbn. f_equal. { auto using vec_plus_assoc. } apply IHu.
Qed.

Lemma mat_plus_comm:
  forall {n m: nat}, forall (u v: matrix n m),
  u + v = v + u.
Proof.
  induction u; intros. {
  rewrite eta0. auto. }
  rewrite (eta v).
  cbn. f_equal. { auto using vec_plus_comm. } apply IHu.
Qed.

Lemma mat_plus_0: forall {n m} (x: matrix n m),
  x + 0 = x.
Proof.
  induction x; auto.
  cbn. f_equal. { auto using vec_plus_0. } apply IHx.
Qed.

Lemma mat_sub_sub: forall {n m} (x: matrix n m),
  x - x = 0.
Proof.
  induction n; intros; cbn.
    - rewrite (eta0 x). cbn. trivial.
    - rewrite (eta x).
      cbn. f_equal. { auto using vec_sub_sub. } apply IHn.
Qed.

Lemma mat_mat_dist: forall {n m} (N M: matrix n m) (u: vec m),
  (N + M) @ u = (N @ u + M @ u)%Vec.
Proof.
  induction N; auto.
  intros. rewrite (eta M).
  simpl. unfold plusmat in IHN. rewrite IHN.
  rewrite dot_dist_l.
  auto.
Qed.

Global Hint Resolve mat_plus_assoc : mat_scope.
Global Hint Resolve mat_plus_comm : mat_scope.
Global Hint Resolve mat_plus_0 : mat_scope.
Global Hint Resolve mat_sub_sub : mat_scope.


(* MAT COL append *)

Fixpoint hc {n m} (M: matrix n (S m)): vec n.
destruct M.
  - apply [].
  - apply cons. 
    + apply (hd h).
    + eapply hc.
      apply M.
Defined.

Fixpoint tc {n m} (M: matrix n (S m)): matrix n m.
destruct M.
  - apply [].
  - apply cons. 
    + apply (tl h).
    + eapply tc.
      apply M.
Defined.

Fixpoint cc {n m k} (M: matrix n m) (N: matrix n k) : matrix n (m + k).
  destruct n.
    - apply [].
    - apply cons.
      + apply append.
        * apply (hd M).
        * apply (hd N).
      + apply cc.
        * apply (tl M).
        * apply (tl N).
Defined.

Infix "++'" := cc (at level 60, right associativity): mat_scope.

Fact eta0_col: forall {n} (M: matrix n O),
  M = emptyM.
Proof.
  induction M; auto.
  simpl. f_equal; auto using eta0.
Qed.

Fact eta_col: forall {n m} (M: matrix n (S m)),
  M = col (hc M) ++' tc M.
Proof.
  induction M; auto.
  simpl. f_equal; auto.
  apply (eta h).
Qed.

Lemma cc_empty: forall {n m} (M: matrix n m),
  @emptyM n ++' M = M.
Proof.
  induction M; auto.
  simpl. f_equal; auto.
Qed.

Global Hint Resolve cc_empty : mat_scope.

Lemma cc_dist: forall {k n m} (N: matrix k n) (M: matrix k m) (u: vec n) (v: vec m),
  (N ++' M) @ (u ++ v) = ((N @ u) + (M @ v))%Vec.
Proof.
  induction k.
    - intros. rewrite (eta0 (N @ u)), (eta0 (M @ v)). auto.
    - intros. rewrite (eta N), (eta M).
      simpl. rewrite IHk. cbn. f_equal.
      rewrite dot_split. lra.
Qed.

(* MATMAT def *)

Fixpoint matmultmat {n k m} (N: matrix n k) (M: matrix k m): matrix n m.
destruct m.
  - apply emptyM.
  - apply (cc (col (N@ hc M))).
    eapply matmultmat.
      + apply N.
      + apply (tc M).
Defined.

Infix "@@" := matmultmat (at level 40, left associativity): mat_scope.

Fixpoint tM {n m} (M: matrix n m) : matrix m n.
destruct m.
  - apply [].
  - apply cons.
    + apply (hc M).
    + apply tM.
      apply (tc M).
Defined.

Definition is_Linv_of {n r}
  (A: matrix n r) (B: matrix r n) :=
  A @@ B = I.

Definition is_Rinv_of {n r}
  (A: matrix r n) (B: matrix n r) :=
   B @@ A = I.

Definition sqmatrix (n: nat) := matrix n n.

Definition is_inv_of {n}
  (A: sqmatrix n) (B: sqmatrix n) :=
  is_Linv_of A B /\ is_Rinv_of A B.

Fixpoint trace {n} (A: sqmatrix n): R.
  destruct n.
    - apply R0.
    - apply Rplus.
      + apply (hd (hd A)).
      + apply (trace n (tl (tc A))).
Defined.

Inductive is_diag: forall {n}, sqmatrix n -> Prop :=
  | diag_empty: is_diag []
  | S_diag: forall {n} (d: R) (D: sqmatrix n), is_diag D -> is_diag ((d::0%Vec)::(col 0%Vec ++' D)).

Fixpoint diag {n} (d: vec n): sqmatrix n.
  destruct n.
    - apply [].
    - apply cons.
      + apply (hd d :: 0%Vec).
      + apply (@cc n (S 0) n).
        * apply (col 0%Vec).
        * apply diag.
          apply (tl d).
Defined.

(* MATMAT proofs *)

Lemma mat_mult_emptyl: forall {n m} (A: matrix n m),
  [] @@ A = [].
Proof.
  induction A.
    - destruct m; auto.
    - destruct m; auto.
Qed.

Lemma mat_mult_vec_empty: forall {n} (A: matrix n O),
  A @ [] = 0%Vec.
Proof.
  induction n.
    - intros. rewrite (eta0_col A). trivial.
    - intros. rewrite (eta0_col A). simpl. rewrite IHn. trivial.
Qed.

Global Hint Resolve mat_mult_vec_empty : mat_scope.

Lemma mat_mult_I: forall {n m} (M: matrix n m),
  I @@ M = M.
Proof.
  induction m; auto.
    - intros. simpl. induction M; auto. simpl. f_equal; auto. symmetry. apply eta0.
    - intros.
      cbn. rewrite IHm. rewrite vec_mult_I.
      symmetry. apply eta_col.
Qed.

Global Hint Resolve mat_mult_I : mat_scope.

Lemma mat_tail_col_commute: forall {m n}
  (A: matrix (S n) m) (x: vec m),
  tl (col (A @ x)) = col (tl A @ x).
Proof.
  induction m.
    - intros. rewrite (eta0_col _). trivial.
    - intros. rewrite (eta x), (eta_col A).
      simpl. f_equal.
Qed.

Lemma mat_tail_mult_commute: forall {m n r}
  (B: matrix (S n) r) (A: matrix r m),
    tl (B @@ A) = tl B @@ A.
Proof.
  induction m; auto.
  intros. simpl. rewrite IHm.
  rewrite mat_tail_col_commute.
  trivial.
Qed.

Lemma mat_head_mult_commute: forall {m n r}
  (B: matrix (S n) r) (A: matrix r m),
  hd (B @@ A) = tM A @ hd B.
Proof.
  induction m; auto.
  intros. simpl. rewrite IHm.
  rewrite (eta B) at 1. simpl. rewrite dot_comm. trivial.
Qed.

Lemma mat_tl_tc_commute: forall {n m}
  (M: matrix (S n) (S m)),
    tl (tc M) = tc (tl M).
Proof.
  intros.
  rewrite (eta_col _). trivial.
Qed.

Global Hint Resolve mat_tl_tc_commute : mat_scope.

Lemma mat_tm_tc_commute: forall {m n}
  (M: matrix (S n) m),
    tc (tM M) = tM (tl M).
Proof.
  induction m; auto.
  intros. simpl. rewrite IHm.
  rewrite (eta_col M). trivial.
Qed.

Lemma mat_tm_tl_commute: forall {n m}
  (M: matrix n (S m)),
    tl (tM M) = tM (tc M).
Proof. intros. trivial. Qed.

Lemma mat_hd_hc_hd_eq: forall {n m}
  (M: matrix (S n) (S m)),
  hd (hc M) = hd (hd M).
Proof. intros. rewrite (eta M) at 1. trivial. Qed.

Lemma mat_hc_hd_commute: forall {m n}
  (M: matrix (S n) m),
    hc (tM M) = hd M.
Proof.
  induction m.
    - intros. rewrite (eta0_col M). trivial.
    - intros. simpl. rewrite IHm.
      rewrite (eta M) at 2. simpl.
      rewrite (mat_hd_hc_hd_eq).
      rewrite eta. trivial.
Qed.

Lemma mat_hd_col_hd: forall {n m}
  (M: matrix (S n) (S m)),
  hd (col (hd M)) = [hd (hd M)].
Proof.
  intros.
  rewrite (eta (hd M)). simpl. trivial.
Qed.

Lemma tm_dist: forall {m n}
  (M: matrix (S n) m),
  tM M = col (hd M) ++' tM (tl M).
Proof.
  induction m; auto.
  intros. simpl.
  rewrite (IHm). f_equal; auto.
    - rewrite (eta (hd M)). simpl.
      rewrite (eta M) at 1.
      trivial.
    - rewrite mat_tl_tc_commute.
      f_equal. rewrite (eta (hd M)). simpl.
      f_equal. rewrite (eta M). trivial.
Qed.

Lemma mat_tm_tm: forall {n m} (M: matrix n m), tM (tM M) = M.
Proof.
  induction n; auto.
    - intros. rewrite eta0. trivial.
    - destruct m.
      -- intros. rewrite (eta0_col M). simpl.
      f_equal. trivial. rewrite (eta0_col _). trivial.
      -- intros.
      rewrite (eta M) at 2. simpl.
      f_equal.
      + rewrite mat_hc_hd_commute.
        rewrite (eta M). simpl.
        rewrite <- (eta _). trivial.
      +  rewrite tm_dist. simpl.
  rewrite mat_tm_tc_commute.
  rewrite IHn.
  rewrite (eta M). simpl.
  rewrite eta_col. trivial.
Qed.

Global Hint Resolve mat_tm_tm : mat_scope.

Lemma mat_tm_mult_vec: forall {n m}
  (A: matrix n (S m)) (x: vec n),
  tM A @ x = dot (hc A) x :: tM (tc A) @ x.
Proof. auto. Qed.

Lemma mat_mult_col: forall {n m}
  (A: matrix n (S m)) (x: vec (S m)),
  A @ x = (hd x * hc A + tc A @ tl x)%Vec.
Proof.
  induction n.
    - intros. rewrite (eta0), (eta0 _). trivial.
    - intros. rewrite (eta A) at 1.
      simpl (_ @ _) at 1. rewrite IHn.
      rewrite (eta A) at 4 5.
      simpl hc. simpl tc.
      simpl (_ @ _) at 2.
      rewrite (dot_step (hd A) x).
      rewrite (vec_plus_app_dist).
      f_equal.
      rewrite (Rmult_comm).
      trivial.
Qed.

Lemma mat_hd_dot_commute: forall {m n}
  (A: matrix (S n) m) (x: vec m),
  hd (A @ x) = dot (hd A) x.
Proof. intros. rewrite (eta A). trivial. Qed.

Lemma dot_mult_commute: forall {n} (a: R)
  (x y: vec n),
  (a * dot x y)%R = dot (a * x)%Vec y.
Proof.
  induction n.
    - intros. rewrite (eta0 _). simpl. lra.
    - intros. rewrite 2 dot_step.
      rewrite vec_mult_step. simpl hd.
      simpl tl.
      rewrite <- IHn. lra.
Qed.

Lemma mat_dot_comm: forall {n m}
  (A: matrix n m) (x: vec n) (y: vec m),
  dot x (A @ y) = dot (tM A @ x) y.
Proof.
  induction n.
    - intros. rewrite (eta0 _). rewrite (eta0_col _).
      rewrite mat_mult_vec_empty. rewrite dot_0. trivial.
    - destruct m; intros.
      { rewrite (eta0_col _).
        rewrite (eta0 _). rewrite mat_mult_vec_empty.
        rewrite (dot_comm). rewrite dot_0. trivial.
      }
  rewrite (mat_mult_col (tM A) _).
  rewrite mat_tm_tc_commute.
  rewrite dot_dist_l.
  rewrite <- IHn.
  rewrite mat_hc_hd_commute.
  rewrite (dot_step).
  rewrite mat_hd_dot_commute.
  rewrite dot_mult_commute.
  rewrite (eta A) at 2.
  simpl tl. trivial.
Qed.

Lemma mat_mult_mat_step: forall {n r m}
  (B: matrix n r) (A: matrix r (S m)),
    B @@ A = col (B @ hc A) ++' B @@ tc A.
Proof. intros. trivial. Qed.

Lemma mat_mult_mat_row_step: forall {m r n}
  (B: matrix (S n) r) (A: matrix r m),
  B @@ A = tM A @ hd B :: tl B @@ A.
Proof.
  induction m.
    - intros. simpl. trivial.
    - intros. simpl. rewrite IHm.
      simpl. f_equal.
      + rewrite dot_comm.
        rewrite <- mat_hd_dot_commute.
        rewrite (eta (B @ hc A)). simpl. trivial.
      + rewrite mat_tail_col_commute. trivial.
Qed.

Lemma mat_mult_vec_O:
  forall {n} (A: matrix n O) (x: vec O),
  A @ x = 0%Vec.
Proof.
  intros. rewrite (eta0_col _).
  rewrite (eta0 _). apply mat_mult_vec_empty.
Qed.

Global Hint Resolve mat_mult_vec_O : mat_scope.

Theorem mat_mult_mat_MAGIC:
  forall {n m} (B: matrix n O) (A: matrix O m),
  B @@ A = 0.
Proof.
  induction n.
    - intros. rewrite (eta0 _). trivial.
    - intros.
      rewrite (mat_mult_mat_row_step B A).
      rewrite (IHn).
      rewrite mat_mult_vec_O.
      trivial.
Qed.

Global Hint Resolve mat_mult_mat_MAGIC : mat_scope.

Lemma mat_mult_mat_vec_assoc:
  forall {n r m} (B: matrix n r) (A: matrix r m)
  (x: vec m),
    (B @@ A) @ x = B @ (A @ x).
Proof.
  induction n.
    - intros. rewrite (eta0), (eta0 _). trivial.
    - intros.
      destruct m.
        -- rewrite (eta0_col _).
           rewrite (eta0 _).
           rewrite (eta0_col A).
           rewrite 2 mat_mult_vec_empty.
           rewrite mat_mult_zeros. trivial.
        --
    rewrite (eta B) at 2.
    simpl (_ @ _) at 2.
    rewrite <- IHn.
    rewrite mat_mult_mat_row_step.
    replace ((tM A @ hd B :: tl B @@ A) @ x) with
    ( dot (tM A @ hd B) x :: (tl B @@ A) @ x).
    { f_equal. rewrite mat_dot_comm. trivial.
    } trivial.
Qed.


Lemma mat_scalar_comm: forall {n m}
  (a: R) (x: vec m) (A: matrix n m),
  A @ (a * x)%Vec = (a * A) @ x.
Proof.
  induction n.
    - intros. rewrite (eta0 A). trivial.
    - intros. rewrite (eta A).
      simpl.
      rewrite (dot_comm (hd A) (a * x))%Vec.
      rewrite <- 2 (dot_mult_commute).
      rewrite (dot_comm). f_equal.
      rewrite (IHn).
      auto.
Qed.

Lemma vec_tl_col_commute: forall {n}
  (x: vec (S n)),
  tl (col x) = col (tl x).
Proof. intros. rewrite (eta x). simpl. trivial. Qed.

Lemma hc_col: forall {n m}
  (x: vec n) (A: matrix n m),
  hc (col x ++' A) = x.
Proof.
  induction n.
    - intros. simpl. symmetry. apply eta0.
    - intros. simpl. rewrite (eta x) at 3.
      f_equal.
      + rewrite (eta x). trivial.
      + rewrite (eta x). simpl.
        apply IHn.
Qed.

Global Hint Resolve hc_col : mat_scope.

Lemma tc_col: forall {n m}
  (x: vec n) (A: matrix n m),
  tc (col x ++' A) = A.
Proof.
  induction n.
    - intros. rewrite (eta0). trivial.
    - intros. rewrite (eta A).
      simpl tc. f_equal.
      + rewrite (eta x). trivial.
      + rewrite (eta x). simpl.
        apply IHn.
Qed.

Global Hint Resolve tc_col : mat_scope.

Fact diag_step: forall {n} (A: sqmatrix (S n)),
  is_diag A -> A = ((hd(hd A))::0%Vec) :: (col 0%Vec ++' (tl (tc A))).
Proof.
  intros.
  inversion H; subst.
  apply (inj_pair2_eq_dec _ Nat.eq_dec) in H1.
  rewrite (eta A) at 1.
  rewrite (eta_col _) at 1.
  simpl.
  rewrite (eta A) in H1.
  rewrite (eta_col (hd A :: _)) in H1.
  simpl in H1.
  inversion H1; subst.
  apply (inj_pair2_eq_dec _ Nat.eq_dec) in H4.
  apply (inj_pair2_eq_dec _ Nat.eq_dec) in H5.
  apply (f_equal hc) in H5.
  rewrite 2 hc_col in H5.
  rewrite <- H4, H5. rewrite mat_tl_tc_commute. trivial.
Qed.

Fact diag_step_diag: forall {n} (A: sqmatrix (S n)),
  is_diag A -> is_diag (tl (tc A)).
Proof.
  intros.
  inversion H; subst.
    apply (inj_pair2_eq_dec _ Nat.eq_dec) in H1.
    rewrite (eta A) in H1.
    rewrite (eta_col (hd A :: _)) in H1.
    inversion H1; subst.
    apply (inj_pair2_eq_dec _ Nat.eq_dec) in H4.
    apply (inj_pair2_eq_dec _ Nat.eq_dec) in H5.
    apply (f_equal tc) in H5.
    rewrite 2 tc_col in H5.
    simpl.
    rewrite (mat_tl_tc_commute).
    rewrite <- H5. apply H2.
Qed.

Lemma mat_mult_mat_mat_assoc:
  forall {k n r m}
  (A: matrix n r) (B: matrix r m)
 (C: matrix m k),
    A @@ B @@ C = A @@ (B @@ C).
Proof.
  induction k.
    - intros. rewrite (eta0_col _). trivial.
    - intros.
      rewrite 2 (mat_mult_mat_step _ C).
      rewrite IHk.
      destruct n; auto.
      rewrite (mat_mult_mat_step A (col (B @ hc C) ++' B @@ tc C)).
      f_equal.
      + rewrite hc_col.
        rewrite (mat_mult_mat_vec_assoc).
        trivial.
      + rewrite tc_col. trivial.
Qed.

Theorem mat_mult_tm_dist: forall {n r m}
  (A: matrix n r) (B: matrix r m),
    tM (A @@ B) = tM B @@ tM A.
Proof.
  induction n.
    - intros. rewrite (eta0 A).
      rewrite (eta0 ([] @@ B)).
      induction m; auto.
      simpl. f_equal. apply (IHm (tc B)).
    - intros.
      rewrite tm_dist.
      rewrite mat_tail_mult_commute.
      rewrite IHn.
      simpl. rewrite mat_tm_tc_commute. f_equal.
      f_equal.
      rewrite mat_hc_hd_commute.
      apply mat_head_mult_commute.
Qed.

Lemma mat_tm_I: forall {n},
  @tM n n I = I.
Proof.
  intros.
  assert(A := @mat_mult_tm_dist n n n I (tM I)).
  rewrite (mat_mult_I) in A.
  rewrite mat_tm_tm in A.
  rewrite (mat_mult_I) in A.
  auto.
Qed.

Global Hint Resolve mat_tm_I : mat_scope.

Lemma mat_mult_I_r: forall {n m} (A: matrix n m),
  A @@ I = A.
Proof.
  intros.
  assert (D := @mat_mult_tm_dist m m n I (tM A)).
  rewrite (mat_tm_I) in D.
  rewrite mat_mult_I in D.
  rewrite (mat_tm_tm) in D.
  auto.
Qed.

Global Hint Resolve mat_mult_I_r : mat_scope.

Lemma mat_inv_eq: forall {n} (A L R: sqmatrix n),
  L @@ A = I -> A @@ R = I -> L = R.
Proof.
  intros.
  rewrite <- (mat_mult_I_r L).
  rewrite <- H0.
  rewrite <- mat_mult_mat_mat_assoc.
  rewrite H.
  apply mat_mult_I.
Qed.

Lemma mat_diag_vec: forall {n} (x: vec n),
  is_diag (diag x).
Proof.
  induction n.
    - intros. constructor.
    - intros. simpl. apply S_diag. apply IHn.
Qed.

Lemma mat_diag_exist: forall {n} (D: sqmatrix n),
  is_diag D <-> exists x, D = diag x.
Proof.
  induction n.
    - intros. split.
      + intros. exists []. rewrite (eta0 _). trivial.
      + intros [x A]. rewrite (eta0 _). constructor.
    - intros. split.
      + intros.
        assert (B := diag_step_diag D H).
        destruct (IHn (tl (tc D))) as [X _].
        specialize (X B).
        destruct X.
        exists (hd (hd D) :: x).
        simpl. rewrite <- H0.
        apply diag_step. trivial.
      + intros [x H].
        simpl in H.
    rewrite H.
    apply S_diag.
    apply IHn.
    exists (tl x).
    trivial.
Qed.

Lemma mat_hc_app_dist: forall {m n k}
  (A: matrix n (S m)) (B: matrix k (S m)),
  hc (A ++ B) = hc A ++ hc B.
Proof.
  induction n.
    - intros. rewrite (eta0 _). trivial.
    - intros. rewrite (eta A). simpl.
      f_equal. apply IHn.
Qed.

Lemma mat_tc_app_dist: forall {m n k}
  (A: matrix n (S m)) (B: matrix k (S m)),
  tc (A ++ B) = tc A ++ tc B.
Proof.
  induction n.
    - intros. rewrite (eta0 _). trivial.
    - intros. rewrite (eta A). simpl.
      f_equal. apply IHn.
Qed.

Lemma mat_tm_app_dist: forall {m n k}
  (A: matrix n m) (B: matrix k m),
  tM (A ++ B) = tM A ++' tM B.
Proof.
  induction m.
    - intros. trivial.
    - intros.
      simpl. rewrite mat_hc_app_dist. f_equal.
      rewrite mat_tc_app_dist.
      apply IHm.
Qed.

Theorem mat_mult_app_dist: forall {n m r k}
  (A: matrix n m) (C: matrix m k)
  (B: matrix n r) (D: matrix r k),
  (A ++' B) @@ (C ++ D) = A @@ C + B @@ D.
Proof.
  induction n.
    - intros. rewrite (eta0), (eta0 _). trivial.
    - intros.
      rewrite 3 mat_mult_mat_row_step.
      rewrite mat_tm_app_dist.
      simpl. cbn. rewrite cc_dist. f_equal.
      rewrite IHn.
      trivial.
Qed.

Lemma mat_app_cc_dist: forall {n m k r}
  (A: matrix n m) (B: matrix r m)
  (C: matrix n k) (D: matrix r k),
  (A ++ B) ++' (C ++ D) = (A ++' C) ++ (B ++' D).
Proof.
  induction n.
    - intros. rewrite (eta0 A), (eta0 C). trivial.
    - intros.
      simpl. rewrite 2 hd_app.
      f_equal.
      rewrite 2 tl_app.
      apply IHn.
Qed.

Lemma mat_tm_app_col_dist: forall {n m k}
  (A: matrix m n) (B: matrix k n),
  tM (A ++ B) = tM A ++' tM B.
Proof.
  intros. rewrite <- mat_tm_tm.
  rewrite mat_tm_app_dist.
  intuition.
Qed.

Lemma mat_app_0: forall {m n k},
  (0: matrix n m) ++ (0: matrix k m) = 0.
Proof.
  induction n.
    - intros. trivial.
    - intros. simpl. f_equal. apply IHn.
Qed.

Global Hint Resolve mat_app_0 : mat_scope.

Lemma mat_hc_cc: forall {n m k}
  (A: matrix n (S m)) (B: matrix n k),
  hc (A ++' B) = hc A.
Proof.
  induction n.
    - intros. rewrite eta0. trivial.
    - intros. simpl.
  rewrite (eta A) at 3.
  simpl. f_equal; auto.
  apply hd_app.
Qed.

Lemma mat_hd_tc_commute: forall {n m}
  (A: matrix (S n) (S m)),
  hd (tc A) = tl (hd A).
Proof. intros.
  rewrite (eta_col _). trivial.
Qed.

Lemma mat_tc_cc: forall {n m k}
  (A: matrix n (S m)) (B: matrix n k),
  tc (A ++' B) = tc A ++' B.
Proof.
  induction n.
    - intros. rewrite eta0. trivial.
    - intros. simpl.
  rewrite tl_app.
  rewrite mat_hd_tc_commute.
  f_equal.
  rewrite IHn.
  rewrite mat_tl_tc_commute.
  trivial.
Qed.

Lemma mat_hc_0: forall {n m},
  hc (0: matrix n (S m)) = 0%Vec.
Proof.
  induction n.
    - auto.
    - intros. simpl. f_equal. auto.
Qed.

Global Hint Resolve mat_hc_0 : mat_scope.

Lemma mat_tc_0: forall {n m},
  tc (0: matrix n (S m)) = 0.
Proof.
  induction n.
    - auto.
    - intros. simpl. f_equal. auto.
Qed.

Global Hint Resolve mat_tc_0 : mat_scope.

Lemma mat_cc_0: forall {m n k},
  (0: matrix n m) ++' (0: matrix n k) = (0: matrix n (m + k)).
Proof.
  induction m.
    - intros. rewrite (eta0_col _). apply cc_empty.
    - intros. rewrite (eta_col _).
      rewrite (eta_col).
      rewrite mat_tc_cc.
      rewrite mat_hc_cc.
      rewrite mat_hc_0.
      rewrite mat_tc_0.
      f_equal.
        + f_equal.
          destruct n; auto.
          simpl.
          rewrite mat_hc_0. trivial.
        + destruct n; auto.
          simpl.
          rewrite mat_tc_0. apply IHm.
Qed.

Lemma mat_tm_cc_dist: forall {n m k}
  (A: matrix m n) (B: matrix m k),
  tM (A ++' B) = tM A ++ tM B.
Proof.
  induction n.
    - intros. rewrite (eta0_col _).
      rewrite cc_empty.
      trivial.
    - intros.
      simpl.
      f_equal.
      { apply mat_hc_cc. }
      rewrite mat_tc_cc.
      apply IHn.
Qed.

Lemma mat_vec_app_dist: forall {n m k}
  (A: matrix n m) (B: matrix k m) (x: vec m),
  (A ++ B) @ x = A @ x ++ B @ x.
Proof.
  induction n.
    - intros. rewrite (eta0 _). trivial.
    - intros.
      rewrite (eta A).
      simpl.
      rewrite IHn. trivial.
Qed.

Theorem mat_mult_app_col_dist: forall {n r m k L}
  (A: matrix n m) (C: matrix m k)
  (B: matrix r m) (D: matrix m L),
  (A ++ B) @@ (C ++' D) =
  (A @@ C ++' A @@ D) ++ (B @@ C ++' B @@ D).
Proof.
  induction n.
    - induction r.
      + intros. simpl. apply (eta0 _).
      + intros.
        simpl.
        rewrite 2 mat_tail_mult_commute.
        rewrite 2 mat_head_mult_commute.
        rewrite (eta0 _).
        simpl. rewrite mat_mult_mat_row_step.
        f_equal.
      * rewrite mat_tm_cc_dist.
        apply mat_vec_app_dist.
      * specialize (IHr m k L [] C (tl B) D).
        simpl in IHr.
        apply IHr.
    - intros.
      simpl.
      rewrite ! mat_head_mult_commute.
      rewrite ! mat_tail_mult_commute.
      simpl. rewrite <- IHn.
      rewrite mat_mult_mat_row_step.
      simpl. f_equal.
       +
      rewrite mat_tm_cc_dist.
      rewrite hd_app.
      apply mat_vec_app_dist.
       +
      rewrite tl_app. trivial.
Qed.

Lemma mat_hc_I: forall {n},
  hc (I: matrix (S n) (S n)) = R1::0%Vec.
Proof.
  intros.
  rewrite <- mat_tm_I.
  rewrite mat_hc_hd_commute.
  trivial.
Qed.

Lemma vec_hc_col: forall {n} (x: vec n),
  hc (col x) = x.
Proof.
  induction n.
    - intros. rewrite (eta0 _), (eta0). trivial.
    - intros. rewrite (eta x). simpl. f_equal. apply IHn.
Qed.

Lemma vec_0_mult: forall {n}
  (x: R),
  (x * 0: vec n)%Vec = 0%Vec.
Proof.
  induction n; auto.
  intros. rewrite vec_mult_step.
  simpl. f_equal. { lra. }
  apply IHn.
Qed.

Lemma mat_mult_vec_col0: forall {n}
  (x: vec 1),
  col 0%Vec @ x = (0: vec n)%Vec.
Proof.
  induction n; auto.
  intros.
  rewrite mat_mult_col.
  rewrite vec_mult_step.
  simpl. rewrite vec_plus_step.
  simpl. f_equal. { lra. }
  rewrite (eta0 _).
  rewrite (mat_mult_vec_empty _).
  rewrite vec_hc_col.
  rewrite vec_plus_0.
  apply vec_0_mult.
Qed.

Lemma mat_mult_col0: forall {n m}
  (A: matrix 1 n),
  col (0%Vec : vec m) @@ A = 0.
Proof.
  induction m.
    - intros. rewrite (eta0). apply eta0.
    - intros. rewrite mat_mult_mat_row_step.
      rewrite (eta 0).
      simpl.
      f_equal; auto.
      rewrite mat_mult_col.
      simpl. rewrite mat_mult_vec_empty.
      rewrite vec_plus_0.
      rewrite vec_mult_0. trivial.
Qed.

Lemma mat_plus_zero_GIBBERISH: forall {n m}
  (A B: matrix n m),
  A = 0 -> A + B = B.
Proof.
  intros. rewrite H.
  rewrite mat_plus_comm.
  apply mat_plus_0.
Qed.

Lemma vec_mult_1: forall {n}
  (x: vec n),
  (R1 * x)%Vec = x.
Proof.
  induction n.
   - intros. rewrite (eta0). apply eta0.
   - intros. rewrite vec_mult_step.
     rewrite eta.
     f_equal; auto.
    lra.
Qed.

Lemma mat_II_gibberish: forall {m n} (A: matrix (S n) m),
  ((R1 :: 0%Vec) :: col 0%Vec ++' I) @@ A = A.
Proof.
  intros.
  rewrite mat_mult_mat_row_step.
  simpl.
  replace A with ([hd A] ++ tl A) at 2.
  { rewrite (mat_mult_app_dist _ [hd A] _ _).
    rewrite mat_mult_I.
    rewrite (eta A) at 4.
    f_equal.
    - rewrite mat_mult_col.
      simpl. rewrite mat_mult_zeros.
      rewrite vec_plus_0.
      rewrite (mat_hc_hd_commute).
      apply vec_mult_1.
    - apply mat_plus_zero_GIBBERISH.
      apply mat_mult_col0.
  }
  simpl. symmetry. apply eta.
Qed.

Lemma mat_mult_I_eq: forall {n} (B: sqmatrix n),
  (forall {m} (A: matrix n m), B @@ A = A)
  -> B = I.
Proof.
  intros.
  specialize (H n I).
  rewrite mat_mult_I_r in H.
  apply H.
Qed.

Fact mat_I_step: forall {n},
  (I: sqmatrix (S n)) = ((R1 :: 0%Vec) :: col 0%Vec ++' I).
Proof.
  intros.
  symmetry. apply mat_mult_I_eq.
  intros. apply mat_II_gibberish.
Qed. 

Lemma mat_tc_tl_I: forall {n},
  tl (tc (I: sqmatrix (S n))) = I.
Proof.
  intros. rewrite mat_I_step.
  simpl. apply tc_col.
Qed.

Lemma mat_I_is_diag: forall {n},
  @is_diag n I.
Proof.
  induction n.
    - constructor.
    - rewrite mat_I_step. apply S_diag.
      apply IHn.
Qed.

Close Scope mat_scope.
Close Scope vec_scope.
Close Scope R_scope.