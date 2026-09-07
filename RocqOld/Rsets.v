Add LoadPath "C:\Progis\Coq\Prog\matrix" as Matrix.
Load Rprops.

Open Scope R.
Open Scope vec_scope.
Open Scope mat_scope.

(* MEM def *)

Require Import Bool.
Definition set (A : Set) := A -> bool.

Definition is_mem {A: Set} (H: set A) (a : A) := H a = true.

Theorem is_mem_dec (A : Set) (H : set A) :
  forall a, { is_mem H a } +  { ~(is_mem H a) }.
  unfold is_mem. intros a.
  apply (bool_dec (H a)).
Qed.

Theorem is_mem_contradict (A : Set) (H : set A) :
  forall a, is_mem H a -> ~is_mem H a -> False.
  intros a; auto.
Qed.

Theorem is_mem_not (A : Set) (H : set A):
  forall a, ~is_mem H a <-> (H a) = false.
  intros a.
  unfold is_mem.
  rewrite <- not_true_iff_false.
  reflexivity.
Qed.

Structure img {n m} (A: matrix n m) := make_img {
  img_mem :> set (vec n) ;
  has_og: forall z, is_mem img_mem z <-> exists x, A@x = z ;
}.

Structure ker {n m} (A: matrix n m) := make_ker {
  ker_mem :> set (vec m) ;
  is_0: forall z, is_mem ker_mem z <-> A@z = 0%Vec ;
}.

(* SPAN def *)

Inductive lin_ind {m}: forall {n}, matrix n m -> Prop :=
  | empty_ind: lin_ind []
  | S_ind: forall {n} (B: matrix n m) z, ~(exists x, tM B @ x = z) -> lin_ind (z :: B).

Definition spans {n m} (A: matrix n m) :=
  forall x, exists y, tM A @ y = x.

(* SPAN proofs *)

Goal lin_ind [[R1; R0];[R0;R1]].
Proof.
  apply S_ind.
  intros [x A].
  rewrite (eta x) in A.
  rewrite (eta0 (tl x)) in A.
  apply (f_equal hd) in A.
  cbn in A. lra.
Qed.

Goal forall {n m} (A: matrix n m),
  ~(lin_ind (0%Vec :: A)).
Proof.
  intros n m A H.
  inversion H; subst.
  apply H2.
  exists 0%Vec.
  intuition.
Qed.

(* SPAN proofs *)

Require Import Logic.Eqdep_dec.

Global Hint Resolve inj_pair2_eq_dec : mat_scope.

Ltac depeq H :=
  apply inj_pair2_eq_dec in H; auto using eq_nat_dec.

Fact lin_ind_step: forall {n m}
  (A: matrix (S n) m),
  lin_ind A ->
  ~(exists x, tM (tl A) @ x = hd A).
Proof.
  intros n m A H [x D].
  inversion H; subst.
  apply H2.
  exists x.
  apply inj_pair2_eq_dec in H1; auto using eq_nat_dec.
  rewrite <- H1 in D. apply D.
Qed.

Goal forall {n m} (A: matrix n m),
  (exists (B: matrix m n), B @@ A = I) -> spans A.
Proof.
  intros n m A [B H] x.
  exists (tM B @ x).
  rewrite <- mat_mult_mat_vec_assoc.
  rewrite <- mat_mult_tm_dist.
  rewrite H.
  rewrite mat_tm_I.
  apply vec_mult_I.
Qed.

Goal forall {n m} (A: matrix n m),
  (exists (B: matrix m n), A @@ B = I) -> spans (tM A).
Proof.
  intros n m A [B H] x.
  exists (B @ x).
  rewrite <- mat_mult_mat_vec_assoc.
  rewrite mat_tm_tm.
  rewrite H.
  apply vec_mult_I.
Qed.
(*
Theorem mat_Linv: forall {k m n} (A: matrix n m),
  spans A -> exists (B: matrix k n), B @@ A = I.
Proof.
  unfold spans.
  induction k.
   - intros. exists []. apply eta0.
   - intros.
     specialize (IHk m n A H).
     destruct IHk as [B0 E].
     destruct (H (canon_e O)).
     exists (x :: eyeM 1 @@ B0).
     simpl.
     rewrite mat_mult_mat_row_step.
     simpl.
     rewrite H0.
     f_equal. rewrite mat_mult_mat_mat_assoc.
     rewrite E. Check mat_mult_I_r.
     apply mat_mult_I_r.
     destruct m. {
     induction n.
        - exists emptyM. rewrite (eta0_col).
          trivial.
        - specialize (IHn (tl A)).
          
      destruct (H (R1::0%Vec)).
      assert (D:
        forall x: vec m,
        exists y: vec n, tM (tc A) @ y = x).
      { intros. specialize (H (R0::x0)).
        destruct H.
        simpl in H.
        inversion H; subst.
        depeq H3.
        exists x1. auto.
      }
      destruct (IHm n (tc A) D) as [B0 E].
      apply (f_equal (fun x => @eyeM 1 m m @@ x)) in E.
      rewrite <- mat_mult_mat_mat_assoc in E.
      rewrite mat_mult_I_r in E.
      rewrite mat_I_step.
      exists (x :: (eyeM 1 @@ B0)).
      rewrite mat_mult_mat_row_step.
      simpl hd. rewrite H0. f_equal.
      simpl. 
      f_equal. f_equal. admit.
      rewrite E. simpl.
       
Qed.

Goal forall {n m} (A: matrix n m),
  spans A -> lin_ind A -> n = m.
Proof.
  unfold spans.
  induction n.
    - intros.
      destruct m; auto.
      specialize (H 1%Vec).
      destruct H.
      apply (f_equal hd) in H.
      simpl in H.
      rewrite (dot_comm) in H.
      rewrite (eta0 x) in H.
      simpl in H.
      lra.
    - intros.
      apply lin_ind_step in H0.
      destruct m.
      { exfalso. apply H0. exists 0%Vec. rewrite (eta0 _), (eta0). trivial. }
      f_equal.
      eapply (IHn _ (tl (tc A))).
      + intros.
        destruct (H (0%R::x)).
        simpl in H1.
        assert (D := cons_inj H1);
        destruct D.
        rewrite mat_mult_col in H3.
        rewrite (mat_tm_tc_commute) in H3.
        exists (tl x0 + hd x0 * canon_e O)%Vec.
        rewrite mat_vec_dist.
        rewrite (mat_scalar_comm).
        
Admitted.
*)

Close Scope vec_scope.
Close Scope mat_scope.
Close Scope R.