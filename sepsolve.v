Require Import Psatz.
Load Karamata.
Load sepsolve_vec.
Open Scope R_scope.
Open Scope vec_scope.

Definition gaussian {n: nat} := (vec n * vec n)%type.

Fixpoint is_ca_separated {n m: nat} (c: R) (a: vec n)
  (g: @gaussian n) (l: Vector.t (@gaussian n) m): Prop.
destruct l.
  - apply True.
  - inversion g as [mu sigm].
    destruct h as [mu2 sigm2].
    apply (
      c * dot a sigm  <= dot a (sqvec (mu - mu2)) /\
      c * dot a sigm2 <= dot a (sqvec (mu - mu2)) /\
      is_ca_separated n n0 c a g l
    ).
Defined.

Fixpoint c_separates {n m: nat} (c: R) (a: vec n)
  (l: Vector.t (@gaussian n) m) : Prop.
destruct l.
  - apply True.
  - apply (
      is_ca_separated c a h l /\
      c_separates n n0 c a l
    ).
Defined.

Goal forall (n m: nat) (c: R) (l: Vector.t (@gaussian n) m),
  c_separates c 0 l.
Proof.
  induction l.
    - reflexivity.
    - simpl. constructor; auto.
      cut (forall n m c (g: @gaussian n) (l: Vector.t _ m), @is_ca_separated n _ c 0 g l); auto.
      intros. induction l0.
      + reflexivity.
      + simpl. destruct g, h0. constructor; auto.
        ++ rewrite 2dot_0. lra.
        ++ constructor; auto. rewrite 2dot_0. lra.
Qed.

(* Equal-cardinality partition: binary selector, exactly m entries,
   and selected sum is half of total sum. *)
Definition is_ec_partition {d : nat} (a s : vec d) : Prop :=
  is_binary a /\
  dot a 1 = INR d / 2 /\
  dot a s = dot s 1 / 2
.

Definition box_constraints {d : nat} (a : vec d) : Prop :=
  is_vec_leq 0 a /\ is_vec_leq a 1.

Definition has_ec_partition {d : nat} (s : vec d) : Prop :=
  exists a, is_ec_partition a s.


(* The three Gaussians from the reduction. *)
Definition red_g1 {d : nat} : @gaussian d :=
  (0, 1).

Definition red_g2 {d : nat} (s : vec d) : @gaussian d :=
  (INR d / 2 * sqrtvec s, INR d / 2 * 1).

Definition red_g3 {d : nat} (s : vec d) : @gaussian d :=
  (- (dot s 1 / 2 * 1), INR d / 2 * s).

Definition red_instance {d : nat} (s: vec d)
  : Vector.t (@gaussian d) 3 :=
  [red_g1; red_g2 s; red_g3 s].

Definition c_separated_valid {n k: nat}
  (c: R) (m: nat) (a: vec n) (l: Vector.t gaussian k) :=
  is_binary a /\
  dot a 1 = (INR m) /\
  c_separates c a l
.

Lemma red_12:
  forall {n: nat} (d: nat) (a s: vec n),
  dot a (sqvec (0 - INR (2 * d) / 2 * sqrtvec s))
  = (INR d * INR d * dot a (sqvec (sqrtvec s)))%R
.
Proof.
  intros n d a s.
  rewrite vec_0_neg.
  rewrite sqvec_neg.
  replace (INR (2 * d) / 2) with (INR d).
  - rewrite sqvec_dist.
    apply dot_mult_dist_r.
  - rewrite mult_INR.
    simpl. lra.
Qed.

Lemma red_13:
  forall {n: nat} (a s: vec n),
  dot a (sqvec (0 - - (dot s 1 / 2 * 1))) = (dot s 1%Vec / 2 * (dot s 1%Vec / 2) * dot a 1%Vec)%R
.
Proof.
  intros n a s.
  rewrite vec_0_neg.
  rewrite 2 sqvec_neg.
  rewrite sqvec_dist.
  rewrite dot_mult_dist_r.
  rewrite sqvec_1.
  reflexivity.
Qed.

Theorem red_instance_correct_left :
  forall {d : nat} (a s : vec (2 * d)),
    perf_square_vec s ->
    c_separated_valid
      (dot s 1 / 2) d a (red_instance s)
    ->
    is_ec_partition a s
.
Proof.
  intros d a s Hsqrt Hvalid.
  unfold c_separated_valid in Hvalid.
  destruct Hvalid as [Ha [Hcard Hsep]].

  unfold red_instance, red_g1, red_g2, red_g3 in Hsep.
  simpl in Hsep.

  destruct Hsep as [Hfrom1 _].
  simpl in Hfrom1.

  (* From pair (1,2), using the second variance inequality. *)
  destruct Hfrom1 as [_ [H12 [_ [H13 _]]]].
  replace (INR (d + (d + 0))%nat) with (INR (2 * d)%nat) in H12, H13 by (f_equal; lia).
  rewrite red_12 in H12.
  rewrite red_13 in H13.
  replace (INR (2 * d) / 2) with (INR d) in H12, H13.
  2:{ rewrite mult_INR. simpl. lra. }
  rewrite dot_mult_dist_r in H12, H13.
  destruct (Nat.eq_dec d 0).
  { subst. simpl in a, s. rewrite (nil_spec a), (nil_spec s). split; [constructor|]. split; simpl; lra. }
  assert (Nd : 0 < INR d).
  { rewrite <- INR_0. apply lt_INR. lia. }

  assert (Hlower : dot s 1 / 2 <= dot a s).
  {
    rewrite sq_sqrt_vec in H12 by (auto using perf_square_non_neg).
    apply (Rmult_le_reg_l (INR d) _ _ Nd).
    rewrite <- Hcard at 1.
    rewrite (Rmult_comm (dot a 1)).
    apply (Rmult_le_reg_l (INR d) _ _ Nd).
    rewrite <- 2 Rmult_assoc.
    rewrite (Rmult_comm _ (dot _ _ / 2)).
    rewrite (Rmult_assoc (dot _ _ / 2)). apply H12.
  }

  assert (Hupper : dot a s <= dot s 1 / 2).
  {
    destruct (Req_dec (dot s 1) 0).
    + apply (non_neg_dot_0 _ (perf_square_non_neg _ Hsqrt)) in H.
      subst. rewrite (dot_comm _ 0).
      rewrite 2 dot_0. lra.
    + assert (B:= non_neg_dot_1 _ (perf_square_non_neg _ Hsqrt)).
      assert (B2: 0 < dot s 1 / 2) by lra.
      apply (Rmult_le_reg_l (INR d) _ _ Nd).
      rewrite <- Hcard at 2.
      rewrite (Rmult_comm (dot a 1)).
      apply (Rmult_le_reg_l (dot s 1 / 2) _ _ B2).
      rewrite <- (Rmult_assoc _ _ (dot a 1)). apply H13.
  }

  unfold is_ec_partition.
  constructor; auto.
  constructor.
  + rewrite mult_INR. simpl INR. lra.
  + lra.
Qed.

Lemma red_23 :
  forall {m} (a b c: vec m),
    is_binary a ->
    is_vec_leq 0 b ->
    is_vec_leq 0 c ->
      dot a (sqvec b) <= dot a (sqvec (b + c))
.    
Proof.
  induction m; intros a b c Ha Hb Hc.
  - rewrite (eta0 a), (eta0 b), (eta0 c).
    simpl. lra.
  - rewrite (eta a), (eta b), (eta c) in *.
    inversion Ha as [| ? ? ? Ha_hd Ha_tl]; subst; clear Ha.
    inversion Hb as [| ? ? ? ? ? Hb_hd Hb_tl]; subst; clear Hb.
    inversion Hc as [| ? ? ? ? ? Hc_hd Hc_tl]; subst; clear Hc.
    repeat match goal with
    | H : existT _ _ _ = existT _ _ _ |- _ =>
        apply (inj_pair2_eq_dec _ Nat.eq_dec) in H; subst; clear H
    end.
    rewrite !dot_step.
    simpl.
    specialize (IHm _ _ _ Ha_tl Hb_tl Hc_tl).
    destruct Ha_hd as [Ha | Ha]; subst; rewrite Ha; unfold sqvec in IHm.
    + rewrite 2 Rmult_0_l. rewrite 2 Rplus_0_l. apply IHm.
    + rewrite 2 Rmult_1_l. apply Rplus_le_compat; auto.
      nra.
Qed.

Theorem red_instance_correct_right :
  forall {d : nat} (a s : vec (2 * d)),
    perf_square_vec s ->
    is_ec_partition a s ->
    c_separated_valid (dot s 1 / 2) d a (red_instance s)
.
Proof.
  intros d a s P [B [D Sm]].
  split; auto.
  rewrite mult_INR in D. simpl in D.
  replace ((1+1) * INR d / 2) with (INR d) in D by lra.
  split.
    - apply D.
    - split.
    -- split.
    { rewrite red_12.
      rewrite (sq_sqrt_vec _ _ (perf_square_non_neg _ P)).
      rewrite Sm. rewrite Rmult_comm. apply Rmult_le_compat_r.
      - apply Rle_mult_inv_pos; [|lra].
        apply non_neg_dot_1.
        apply perf_square_non_neg; auto.
      - replace (dot a 1) with (INR d).
        rewrite <- mult_INR. apply le_INR.
        destruct (Nat.eq_dec d 0).
        { subst. lia. }
        apply Nat.le_mul_r. lia.
    }
    split.
    { rewrite red_12.
      rewrite (sq_sqrt_vec _ _ (perf_square_non_neg _ P)).
      replace (INR (2 * d) / 2) with (INR d).
      2:{ rewrite mult_INR. simpl. lra. }
      rewrite dot_mult_dist_r.
      rewrite Sm.
      replace (dot a 1) with (INR d). lra.
    }
    split.
    { rewrite red_13.
      replace (dot a 1) with (INR d).
      apply (Rmult_le_compat_r _ _ _ (pos_INR _)).
      assert (F: forall m (u v: vec m), is_binary u -> perf_square_vec v -> exists q, dot u v = INR q).
      { induction m; intros u v Bi Pe.
        + exists O. rewrite (nil_spec u). trivial.
        + rewrite (eta u) in Bi. rewrite (eta v) in Pe.
          inv (Bi, Pe). 
          destruct (IHm _ _ H3 H1).
          destruct H2.
          ++ exists (x0)%nat.
             rewrite dot_step.
             rewrite H, H2, <- H0. lra.
          ++ exists (x*x + x0)%nat.
             rewrite dot_step.
             rewrite H, H2, <- H0.
              rewrite <- mult_INR. rewrite plus_INR. lra.
      }
      destruct (F _ _ _ B P).
      destruct x.
      + simpl in H. replace (dot a s) with 0%R in Sm.
        rewrite <- Sm. lra.
      + assert (Sn: 1 <= dot s 1 / 2).
        { replace (dot a s) with (1 + INR x)%R in Sm.
          2:{ rewrite S_INR in H. lra. }
          assert (G:= pos_INR x). lra.
        } rewrite <- Rmult_1_l at 1. apply Rmult_le_compat_r; lra.
    }
    split; [|exact I].
    rewrite red_13.
    replace (INR (2*d) / 2) with (INR d).
    2:{ rewrite mult_INR. simpl. lra. }
    rewrite dot_mult_dist_r.
    rewrite <- D.
    rewrite Sm.
    rewrite (Rmult_comm (dot a 1)).
    lra.
    --
    split; [|auto].
    split.
    {
      replace (INR (2 * d) / 2) with (INR d).
      2:{ rewrite mult_INR. simpl. lra. }
      rewrite vec_sub_neg.
      eapply Rle_trans.
      2:{
        apply red_23; auto.
        - apply vec_sqrt_nonneg.
          + apply pos_INR.
          + apply perf_square_non_neg. exact P.
        - apply vec_nonneg_mult_1.
          apply Rle_mult_inv_pos; [|lra].
          apply non_neg_dot_1.
          apply perf_square_non_neg. exact P.
      }
      rewrite sqvec_dist.
      rewrite !dot_mult_dist_r.
      rewrite (sq_sqrt_vec _ _ (perf_square_non_neg _ P)).
      rewrite Sm.
      replace (dot a 1) with (INR d).
      lra.
    }
    {
      replace (INR (2 * d) / 2) with (INR d).
      2:{ rewrite mult_INR. simpl. lra. }
      rewrite vec_sub_neg.
      rewrite dot_mult_dist_r.
      rewrite Sm. simpl.
      split; [|trivial].
      eapply Rle_trans.
      2:{
        rewrite vec_plus_comm.
        apply red_23; auto.
        - apply vec_nonneg_mult_1.
          apply Rle_mult_inv_pos; [|lra].
          apply non_neg_dot_1.
          apply perf_square_non_neg. exact P.
        - apply vec_sqrt_nonneg.
          + apply pos_INR.
          + apply perf_square_non_neg. exact P.
      }
      rewrite sqvec_dist.
      rewrite dot_mult_dist_r.
      rewrite sqvec_1.
      rewrite D.
      lra.
    }
    split; exact I.
Qed.


Definition hinge (c D S : R) : R :=
  Rmax 0%R (c - D / S)
.

Fixpoint sumR (xs : list R) : R :=
  match xs with
  | List.nil => 0
  | List.cons x xs => x + sumR xs
  end.

Definition gaussian_pair_stats {d : nat}
  (a : vec d) (p : @gaussian d * @gaussian d) : R * R :=
  let (g1, g2) := p in
  let (mu1, sig1) := g1 in
  let (mu2, sig2) := g2 in
    (dot a (sqvec (mu1 - mu2)),
     Rmax (dot a sig1) (dot a sig2)).

Definition gaussian_pair_hinge {d : nat}
  (c : R) (a : vec d) (g1 g2 : @gaussian d) : R :=
  let (D, S) := gaussian_pair_stats a (g1, g2) in
    hinge c D S.

Fixpoint hinge_against {d : nat}
  (c : R) (a : vec d) (g : @gaussian d) (L : list (@gaussian d)) : R :=
  match L with
  | List.nil => 0
  | List.cons h L' => gaussian_pair_hinge c a g h + hinge_against c a g L'
  end.

Fixpoint hinge_form {d : nat}
  (c : R) (a : vec d) (L : list (@gaussian d)) : R :=
  match L with
  | List.nil => 0
  | List.cons g L' => hinge_against c a g L' + hinge_form c a L'
  end.

Fixpoint hinge_cross {d : nat}
  (c : R) (a : vec d) (L1 L2 : list (@gaussian d)) : R :=
  match L1 with
  | List.nil => 0
  | List.cons g L1' => hinge_against c a g L2 + hinge_cross c a L1' L2
  end.

Lemma hinge_against_app :
  forall {d : nat} (c : R) (a : vec d) (g : @gaussian d)
    (L1 L2 : list (@gaussian d)),
    hinge_against c a g (List.app L1 L2) =
      (hinge_against c a g L1 + hinge_against c a g L2)%R.
Proof.
  induction L1; intros.
  - simpl. lra.
  - simpl. rewrite IHL1. lra.
Qed.

Lemma hinge_form_app :
  forall {d : nat} (c : R) (a : vec d)
    (L1 L2 : list (@gaussian d)),
    hinge_form c a (List.app L1 L2) =
      (hinge_form c a L1 + hinge_form c a L2 +
       hinge_cross c a L1 L2)%R.
Proof.
  induction L1; intros.
  - simpl. lra.
  - simpl.
    rewrite hinge_against_app.
    rewrite IHL1.
    lra.
Qed.

Lemma hinge_cross_zero :
  forall {d : nat} (c : R) (a : vec d)
    (L1 L2 : list (@gaussian d)),
    (forall g, List.In g L1 -> hinge_against c a g L2 = 0%R) ->
    hinge_cross c a L1 L2 = 0%R.
Proof.
  induction L1; intros.
  - simpl. reflexivity.
  - simpl.
    rewrite H by (simpl; auto).
    rewrite IHL1.
    + lra.
    + intros. apply H. simpl. auto.
Qed.

Lemma hinge_form_app_no_cross :
  forall {d : nat} (c : R) (a : vec d)
    (L1 L2 : list (@gaussian d)),
    (forall g, List.In g L1 -> hinge_against c a g L2 = 0%R) ->
    hinge_form c a (List.app L1 L2) =
      (hinge_form c a L1 + hinge_form c a L2)%R.
Proof.
  intros.
  rewrite hinge_form_app.
  rewrite hinge_cross_zero by exact H.
  lra.
Qed.

Lemma gaussian_pair_stats_ordered :
  forall {d : nat} (a mu1 sig1 mu2 sig2 : vec d),
    is_vec_leq 0 a ->
    is_vec_leq sig1 sig2 ->
    gaussian_pair_stats a ((mu1, sig1), (mu2, sig2)) =
      (dot a (sqvec (mu1 - mu2)), dot a sig2).
Proof.
  intros d a mu1 sig1 mu2 sig2 Ha Hsig.
  unfold gaussian_pair_stats.
  rewrite Rmax_right.
  - reflexivity.
  - apply dot_vec_noneg; assumption.
Qed.

(* Recursive binary-well Gaussian schedule.  The class at index [i] has
   mean [m^i * 1].  For [i = 0] its covariance is [1]; for later indices
   it accumulates the pairwise separation scales against the earlier
   classes, all pointed at coordinate [i]. *)
Fixpoint gaussian_schedule_sigma_sum {d : nat}
  (m : R) (i k : nat) : vec d :=
  match k with
  | O => 0
  | S k' =>
      gaussian_schedule_sigma_sum m i k' +
      (((m ^ i - m ^ k') * (m ^ i - m ^ k'))%R *
       (m * canon_e i + 1))%Vec
  end.

Definition gaussian_schedule_mu {d : nat} (m : R) (i : nat) : vec d :=
  (m ^ i)%R * 1.

Definition gaussian_schedule_sigma {d : nat} (m : R) (i : nat) : vec d :=
  match i with
  | O => 1
  | S _ => gaussian_schedule_sigma_sum m i i
  end.

Definition gaussian_schedule_class {d : nat} (m : R) (i : nat)
  : @gaussian d :=
  (gaussian_schedule_mu m i, gaussian_schedule_sigma m i).

Fixpoint gaussian_schedule_from {d : nat} (m : R) (start n : nat)
  : Vector.t (@gaussian d) n :=
  match n with
  | O => []
  | S n' =>
      gaussian_schedule_class m start ::
      gaussian_schedule_from m (S start) n'
  end.

Definition gaussian_schedule {d : nat} (m : R) (n : nat)
  : Vector.t (@gaussian d) n :=
  gaussian_schedule_from m O n
.

Fixpoint gaussian_schedule_hinge_correction {d : nat}
  (a : vec d) (n : nat) : R :=
  match n with
  | O => 0
  | S n' =>
      gaussian_schedule_hinge_correction a n' +
      / (1 + dot a (canon_e (S n')))
  end.

Lemma gaussian_schedule_pair_stats_later_covariance :
  forall {d : nat} (m : R) (a : vec d) (i j : nat),
    dot a (gaussian_schedule_sigma m i) <=
      dot a (gaussian_schedule_sigma m j) ->
    gaussian_pair_stats a
      (gaussian_schedule_class m i, gaussian_schedule_class m j) =
      (dot a
         (sqvec
            (gaussian_schedule_mu m i - gaussian_schedule_mu m j)),
       dot a (gaussian_schedule_sigma m j)).
Proof.
  intros d m a i j Hle.
  unfold gaussian_pair_stats, gaussian_schedule_class.
  simpl.
  rewrite Rmax_right; auto.
Qed.

Lemma gaussian_schedule_pair_hinge_later_covariance :
  forall {d : nat} (m c : R) (a : vec d) (i j : nat),
    dot a (gaussian_schedule_sigma m i) <=
      dot a (gaussian_schedule_sigma m j) ->
    gaussian_pair_hinge c a
      (gaussian_schedule_class m i)
      (gaussian_schedule_class m j) =
      hinge c
        (dot a
           (sqvec
              (gaussian_schedule_mu m i - gaussian_schedule_mu m j)))
        (dot a (gaussian_schedule_sigma m j)).
Proof.
  intros d m c a i j Hle.
  unfold gaussian_pair_hinge.
  rewrite (gaussian_schedule_pair_stats_later_covariance m a i j Hle).
  reflexivity.
Qed.

Fixpoint gaussian_schedule_separation_sum
  (m : R) (i k : nat) : R :=
  match k with
  | O => 0
  | S k' =>
      gaussian_schedule_separation_sum m i k' +
      ((m ^ i - m ^ k') * (m ^ i - m ^ k'))%R
  end.


Fixpoint gaussian_schedule_distance_sum_from {d : nat}
  (a : vec d) (m : R) (j start n : nat) : R :=
  match n with
  | O => 0
  | S n' =>
      dot a
        (sqvec
          (gaussian_schedule_mu m start - gaussian_schedule_mu m j)) +
      gaussian_schedule_distance_sum_from a m j (S start) n'
  end.

Fixpoint hinge_to {d : nat}
  (c : R) (a : vec d) (L : list (@gaussian d)) (g : @gaussian d)
  : R :=
  match L with
  | List.nil => 0
  | List.cons h L' => gaussian_pair_hinge c a h g + hinge_to c a L' g
  end.

Lemma hinge_against_snoc :
  forall {d : nat} (c : R) (a : vec d) (g h : @gaussian d) L,
    hinge_against c a g (List.app L (List.cons h List.nil)) =
      (hinge_against c a g L + gaussian_pair_hinge c a g h)%R.
Proof.
  induction L; intros.
  - simpl. lra.
  - simpl. rewrite IHL. lra.
Qed.

Lemma hinge_form_snoc :
  forall {d : nat} (c : R) (a : vec d) (L : list (@gaussian d)) g,
    hinge_form c a (List.app L (List.cons g List.nil)) =
      (hinge_form c a L + hinge_to c a L g)%R.
Proof.
  induction L; intros.
  - simpl. lra.
  - simpl.
    rewrite hinge_against_snoc.
    rewrite IHL.
    lra.
Qed.

Lemma gaussian_schedule_from_snoc :
  forall {d : nat} (m : R) (start n : nat),
    to_list (@gaussian_schedule_from d m start (S n)) =
      List.app (to_list (gaussian_schedule_from m start n))
        (List.cons (gaussian_schedule_class m (start + n)) List.nil).
Proof.
  intros d m start n.
  revert m start.
  induction n; intros.
  - simpl. replace (start + 0)%nat with start by lia. reflexivity.
  - simpl gaussian_schedule_from in *.
    rewrite 1 to_list_cons.
    rewrite IHn.
    rewrite ! to_list_cons.
    simpl.
    replace (S (start + n))%nat with (start + S n)%nat by lia.
    reflexivity.
Qed.

Lemma gaussian_schedule_snoc :
  forall {d : nat} (m : R) (n : nat),
    to_list (@gaussian_schedule d m (S n)) =
      List.app (to_list (gaussian_schedule m n))
        (List.cons (gaussian_schedule_class m n) List.nil).
Proof.
  intros d m n.
  unfold gaussian_schedule.
  rewrite gaussian_schedule_from_snoc.
  reflexivity.
Qed.

Lemma gaussian_schedule_sigma_sum_factor :
  forall {d : nat} (m : R) (i k : nat),
    @gaussian_schedule_sigma_sum d m i k =
      gaussian_schedule_separation_sum m i k *
        (m * canon_e i + 1).
Proof.
  induction k; intros.
  - simpl. symmetry. apply vec_mult_0.
  - simpl. rewrite IHk.
    rewrite vec_mult_dist.
    reflexivity.
Qed.

Lemma gaussian_schedule_sigma_sum_dot :
  forall {d : nat} (m : R) (a : vec d) (i k : nat),
    dot a (gaussian_schedule_sigma_sum m i k) =
      (gaussian_schedule_separation_sum m i k *
       dot a (m * canon_e i + 1)%Vec)%R.
Proof.
  intros.
  rewrite gaussian_schedule_sigma_sum_factor.
  rewrite dot_mult_dist_r.
  reflexivity.
Qed.

Lemma canon_e_nonneg :
  forall (d i : nat), is_vec_leq 0 (@canon_e d i).
Proof.
  induction d; intros i.
  - simpl. constructor.
  - destruct i; simpl; constructor; try lra.
  + apply leq_refl.
  + apply IHd.
Qed.

Lemma canon_e_le_1 :
  forall (d i : nat), is_vec_leq (@canon_e d i) 1.
Proof.
  induction d; intros i.
  - simpl. constructor.
  - destruct i; simpl; constructor; try lra.
  + apply leq_0_1.
  + apply IHd.
Qed.

Lemma dot_canon_e_nonneg :
  forall {d : nat} (a : vec d) i,
    is_vec_leq 0 a ->
    0 <= dot a (canon_e i).
Proof.
  intros.
  apply dot_vec_noneg_0.
  - assumption.
  - apply canon_e_nonneg.
Qed.

Lemma dot_canon_e_le_dot_1 :
  forall {d : nat} (a : vec d) i,
    is_vec_leq 0 a ->
    dot a (canon_e i) <= dot a 1.
Proof.
  intros.
  apply dot_vec_noneg.
  - assumption.
  - apply canon_e_le_1.
Qed.

Lemma dot_schedule_axis :
  forall {d : nat} (m : R) (a : vec d) i,
    dot a (m * canon_e i + 1) =
      (m * dot a (canon_e i) + dot a 1%Vec)%R.
Proof.
  intros.
  rewrite dot_dist.
  rewrite dot_mult_dist_r.
  reflexivity.
Qed.

Lemma gaussian_schedule_mu_distance :
  forall {d : nat} (a : vec d) (m : R) (i j : nat),
    dot a
      (sqvec
        (gaussian_schedule_mu m i - gaussian_schedule_mu m j)) =
      (((m ^ i - m ^ j) * (m ^ i - m ^ j)) * dot a 1%Vec)%R.
Proof.
  induction d; intros a m i j.
  - rewrite (eta0 a). simpl. lra.
  - rewrite dot_step. simpl.
    unfold sqvec, gaussian_schedule_mu, subvecs, multvec in IHd.
    rewrite IHd.
    rewrite dot_step. simpl.
    lra.
Qed.

Lemma gaussian_schedule_distance_sum_from_0 :
  forall {d : nat} (a : vec d) (m : R) (j start : nat),
    gaussian_schedule_distance_sum_from a m j start 0 = 0%R.
Proof.
  reflexivity.
Qed.

Fixpoint gaussian_schedule_separation_sum_from
  (m : R) (j start n : nat) : R :=
  match n with
  | O => 0
  | S n' =>
      ((m ^ j - m ^ start) * (m ^ j - m ^ start) +
       gaussian_schedule_separation_sum_from m j (S start) n')%R
  end.

Lemma gaussian_schedule_distance_sum_from_ext :
  forall {d : nat} (a : vec d) (m : R) (j start n : nat),
    dot a 1 = m ->
    gaussian_schedule_distance_sum_from a m j start n =
      (m *
       gaussian_schedule_separation_sum_from m j start n)%R.
Proof.
  intros d a m j start n.
  revert d a m j start.
  induction n; intros.
  - simpl. lra.
  - simpl.
    rewrite gaussian_schedule_mu_distance.
    rewrite H.
    rewrite IHn by assumption.
    replace ((m ^ start - m ^ j) * (m ^ start - m ^ j))%R
      with ((m ^ j - m ^ start) * (m ^ j - m ^ start))%R by lra.
    lra.
Qed.

Lemma gaussian_schedule_separation_sum_nonneg :
  forall (m : R) (i k : nat),
    0 <= gaussian_schedule_separation_sum m i k.
Proof.
  induction k; intros.
  - simpl. lra.
  - simpl.
    assert (0 <= (m ^ i - m ^ k) * (m ^ i - m ^ k)).
    { apply Rle_0_sqr. }
    lra.
Qed.

Lemma gaussian_schedule_separation_sum_from_acc :
  forall (m : R) (j start n : nat),
    (gaussian_schedule_separation_sum_from m j start n +
     gaussian_schedule_separation_sum m j start =
     gaussian_schedule_separation_sum m j (start + n))%R.
Proof.
  intros m j start n.
  revert m j start.
  induction n; intros.
  - replace (start + 0)%nat with start by lia. simpl. lra.
  - simpl.
    replace (start + S n)%nat with (S start + n)%nat by lia.
    rewrite <- IHn. simpl.
    lra.
Qed.

Lemma gaussian_schedule_separation_sum_from_0 :
  forall (m : R) (j : nat),
    gaussian_schedule_separation_sum_from m j 0 j =
      gaussian_schedule_separation_sum m j j.
Proof.
  intros.
  pose proof (gaussian_schedule_separation_sum_from_acc m j 0 j) as H.
  simpl in H. lra.
Qed.

Lemma gaussian_schedule_separation_sum_extend_nonneg :
  forall (m : R) (i k n : nat),
    gaussian_schedule_separation_sum m i k <=
      gaussian_schedule_separation_sum m i (k + n).
Proof.
  intros m i k n.
  revert m i k.
  induction n; intros.
  - replace (k + 0)%nat with k by lia. lra.
  - replace (k + S n)%nat with (S (k + n))%nat by lia.
    simpl.
    pose proof (IHn m i k) as IH.
    pose proof (Rle_0_sqr (m ^ i - m ^ (k + n))) as Hsq.
    rewrite Rsqr_def in Hsq.
    lra.
Qed.

Lemma gaussian_schedule_separation_sum_le :
  forall (m : R) (i k l : nat),
    (k <= l)%nat ->
    gaussian_schedule_separation_sum m i k <=
      gaussian_schedule_separation_sum m i l.
Proof.
  intros.
  replace l with (k + (l - k))%nat by lia.
  apply gaussian_schedule_separation_sum_extend_nonneg.
Qed.

Lemma gaussian_schedule_separation_sum_ge_1 :
  forall (m : R) (j : nat),
    2 <= m ->
    (0 < j)%nat ->
    1 <= gaussian_schedule_separation_sum m j j.
Proof.
  intros m j Hm Hj.
  destruct j as [|j']; [lia|].
  simpl.
  pose proof (gaussian_schedule_separation_sum_nonneg m (S j') j') as Hprev.
  assert (Hpow : 1 <= m ^ j').
  { apply pow_R1_Rle. lra. }
  assert (Hdiff : 1 <= m ^ S j' - m ^ j').
  {
    simpl.
    replace (m * m ^ j' - m ^ j')%R with (m ^ j' * (m - 1))%R by ring.
    nra.
  }
  assert (Hhdiff: (1 <= (m ^ S j' - m ^ j') * (m ^ S j' - m ^ j'))%R).
  {
    rewrite <- (Rmult_1_l 1%R).
    apply Rmult_le_compat; lra.
  }
  simpl in Hhdiff.
  lra.
Qed.

Lemma gaussian_schedule_separation_term_scaled_le :
  forall (m : R) (k i j : nat),
    2 <= m ->
    (k < i)%nat ->
    (i < j)%nat ->
    ((m + 1) *
      ((m ^ i - m ^ k) * (m ^ i - m ^ k)) <=
     (m ^ j - m ^ k) * (m ^ j - m ^ k))%R.
Proof.
  intros m k i j Hm Hki Hij.
  assert (Hbase : 1 < m) by lra.
  assert (Hdi_pos : 0 <= m ^ i - m ^ k).
  { left. apply Rgt_minus. apply Rlt_pow; auto. }
  assert (Hdj_pos : 0 <= m ^ j - m ^ k).
  { left. apply Rgt_minus. apply Rlt_pow; auto. lia. }
  assert (Hscale : m * (m ^ i - m ^ k) <= m ^ j - m ^ k).
  {
    assert (Hpow1 : m ^ S i <= m ^ j).
    { apply Rle_pow; lra || lia. }
    assert (Hpow2 : m ^ k <= m ^ S k).
    { apply Rle_pow; lra || lia. }
    simpl in Hpow1, Hpow2.
    nra.
  }
  assert (Hcoeff : m + 1 <= m * m) by nra.
  assert (Hsq : (m * (m ^ i - m ^ k)) *
                (m * (m ^ i - m ^ k)) <=
                (m ^ j - m ^ k) * (m ^ j - m ^ k)).
  { apply Rmult_le_compat; nra. }
  replace (m * (m ^ i - m ^ k) * (m * (m ^ i - m ^ k)))%R with
    (m * m * ((m ^ i - m ^ k) * (m ^ i - m ^ k)))%R in Hsq by lra.
  assert (Hd: 0 <= ((m ^ i - m ^ k) * (m ^ i - m ^ k))%R) by nra.
  apply (Rmult_le_compat_r _ _ _ Hd) in Hcoeff.
  nra.
Qed.

Lemma gaussian_schedule_separation_sum_scaled_prefix_le :
  forall (m : R) (i j k : nat),
    2 <= m ->
    (i < j)%nat ->
    (k <= i)%nat ->
    ((m + 1) * gaussian_schedule_separation_sum m i k <=
      gaussian_schedule_separation_sum m j k)%R.
Proof.
  intros m i j k.
  revert m i j.
  induction k; intros.
  - simpl. nra.
  - simpl.
    assert (Hk_i : (k < i)%nat) by lia.
    specialize (IHk m i j H H0 ltac:(lia)).
    pose proof (gaussian_schedule_separation_term_scaled_le m k i j H Hk_i H0) as Hterm.
    nra.
Qed.

Lemma gaussian_schedule_separation_sum_scaled_le :
  forall (m : R) (i j : nat),
    2 <= m ->
    (i < j)%nat ->
    ((m + 1) * gaussian_schedule_separation_sum m i i <=
      gaussian_schedule_separation_sum m j j)%R.
Proof.
  intros.
  eapply Rle_trans.
  - apply gaussian_schedule_separation_sum_scaled_prefix_le; eauto; lia.
  - apply gaussian_schedule_separation_sum_le. lia.
Qed.

Lemma dot_schedule_axis_lower :
  forall {d : nat} (m : R) (a : vec d) i,
    2 <= m ->
    is_vec_leq 0 a ->
    dot a 1 = m ->
    m <= dot a (m * canon_e i + 1).
Proof.
  intros.
  rewrite dot_schedule_axis.
  pose proof (dot_canon_e_nonneg a i H0) as Hae.
  nra.
Qed.

Lemma dot_schedule_axis_upper :
  forall {d : nat} (m : R) (a : vec d) i,
    2 <= m ->
    is_vec_leq 0 a ->
    dot a 1 = m ->
    dot a (m * canon_e i + 1) <= m * (m + 1).
Proof.
  intros.
  rewrite dot_schedule_axis.
  pose proof (dot_canon_e_le_dot_1 a i H0) as Hae.
  rewrite H1 in Hae.
  nra.
Qed.

Lemma gaussian_schedule_later_covariance :
  forall {d : nat} (m : R) (a : vec d) (i j : nat),
    2 <= m ->
    is_vec_leq 0 a ->
    dot a 1 = m ->
    (i < j)%nat ->
    dot a (gaussian_schedule_sigma m i) <=
      dot a (gaussian_schedule_sigma m j).
Proof.
  intros d m a i j Hm Ha Hdot Hij.
  destruct j as [|j']; [lia|].
  destruct i as [|i'].
  - unfold gaussian_schedule_sigma.
    rewrite Hdot.
    rewrite gaussian_schedule_sigma_sum_dot.
    pose proof (gaussian_schedule_separation_sum_ge_1 m (S j') Hm ltac:(lia)) as Hsep.
    pose proof (dot_schedule_axis_lower m a (S j') Hm Ha Hdot) as Haxis.
    nra.
  - unfold gaussian_schedule_sigma.
    rewrite !gaussian_schedule_sigma_sum_dot.
    pose proof (dot_schedule_axis_upper m a (S i') Hm Ha Hdot) as Haxis_i.
    pose proof (dot_schedule_axis_lower m a (S j') Hm Ha Hdot) as Haxis_j.
    pose proof (gaussian_schedule_separation_sum_scaled_le m (S i') (S j') Hm ltac:(lia)) as Hsep.
    pose proof (gaussian_schedule_separation_sum_nonneg m (S i') (S i')) as Hsep_i.
    pose proof (gaussian_schedule_separation_sum_nonneg m (S j') (S j')) as Hsep_j.
    nra.
Qed.

Lemma gaussian_schedule_distance_sum_0 :
  forall {d : nat} (a : vec d) (m : R) (j : nat),
    dot a 1 = m ->
    gaussian_schedule_distance_sum_from a m j 0 j =
      (m * gaussian_schedule_separation_sum m j j)%R.
Proof.
  intros.
  rewrite gaussian_schedule_distance_sum_from_ext by assumption.
  rewrite gaussian_schedule_separation_sum_from_0.
  reflexivity.
Qed.

Lemma gaussian_schedule_sigma_dot_as_distance :
  forall {d : nat} (m : R) (a : vec d) (j : nat),
    dot a 1 = m ->
    (0 < j)%nat ->
    dot a (gaussian_schedule_sigma m j) =
      (gaussian_schedule_distance_sum_from a m j 0 j *
       (1 + dot a (canon_e j)))%R.
Proof.
  intros d m a j Hdot Hj.
  destruct j as [|j']; [lia|].
  unfold gaussian_schedule_sigma.
  rewrite gaussian_schedule_sigma_sum_dot.
  rewrite dot_schedule_axis.
  rewrite Hdot.
  rewrite gaussian_schedule_distance_sum_0 by assumption.
  ring.
Qed.

Lemma gaussian_schedule_distance_sum_positive :
  forall {d : nat} (a : vec d) (m : R) (j : nat),
    2 <= m ->
    dot a 1 = m ->
    (0 < j)%nat ->
    0 < gaussian_schedule_distance_sum_from a m j 0 j.
Proof.
  intros.
  rewrite gaussian_schedule_distance_sum_0 by assumption.
  pose proof (gaussian_schedule_separation_sum_ge_1 m j H H1) as Hsep.
  nra.
Qed.

Lemma gaussian_schedule_sigma_dot_positive :
  forall {d : nat} (m : R) (a : vec d) (j : nat),
    2 <= m ->
    is_vec_leq 0 a ->
    dot a 1 = m ->
    (0 < j)%nat ->
    0 < dot a (gaussian_schedule_sigma m j).
Proof.
  intros.
  rewrite gaussian_schedule_sigma_dot_as_distance by assumption.
  pose proof (gaussian_schedule_distance_sum_positive a m j H H1 H2) as HD.
  pose proof (dot_canon_e_nonneg a j H0) as Hae.
  nra.
Qed.

Lemma gaussian_schedule_distance_sum_sigma_ratio :
  forall {d : nat} (m : R) (a : vec d) (j : nat),
    2 <= m ->
    is_vec_leq 0 a ->
    dot a 1 = m ->
    (0 < j)%nat ->
    gaussian_schedule_distance_sum_from a m j 0 j /
      dot a (gaussian_schedule_sigma m j) =
      / (1 + dot a (canon_e j)).
Proof.
  intros.
  rewrite gaussian_schedule_sigma_dot_as_distance by assumption.
  pose proof (gaussian_schedule_distance_sum_positive a m j H H1 H2) as HD.
  pose proof (dot_canon_e_nonneg a j H0) as Hae.
  field.
  split; nra.
Qed.

Lemma gaussian_schedule_separation_term_le_sum :
  forall (m : R) (i j : nat),
    (i < j)%nat ->
    ((m ^ i - m ^ j) * (m ^ i - m ^ j) <=
      gaussian_schedule_separation_sum m j j)%R.
Proof.
  intros.
  pose proof (gaussian_schedule_separation_sum_nonneg m j i) as Hprev.
  pose proof (gaussian_schedule_separation_sum_le m j (S i) j ltac:(lia)) as Hle.
  simpl in Hle.
  replace ((m ^ i - m ^ j) * (m ^ i - m ^ j))%R
    with ((m ^ j - m ^ i) * (m ^ j - m ^ i))%R by lra.
  nra.
Qed.

Lemma gaussian_schedule_distance_term_le_sum :
  forall {d : nat} (a : vec d) (m : R) (i j : nat),
    2 <= m ->
    dot a 1 = m ->
    (i < j)%nat ->
    dot a
      (sqvec
        (gaussian_schedule_mu m i - gaussian_schedule_mu m j)) <=
      gaussian_schedule_distance_sum_from a m j 0 j.
Proof.
  intros.
  rewrite gaussian_schedule_mu_distance.
  rewrite H0.
  rewrite gaussian_schedule_distance_sum_0 by assumption.
  rewrite (Rmult_comm m).
  apply Rmult_le_compat_r.
  - lra.
  - apply gaussian_schedule_separation_term_le_sum. assumption.
Qed.

Lemma gaussian_schedule_pair_hinge_before :
  forall {d : nat} (m c : R) (a : vec d) (i j : nat),
    2 <= m ->
    1 <= c ->
    is_vec_leq 0 a ->
    dot a 1 = m ->
    (i < j)%nat ->
    gaussian_pair_hinge c a
      (gaussian_schedule_class m i)
      (gaussian_schedule_class m j) =
      (c -
       dot a
        (sqvec
          (gaussian_schedule_mu m i - gaussian_schedule_mu m j)%Vec) /
       dot a (gaussian_schedule_sigma m j))%R.
Proof.
  intros d m c a i j Hm Hc Ha Hdot Hij.
  rewrite gaussian_schedule_pair_hinge_later_covariance.
  2:{ apply gaussian_schedule_later_covariance; assumption. }
  unfold hinge.
  rewrite Rmax_right.
  - reflexivity.
  - assert (HDle :
      dot a
        (sqvec
          (gaussian_schedule_mu m i - gaussian_schedule_mu m j)) <=
      dot a (gaussian_schedule_sigma m j)).
    {
      eapply Rle_trans.
      - apply gaussian_schedule_distance_term_le_sum; eauto.
      - rewrite gaussian_schedule_sigma_dot_as_distance by (try assumption; lia).
        pose proof (gaussian_schedule_distance_sum_positive a m j Hm Hdot ltac:(lia)) as HDpos.
        pose proof (dot_canon_e_nonneg a j Ha) as Hae.
        nra.
    }
    assert (HSpos : 0 < dot a (gaussian_schedule_sigma m j)).
    { apply gaussian_schedule_sigma_dot_positive; try assumption; lia. }
    assert (Hratio :
      dot a
        (sqvec
          (gaussian_schedule_mu m i - gaussian_schedule_mu m j)) /
      dot a (gaussian_schedule_sigma m j) <= 1).
    {
      unfold Rdiv.
      replace 1%R with
        ((dot a (gaussian_schedule_sigma m j) *
         / dot a (gaussian_schedule_sigma m j))%R).
      2:{ field. lra. }
      apply Rmult_le_compat_r.
      - left. apply Rinv_0_lt_compat. exact HSpos.
      - exact HDle.
    }
    lra.
Qed.

Lemma hinge_to_gaussian_schedule_from_before :
  forall {d : nat} (m c : R) (a : vec d) (j start n : nat),
    2 <= m ->
    1 <= c ->
    is_vec_leq 0 a ->
    dot a 1 = m ->
    (start + n <= j)%nat ->
    hinge_to c a (to_list (gaussian_schedule_from m start n))
      (gaussian_schedule_class m j) =
      (c * INR n -
       gaussian_schedule_distance_sum_from a m j start n /
       dot a (gaussian_schedule_sigma m j))%R.
Proof.
  intros d m c a j start n.
  revert d m c a j start.
  induction n; intros.
  - simpl. lra.
  - simpl gaussian_schedule_from.
    rewrite to_list_cons. simpl hinge_to.
    rewrite gaussian_schedule_pair_hinge_before by (try assumption; lia).
    rewrite IHn by (try assumption; lia).
    rewrite S_INR.
    simpl.
    lra.
Qed.

Lemma hinge_to_gaussian_schedule_last :
  forall {d : nat} (m c : R) (a : vec d) (j : nat),
    2 <= m ->
    1 <= c ->
    is_vec_leq 0 a ->
    dot a 1 = m ->
    (0 < j)%nat ->
    hinge_to c a (to_list (gaussian_schedule m j))
      (gaussian_schedule_class m j) =
      (c * INR j - / (1 + dot a (canon_e j)))%R.
Proof.
  intros.
  unfold gaussian_schedule.
  rewrite hinge_to_gaussian_schedule_from_before by (try assumption; lia).
  rewrite gaussian_schedule_distance_sum_sigma_ratio by assumption.
  reflexivity.
Qed.

Lemma gaussian_schedule_hinge_form_prefix_m_ge_2 :
  forall {D : nat} (n : nat) (m c : R) (a : vec D),
    2 <= m ->
    1 <= c ->
    is_vec_leq 0 a ->
    dot a 1 = m ->
    hinge_form c a (to_list (gaussian_schedule m (S n))) =
      (c * INR n * (INR n + 1) / 2 -
       gaussian_schedule_hinge_correction a n)%R.
Proof.
  intros D n m c a.
  revert D m c a.
  induction n; intros.
  - simpl. lra.
  - rewrite gaussian_schedule_snoc.
    rewrite hinge_form_snoc.
    rewrite IHn by assumption.
    rewrite hinge_to_gaussian_schedule_last by (try assumption; lia).
    rewrite S_INR.
    simpl.
    nra.
Qed.

Lemma gaussian_schedule_hinge_form_m_ge_2 :
  forall (d : nat) (m c : R) (a : vec (S d)),
    2 <= m ->
    1 <= c ->
    is_vec_leq 0 a ->
    dot a 1 = m ->
    hinge_form c a (to_list (gaussian_schedule m (S d))) =
      (c * INR d * (INR d + 1) / 2 -
       gaussian_schedule_hinge_correction a d)%R.
Proof.
  intros.
  apply gaussian_schedule_hinge_form_prefix_m_ge_2; assumption.
Qed.


(* The three shifted Gaussians used as the second gadget.  Here
   [gaussian_schedule_separation_sum m d d] is
   [sum_{j=0}^{d-1} (m^d - m^j)^2]. *)
Definition second_gadget_gamma (d : nat) (m : R) : R :=
  (m + gaussian_schedule_separation_sum m d d)%R.

Definition second_gadget_u {d : nat} (m c : R) (s : vec d) : R :=
  (dot s 1%Vec + c + m ^ d)%R.

Definition second_gadget_c {d : nat} (s : vec d) : R :=
  (dot s 1%Vec / 2)%R.

Definition second_gadget_mu1 {d : nat} (m c : R) : vec d :=
  let gamma := second_gadget_gamma d m in
  (gamma * (3 * c + m ^ d)) * 1.

Definition second_gadget_mu2 {d : nat} (m c : R) (s : vec d) : vec d :=
  let gamma := second_gadget_gamma d m in
  gamma * (((3 * c + m ^ d) * 1) + m * sqrtvec s).

Definition second_gadget_mu3 {d : nat} (m c : R) : vec d :=
  let gamma := second_gadget_gamma d m in
  (gamma * (2 * c + m ^ d)) * 1.

Definition second_gadget_sigma1 {d : nat} (m : R) : vec d :=
  let gamma := second_gadget_gamma d m in
  (gamma * gamma) * 1.

Definition second_gadget_sigma2 {d : nat} (m : R) : vec d :=
  let gamma := second_gadget_gamma d m in
  (gamma * gamma * m) * 1.

Definition second_gadget_sigma3 {d : nat} (m : R) (s : vec d) : vec d :=
  let gamma := second_gadget_gamma d m in
  (gamma * gamma * m) * s.

Definition second_gadget_g1 {d : nat} (m c : R) : @gaussian d :=
  (second_gadget_mu1 m c, second_gadget_sigma1 m).

Definition second_gadget_g2 {d : nat} (m c : R) (s : vec d)
  : @gaussian d :=
  (second_gadget_mu2 m c s, second_gadget_sigma2 m).

Definition second_gadget_g3 {d : nat} (m c : R) (s : vec d)
  : @gaussian d :=
  (second_gadget_mu3 m c, second_gadget_sigma3 m s).

Definition second_gadget_instance {d : nat} (m c : R) (s : vec d)
  : Vector.t (@gaussian d) 3 :=
  [second_gadget_g1 m c; second_gadget_g2 m c s; second_gadget_g3 m c s].

Definition second_gadget_partition_instance {d : nat} (m : R) (s : vec d)
  : Vector.t (@gaussian d) 3 :=
  second_gadget_instance m (second_gadget_c s) s.

Lemma second_gadget_u_half_total :
  forall {d : nat} (m c : R) (s : vec d),
    c = dot s 1 / 2 ->
    second_gadget_u m c s = (3 * c + m ^ d)%R.
Proof.
  intros d m c s Hc.
  unfold second_gadget_u.
  nra.
Qed.

Lemma hinge_zero_mul_le :
  forall (c D S : R),
    0 < S -> hinge c D S = 0%R -> c * S <= D.
Proof.
  intros c D S HS Hzero.
  unfold hinge in Hzero.
  assert (Hle : c - D / S <= 0).
  {
    unfold Rmax in Hzero.
    destruct (Rle_dec 0 (c - D / S)); lra.
  }
  assert (Hratio : c <= D / S) by lra.
  unfold Rdiv in Hratio.
  apply (Rmult_le_compat_r _ _ _ (Rlt_le _ _ HS)) in Hratio.
  replace (D * / S * S)%R with D in Hratio by (field; lra).
  lra.
Qed.

Lemma hinge_zero_of_mul_le :
  forall (c D S : R),
    0 < S -> c * S <= D -> hinge c D S = 0%R.
Proof.
  intros c D S HS Hmul.
  unfold hinge.
  assert (Hratio : c <= D / S).
  {
    unfold Rdiv.
    replace c with (c * S * / S)%R by (field; lra).
    apply Rmult_le_compat_r.
    - left. apply Rinv_0_lt_compat. exact HS.
    - exact Hmul.
  }
  unfold Rmax.
  destruct (Rle_dec 0 (c - D / S)); lra.
Qed.

Lemma gaussian_pair_hinge_nonneg :
  forall {d : nat} (c : R) (a : vec d) (g1 g2 : @gaussian d),
    0 <= gaussian_pair_hinge c a g1 g2.
Proof.
  intros d c a g1 g2.
  unfold gaussian_pair_hinge.
  destruct (gaussian_pair_stats a (g1, g2)) as [D S].
  unfold hinge, Rmax.
  destruct (Rle_dec 0 (c - D / S)); lra.
Qed.

Lemma hinge_against_nonneg :
  forall {d : nat} (c : R) (a : vec d) (g : @gaussian d)
    (L : list (@gaussian d)),
    0 <= hinge_against c a g L.
Proof.
  induction L as [| h L IHL]; intros.
  - simpl. lra.
  - simpl.
    pose proof (gaussian_pair_hinge_nonneg c a g h) as Hh.
    lra.
Qed.

Lemma hinge_form_nonneg :
  forall {d : nat} (c : R) (a : vec d) (L : list (@gaussian d)),
    0 <= hinge_form c a L.
Proof.
  induction L as [| g L IHL]; intros.
  - simpl. lra.
  - simpl.
    pose proof (hinge_against_nonneg c a g L) as Hg.
    lra.
Qed.

Lemma Rmult_Rmax_le :
  forall (c x y D : R),
    0 <= c -> c * x <= D -> c * y <= D -> c * Rmax x y <= D.
Proof.
  intros c x y D Hc Hx Hy.
  unfold Rmax.
  destruct (Rle_dec x y); lra.
Qed.

Lemma Rmax_lt_if_l :
  forall x y : R, 0 < x -> 0 < Rmax x y.
Proof.
  intros x y Hx.
  unfold Rmax.
  destruct (Rle_dec x y); lra.
Qed.

Lemma Rmax_lt_if_r :
  forall x y : R, 0 < y -> 0 < Rmax x y.
Proof.
  intros x y Hy.
  unfold Rmax.
  destruct (Rle_dec x y); lra.
Qed.

Lemma second_gadget_gamma_pos :
  forall (n : nat) (m : R),
    0 < m -> 0 < second_gadget_gamma n m.
Proof.
  intros n m Hm.
  unfold second_gadget_gamma.
  pose proof (gaussian_schedule_separation_sum_nonneg m n n).
  lra.
Qed.

Lemma shifted_12_distance :
  forall {n : nat} (gamma A m : R) (a s : vec n),
    dot a (sqvec ((gamma * A) * 1 -
      gamma * (A * 1 + m * sqrtvec s))) =
    (gamma * gamma * m * m * dot a (sqvec (sqrtvec s)))%R.
Proof.
  induction n; intros gamma A m a s.
  - rewrite (eta0 a), (eta0 s). simpl. ring.
  - rewrite (eta s).
    rewrite (dot_step a (sqvec (sqrtvec _))).
    replace (tl (sqvec (sqrtvec (hd s :: tl s)))) with (sqvec (sqrtvec (tl s))) by auto.
    replace (hd (sqvec (sqrtvec (hd s :: tl s)))) with (sqrt (hd s) * sqrt (hd s))%R by auto.
    rewrite Rmult_plus_distr_l.
    rewrite <- (IHn _ A).
    replace (sqrtvec (hd s :: tl s)) with (sqrt (hd s) :: sqrtvec (tl s)) by auto.
    replace (gamma * (A * 1 + m * (sqrt (hd s) :: sqrtvec (tl s)))) with
      ((gamma * (A + m * sqrt (hd s)))%R :: gamma * (A * 1 + m * sqrtvec (tl s)) ).
    2:{  replace (m * (sqrt (hd s) :: sqrtvec (tl s))) with ((m * (sqrt (hd s)))%R :: (m  * sqrtvec (tl s))) by auto.
        cbn. rewrite Rmult_1_r. auto.
      }
    replace (gamma * A * 1 - ((gamma * (A + m * sqrt (hd s)))%R :: gamma * (A * 1 + m * sqrtvec (tl s)))) with
      ((gamma * A - gamma * (A + m * sqrt (hd s)))%R :: (gamma * A * 1 - gamma * (A * 1 + m * sqrtvec (tl s)))).
    2:{ cbn. rewrite Rmult_1_r. auto. }
    rewrite dot_step. simpl.
    unfold sqvec. lra.
Qed.

Lemma shifted_const_distance :
  forall {n : nat} (gamma A B : R) (a : vec n),
    dot a (sqvec ((gamma * A) * 1 - (gamma * B) * 1)) =
    (gamma * gamma * (A - B) * (A - B) * dot a 1%Vec)%R.
Proof.
  induction n; intros gamma A B a.
  - rewrite (eta0 a). simpl. ring.
  - rewrite dot_step.
    replace (tl (@sqvec (S n) (gamma * A * 1 - gamma * B * 1))) with
      (@sqvec n ( (gamma * A * 1 - gamma * B * 1))) by auto.
    rewrite (IHn gamma A B (tl a)).
    rewrite (dot_step a).
    cbn. lra.
Qed.

Lemma shifted_23_distance :
  forall {n : nat} (gamma A B m : R) (a s : vec n),
    dot a (sqvec (gamma * (A * 1 + m * sqrtvec s) -
      (gamma * B) * 1)) =
    (gamma * gamma *
      dot a (sqvec ((A - B) * 1 + m * sqrtvec s))%Vec)%R.
Proof.
  induction n; intros gamma A B m a s.
  - rewrite (eta0 a), (eta0 s). simpl. ring.
  - rewrite 2 dot_step.
    specialize (IHn gamma A B m (tl a) (tl s)).
    rewrite sqvec_tl.
    replace (tl (gamma * (A * 1 + m * sqrtvec s) - gamma * B * 1)%Vec)
      with ((gamma * (A * 1 + m * sqrtvec (tl s)) - gamma * B * 1)%Vec).
    2:{ rewrite (eta s). trivial. }
    rewrite sqvec_hd. rewrite IHn.
    replace (hd (gamma * (A * 1 + m * sqrtvec s) - gamma * B * 1)) with
      ((gamma * (A + m * (sqrt (hd s) )) - gamma * B)%R).
    2:{ rewrite (eta s). simpl. rewrite 2 Rmult_1_r. trivial. }
    replace (hd (sqvec ((A - B) * 1 + m * sqrtvec s)%Vec))
      with ( ((A - B) * 1 + m * sqrt (hd s)) * ((A - B) * 1 + m * sqrt (hd s)) )%R.
    2:{ rewrite (eta s). trivial. }
    rewrite (Rmult_plus_distr_l (gamma * gamma)).
    f_equal.
    + lra.
    + rewrite (eta s). trivial.
Qed.

Lemma second_gadget_sigma1_dot :
  forall {n : nat} (m : R) (a : vec n),
    dot a (second_gadget_sigma1 m) =
    (second_gadget_gamma n m * second_gadget_gamma n m * dot a 1%Vec)%R.
Proof.
  intros n m a.
  unfold second_gadget_sigma1.
  cbn.
  rewrite dot_mult_dist_r.
  reflexivity.
Qed.

Lemma second_gadget_sigma2_dot :
  forall {n : nat} (m : R) (a : vec n),
    dot a (second_gadget_sigma2 m) =
    (second_gadget_gamma n m * second_gadget_gamma n m * m * dot a 1%Vec)%R.
Proof.
  intros n m a.
  unfold second_gadget_sigma2.
  cbn.
  rewrite dot_mult_dist_r.
  reflexivity.
Qed.

Lemma second_gadget_sigma3_dot :
  forall {n : nat} (m : R) (a s : vec n),
    dot a (second_gadget_sigma3 m s) =
    (second_gadget_gamma n m * second_gadget_gamma n m * m * dot a s)%R.
Proof.
  intros n m a s.
  unfold second_gadget_sigma3.
  cbn.
  rewrite dot_mult_dist_r.
  reflexivity.
Qed.

Lemma second_gadget_12_distance :
  forall {n : nat} (m c : R) (a s : vec n),
    dot a (sqvec (second_gadget_mu1 m c - second_gadget_mu2 m c s)) =
    (second_gadget_gamma n m * second_gadget_gamma n m *
      m * m * dot a (sqvec (sqrtvec s)))%R.
Proof.
  intros n m c a s.
  unfold second_gadget_mu1, second_gadget_mu2.
  cbn.
  apply shifted_12_distance.
Qed.

Lemma second_gadget_13_distance :
  forall {n : nat} (m c : R) (a : vec n),
    dot a (sqvec (second_gadget_mu1 m c - second_gadget_mu3 m c)) =
    (second_gadget_gamma n m * second_gadget_gamma n m *
      c * c * dot a 1%Vec)%R.
Proof.
  intros n m c a.
  unfold second_gadget_mu1, second_gadget_mu3.
  cbn.
  rewrite shifted_const_distance.
  ring.
Qed.

Lemma second_gadget_23_distance :
  forall {n : nat} (m c : R) (a s : vec n),
    dot a (sqvec (second_gadget_mu2 m c s - second_gadget_mu3 m c)) =
    (second_gadget_gamma n m * second_gadget_gamma n m *
      dot a (sqvec (c * 1 + m * sqrtvec s)%Vec))%R.
Proof.
  intros n m c a s.
  unfold second_gadget_mu2, second_gadget_mu3.
  cbn.
  rewrite shifted_23_distance.
  replace (3 * c + m ^ n - (2 * c + m ^ n))%R with c by ring.
  reflexivity.
Qed.

Lemma second_gadget_gamma_ge_1 :
  forall (n : nat) (m : R),
    1 <= m -> 1 <= second_gadget_gamma n m.
Proof.
  intros n m Hm.
  unfold second_gadget_gamma.
  pose proof (gaussian_schedule_separation_sum_nonneg m n n).
  lra.
Qed.

Lemma pow_le_mono_nat :
  forall (m : R) (i j : nat),
    1 <= m -> (i <= j)%nat -> m ^ i <= m ^ j.
Proof.
  intros.
  apply Rle_pow; lra || lia.
Qed.

Lemma dot_box_le_dot_1 :
  forall {n : nat} (a s : vec n),
    box_constraints a ->
    is_vec_leq 0 s ->
    dot a s <= dot s 1%Vec.
Proof.
  intros n a s [_ Ha_le_1] Hs.
  rewrite dot_comm.
  apply dot_vec_noneg; assumption.
Qed.

Lemma const_schedule_distance :
  forall {n : nat} (x y : R) (a : vec n),
    dot a (sqvec (x * 1 - y * 1)) =
      ((x - y) * (x - y) * dot a 1%Vec)%R.
Proof.
  induction n; intros x y a.
  - rewrite (eta0 a). simpl. ring.
  - rewrite dot_step.
    replace (tl (@sqvec (S n) (x * 1 - y * 1))) with
      (@sqvec n (x * 1 - y * 1)) by auto.
    rewrite IHn.
    rewrite (dot_step a).
    cbn. lra.
Qed.

Lemma shifted_schedule_distance_lower :
  forall {n : nat} (gamma A m q : R) (a s : vec n),
    0 <= gamma ->
    0 <= m ->
    0 <= gamma * A - q ->
    is_vec_leq 0 a ->
    is_vec_leq 0 s ->
    ((gamma * A - q) * (gamma * A - q) * dot a 1%Vec <=
      dot a (sqvec (gamma * (A * 1 + m * sqrtvec s) - q * 1)%Vec))%R.
Proof.
  induction n; intros gamma A m q a s Hgamma Hm Hgap Ha Hs.
  - rewrite (eta0 a), (eta0 s). simpl. lra.
  - assert (Ha_hd : 0 <= hd a).
    { rewrite (eta a) in Ha. inversion Ha; subst; inv_cleanup; assumption. }
    assert (Ha_tl : is_vec_leq 0 (tl a)).
    { rewrite (eta a) in Ha. inversion Ha; subst; inv_cleanup; assumption. }
    assert (Hs_hd : 0 <= hd s).
    { rewrite (eta s) in Hs. inversion Hs; subst; inv_cleanup; assumption. }
    assert (Hs_tl : is_vec_leq 0 (tl s)).
    { rewrite (eta s) in Hs. inversion Hs; subst; inv_cleanup; assumption. }
    specialize (IHn gamma A m q (tl a) (tl s)
      Hgamma Hm Hgap Ha_tl Hs_tl).
    rewrite (eta a), (eta s).
    rewrite !dot_step.
    assert (Hsqrt : 0 <= sqrt (hd s)).
    { apply sqrt_positivity. exact Hs_hd. }
    replace (hd (sqvec (gamma * (A * 1 + m * sqrtvec (hd s :: tl s)) - q * 1)))%Vec
      with ((gamma * (A + m * sqrt (hd s)) - q) * (gamma * (A + m * sqrt (hd s)) - q))%R.
    2:{ simpl. rewrite ! Rmult_1_r. trivial.  }
    replace (tl (sqvec (gamma * (A * 1 + m * sqrtvec (hd s :: tl s)) - q * 1)))%Vec with
      ((sqvec (gamma * (A * 1 + m * sqrtvec (tl s)) - q * 1))) by trivial.
    simpl.
    rewrite Rmult_plus_distr_l.
    apply Rplus_le_compat; auto.
    rewrite (Rmult_comm _ (hd a * 1)%R).
    rewrite Rmult_1_r.
    apply Rmult_le_compat_l; auto.
    replace (gamma * (A + m * sqrt (hd s)) - q)%R with
      ((gamma * A - q + gamma * m * sqrt (hd s)))%R by lra.
    rewrite Rmult_plus_distr_l.
    rewrite Rmult_plus_distr_r.
    rewrite <- Rplus_0_r at 1.
    rewrite Rplus_assoc.
    apply Rplus_le_compat_l.
    apply Rplus_le_le_0_compat.
    + repeat (apply Rmult_le_pos; auto).
    + apply Rmult_le_pos; [|repeat (apply Rmult_le_pos; auto)].
      apply Rplus_le_le_0_compat; auto.
      repeat (apply Rmult_le_pos; auto).
Qed.

Lemma gaussian_schedule_sigma_dot_le_second_gadget_gamma :
  forall {n : nat} (m : R) (a : vec n) (j : nat),
    2 <= m ->
    is_vec_leq 0 a ->
    dot a 1 = m ->
    (j <= n)%nat ->
    dot a (gaussian_schedule_sigma m j) <=
      (second_gadget_gamma n m * second_gadget_gamma n m * m)%R.
Proof.
  intros n m a j Hm Ha Hdot Hj.
  set (gamma := second_gadget_gamma n m).
  assert (Hgamma_ge_1 : 1 <= gamma).
  { unfold gamma. apply second_gadget_gamma_ge_1. lra. }
  assert (Hsep_n_nonneg : 0 <= gaussian_schedule_separation_sum m n n).
  { apply gaussian_schedule_separation_sum_nonneg. }
  destruct j as [|j'].
  - unfold gaussian_schedule_sigma.
    rewrite Hdot.
    rewrite <- (Rmult_1_l) at 1.
    apply Rmult_le_compat_r; [lra|].
    rewrite <- (Rmult_1_l 1).
    nra.
  - unfold gaussian_schedule_sigma.
    rewrite gaussian_schedule_sigma_sum_dot.
    assert (Haxis :
      dot a (m * canon_e (S j') + 1)%Vec <= m * (m + 1)).
    { apply dot_schedule_axis_upper; assumption. }
    assert (Hsep_le :
      gaussian_schedule_separation_sum m (S j') (S j') <=
      gaussian_schedule_separation_sum m n n).
    {
      destruct (Nat.eq_dec (S j') n) as [Heq | Hneq].
      - subst. lra.
      - assert (Hlt : (S j' < n)%nat) by lia.
        pose proof
          (gaussian_schedule_separation_sum_scaled_le m (S j') n Hm Hlt)
          as Hscaled.
        pose proof
          (gaussian_schedule_separation_sum_nonneg m (S j') (S j'))
          as Hsep_j_nonneg.
        nra.
    }
    assert (Hgamma_sq :
      gaussian_schedule_separation_sum m n n * (m + 1) <= gamma * gamma).
    {
      unfold gamma, second_gadget_gamma.
      nra.
    }
    assert (F1: 0 <= dot a (m * canon_e (S j') + 1)).
    { rewrite dot_dist.
      apply Rplus_le_le_0_compat.
      - rewrite dot_mult_dist_r.
        apply Rmult_le_pos; [lra|apply dot_canon_e_nonneg].
        auto.
      - apply non_neg_dot_1.
        auto.
    }

    assert (F2: 0 <= gaussian_schedule_separation_sum m (S j') (S j')).
    { apply gaussian_schedule_separation_sum_nonneg. }
    assert (F:= Rmult_le_compat _ _ _ _ F2 F1 Hsep_le Haxis).
    nra.
Qed.

Lemma gaussian_schedule_sigma_dot_positive_all :
  forall {n : nat} (m : R) (a : vec n) (j : nat),
    2 <= m ->
    is_vec_leq 0 a ->
    dot a 1 = m ->
    0 < dot a (gaussian_schedule_sigma m j).
Proof.
  intros n m a j Hm Ha Hdot.
  destruct j as [|j'].
  - unfold gaussian_schedule_sigma.
    rewrite Hdot.
    lra.
  - apply gaussian_schedule_sigma_dot_positive; try assumption; lia.
Qed.

Lemma second_gadget_schedule_gap_3c :
  forall (n j : nat) (m c : R),
    2 <= m ->
    1 <= c ->
    (j <= n)%nat ->
    second_gadget_gamma n m * (3 * c + m ^ n) - m ^ j >=
      second_gadget_gamma n m * (3 * c).
Proof.
  intros n j m c Hm Hc Hj.
  assert (Hgamma_ge_1 : 1 <= second_gadget_gamma n m).
  { apply second_gadget_gamma_ge_1. lra. }
  assert (Hpow_le : m ^ j <= m ^ n).
  { apply pow_le_mono_nat; lra || lia. }
  assert (Hpow_j_nonneg : 0 <= m ^ j).
  { pose proof (pow_R1_Rle m j ltac:(lra)). lra. }
  nra.
Qed.

Lemma second_gadget_schedule_gap_2c :
  forall (n j : nat) (m c : R),
    2 <= m ->
    1 <= c ->
    (j <= n)%nat ->
    second_gadget_gamma n m * (2 * c + m ^ n) - m ^ j >=
      second_gadget_gamma n m * (2 * c).
Proof.
  intros n j m c Hm Hc Hj.
  assert (Hgamma_ge_1 : 1 <= second_gadget_gamma n m).
  { apply second_gadget_gamma_ge_1. lra. }
  assert (Hpow_le : m ^ j <= m ^ n).
  { apply pow_le_mono_nat; lra || lia. }
  assert (Hpow_j_nonneg : 0 <= m ^ j).
  { pose proof (pow_R1_Rle m j ltac:(lra)). lra. }
  nra.
Qed.

Lemma second_gadget_schedule_gap_c_plus_m :
  forall (n j : nat) (m c : R),
    (0 < n)%nat ->
    2 <= m ->
    1 <= c ->
    (j < n)%nat ->
    second_gadget_gamma n m * (3 * c + m ^ n) - m ^ j >=
      second_gadget_gamma n m * (c + m).
Proof.
  intros n j m c Hn Hm Hc Hj.
  assert (Hgamma_ge_1 : 1 <= second_gadget_gamma n m).
  { apply second_gadget_gamma_ge_1. lra. }
  assert (Hpow_j_nonneg : 0 <= m ^ j).
  { pose proof (pow_R1_Rle m j ltac:(lra)). lra. }
  assert (Htail : m - 1 <= m ^ n - m ^ j).
  {
    destruct n as [|n']; [lia|].
    assert (Hj' : (j <= n')%nat) by lia.
    assert (Hpow_j_le : m ^ j <= m ^ n').
    { apply pow_le_mono_nat; lra || lia. }
    assert (Hpow_n'_ge_1 : 1 <= m ^ n').
    { apply pow_R1_Rle. lra. }
    simpl.
    assert (Hstep : m - 1 <= m * m ^ n' - m ^ n').
    {
      replace (m * m ^ n' - m ^ n')%R with
        (m ^ n' * (m - 1))%R by ring.
      nra.
    }
    nra.
  }
  assert (Hscaled_tail :
    second_gadget_gamma n m * (m - 1) <=
    second_gadget_gamma n m * m ^ n - m ^ j).
  {
    assert (second_gadget_gamma n m * (m ^ n - m ^ j) <=
      second_gadget_gamma n m * m ^ n - m ^ j).
    {
      nra.
    }
    nra.
  }
  nra.
Qed.

Lemma square_le_of_nonneg_le :
  forall x y : R,
    0 <= x -> x <= y -> x * x <= y * y.
Proof.
  intros x y Hx Hxy.
  assert (Hy : 0 <= y) by lra.
  apply Rmult_le_compat; lra.
Qed.

Lemma gap_square_ge_gamma_xy :
  forall gamma x y scale gap : R,
    0 <= gamma ->
    0 <= x ->
    0 <= y ->
    x <= scale ->
    y <= scale ->
    gamma * scale <= gap ->
    gamma * gamma * x * y <= gap * gap.
Proof.
  intros gamma x y scale gap Hgamma Hx Hy Hx_scale Hy_scale Hgap.
  eapply Rle_trans with
    (r2 := ((gamma * gamma) * (scale * scale))%R).
  - replace (gamma * gamma * x * y)%R with
      ((gamma * gamma) * (x * y))%R by ring.
    apply Rmult_le_compat_l.
    + apply Rmult_le_pos; assumption.
    + apply Rmult_le_compat; lra.
  - replace ((gamma * gamma) * (scale * scale))%R with
      ((gamma * scale) * (gamma * scale))%R by ring.
    apply square_le_of_nonneg_le.
    + apply Rmult_le_pos; lra.
    + exact Hgap.
Qed.

Lemma second_gadget_schedule_pair_hinge_zero_1 :
  forall {n : nat} (m c : R) (a s : vec n) (j : nat),
    2 <= m ->
    1 <= c ->
    is_vec_leq 0 a ->
    dot a 1 = m ->
    (j <= n)%nat ->
    gaussian_pair_hinge c a
      (second_gadget_g1 m c) (gaussian_schedule_class m j) = 0%R.
Proof.
  intros n m c a s j Hm Hc Ha Hdot Hj.
  set (gamma := second_gadget_gamma n m).
  set (A := (3 * c + m ^ n)%R).
  assert (Hgamma_pos : 0 < gamma).
  { unfold gamma. apply second_gadget_gamma_pos. lra. }
  assert (Hgap : gamma * A - m ^ j >= gamma * (3 * c)).
  { unfold gamma, A. apply second_gadget_schedule_gap_3c; assumption. }
  unfold gaussian_pair_hinge, gaussian_pair_stats,
    second_gadget_g1, gaussian_schedule_class.
  simpl.
  apply hinge_zero_of_mul_le.
  - apply Rmax_lt_if_l.
    rewrite second_gadget_sigma1_dot.
    rewrite Hdot.
    fold gamma.
    apply Rmult_lt_0_compat.
    + apply Rmult_lt_0_compat; lra.
    + lra.
  - apply Rmult_Rmax_le; [lra| |].
    + rewrite second_gadget_sigma1_dot.
      unfold second_gadget_mu1, gaussian_schedule_mu.
      fold gamma A.
      rewrite const_schedule_distance.
      rewrite Hdot.

      eapply Rle_trans with (r2 := (gamma * gamma * c * c * m)%R).
      * replace (gamma * gamma * c * c * m)%R with
          ((c * c) * (gamma * gamma * m))%R by ring.
        apply Rmult_le_compat_r.
        -- apply Rmult_le_pos.
           ++ apply Rmult_le_pos; lra.
           ++ lra.
        -- replace c with (1 * c)%R at 1 by ring.
           apply Rmult_le_compat_r; lra.
      * replace (gamma * gamma * c * c * m)%R with
          ((gamma * gamma * c * c) * m)%R by ring.
        replace ((gamma * A - m ^ j) * (gamma * A - m ^ j) * m)%R with
          (((gamma * A - m ^ j) * (gamma * A - m ^ j)) * m)%R by ring.
        apply Rmult_le_compat_r; [lra |].
        replace (gamma * gamma * c * c)%R with
          ((gamma * c) * (gamma * c))%R by ring.
        assert (Hgc_nonneg : 0 <= gamma * c).
        { apply Rmult_le_pos; lra. }
        assert (Hgc_le_3gc : gamma * c <= gamma * (3 * c)).
        {
          replace (gamma * (3 * c))%R with
            (3 * (gamma * c))%R by ring.
          lra.
        }
        assert (Hgc_le_gap : gamma * c <= gamma * A - m ^ j) by lra.
        assert (Hgap_nonneg : 0 <= gamma * A - m ^ j) by lra.
        apply Rmult_le_compat; lra.
    + pose proof
        (gaussian_schedule_sigma_dot_le_second_gadget_gamma m a j
          Hm Ha Hdot ltac:(lia))
        as Hsched.
      unfold second_gadget_mu1, gaussian_schedule_mu.
      fold gamma A.
      rewrite const_schedule_distance.
      rewrite Hdot.
      fold gamma in Hsched.
      eapply Rle_trans with (r2 := (c * (gamma * gamma * m))%R).
      * apply Rmult_le_compat_l; [lra|exact Hsched].
      * replace (c * (gamma * gamma * m))%R with
          ((gamma * gamma * c) * m)%R by ring.
        replace ((gamma * A - m ^ j) * (gamma * A - m ^ j) * m)%R with
          (((gamma * A - m ^ j) * (gamma * A - m ^ j)) * m)%R by ring.
        apply Rmult_le_compat_r; [lra|].
        eapply Rle_trans with (r2 := (gamma * gamma * c * c)%R).
        -- replace (gamma * gamma * c)%R with
             ((gamma * gamma) * c)%R by ring.
           replace (gamma * gamma * c * c)%R with
             ((gamma * gamma) * (c * c))%R by ring.
           apply Rmult_le_compat_l.
           ++ apply Rmult_le_pos; lra.
           ++ replace c with (1 * c)%R at 1 by ring.
              apply Rmult_le_compat_r; lra.
        -- replace (gamma * gamma * c * c)%R with
             ((gamma * c) * (gamma * c))%R by ring.
           assert (Hgc_nonneg : 0 <= gamma * c).
           { apply Rmult_le_pos; lra. }
           assert (Hgc_le_3gc : gamma * c <= gamma * (3 * c)).
           {
             replace (gamma * (3 * c))%R with
               (3 * (gamma * c))%R by ring.
             lra.
           }
           assert (Hgc_le_gap : gamma * c <= gamma * A - m ^ j) by lra.
           assert (Hgap_nonneg : 0 <= gamma * A - m ^ j) by lra.
           apply Rmult_le_compat; lra.
Qed.

Lemma second_gadget_schedule_pair_hinge_zero_2 :
  forall {n : nat} (m c : R) (a s : vec n) (j : nat),
    (0 < n)%nat ->
    2 <= m ->
    1 <= c ->
    is_vec_leq 0 a ->
    is_vec_leq 0 s ->
    dot a 1 = m ->
    (j < n)%nat ->
    gaussian_pair_hinge c a
      (second_gadget_g2 m c s) (gaussian_schedule_class m j) = 0%R.
Proof.
  intros n m c a s j Hn Hm Hc Ha Hs Hdot Hj.
  set (gamma := second_gadget_gamma n m).
  set (A := (3 * c + m ^ n)%R).
  assert (Hgamma_pos : 0 < gamma).
  { unfold gamma. apply second_gadget_gamma_pos. lra. }
  assert (Hgap : gamma * A - m ^ j >= gamma * (c + m)).
  { unfold gamma, A. apply second_gadget_schedule_gap_c_plus_m; assumption. }
  assert (Hgap_nonneg : 0 <= gamma * A - m ^ j).
  {
    assert (0 <= gamma * (c + m)).
    { apply Rmult_le_pos; lra. }
    lra.
  }
  unfold gaussian_pair_hinge, gaussian_pair_stats,
    second_gadget_g2, gaussian_schedule_class.
  simpl.
  apply hinge_zero_of_mul_le.
  - apply Rmax_lt_if_l.
    rewrite second_gadget_sigma2_dot.
    rewrite Hdot.
    fold gamma.
    apply Rmult_lt_0_compat; [|lra].
    apply Rmult_lt_0_compat; [|lra].
    apply Rmult_lt_0_compat; lra.
  - apply Rmult_Rmax_le; [lra| |].
    + rewrite second_gadget_sigma2_dot.
      rewrite Hdot.
      unfold second_gadget_mu2, gaussian_schedule_mu.
      fold gamma A.
      eapply Rle_trans.
      2:{
        apply shifted_schedule_distance_lower; try assumption; lra.
      }
      fold gamma.
      rewrite Hdot.
      replace (c * (gamma * gamma * m * m))%R with
        ((gamma * gamma * c * m) * m)%R by ring.
      replace ((gamma * A - m ^ j) * (gamma * A - m ^ j) * m)%R with
        (((gamma * A - m ^ j) * (gamma * A - m ^ j)) * m)%R by ring.
      apply Rmult_le_compat_r; [lra|].
      apply (gap_square_ge_gamma_xy gamma c m (c + m)); lra.
    + pose proof
        (gaussian_schedule_sigma_dot_le_second_gadget_gamma m a j
          Hm Ha Hdot ltac:(lia))
        as Hsched.
      unfold second_gadget_mu2, gaussian_schedule_mu.
      fold gamma A.
      eapply Rle_trans.
      2:{
        apply shifted_schedule_distance_lower; try assumption; lra.
      }
      fold gamma in Hsched.
      rewrite Hdot.
      eapply Rle_trans with (r2 := (c * (gamma * gamma * m))%R).
      * apply Rmult_le_compat_l; [lra|exact Hsched].
      * replace (c * (gamma * gamma * m))%R with
          ((gamma * gamma * c) * m)%R by ring.
        replace ((gamma * A - m ^ j) * (gamma * A - m ^ j) * m)%R with
          (((gamma * A - m ^ j) * (gamma * A - m ^ j)) * m)%R by ring.
        apply Rmult_le_compat_r; [lra|].
        replace (gamma * gamma * c)%R with
          (gamma * gamma * c * 1)%R by ring.
        apply (gap_square_ge_gamma_xy gamma c 1 (c + m)); lra.
Qed.

Lemma second_gadget_schedule_pair_hinge_zero_3 :
  forall {n : nat} (m c : R) (a s : vec n) (j : nat),
    2 <= m ->
    1 <= c ->
    box_constraints a ->
    is_vec_leq 0 s ->
    dot a 1 = m ->
    dot s 1 = (2 * c)%R ->
    (j <= n)%nat ->
    gaussian_pair_hinge c a
      (second_gadget_g3 m c s) (gaussian_schedule_class m j) = 0%R.
Proof.
  intros n m c a s j Hm Hc Hbox Hs Hdot Hstotal Hj.
  destruct Hbox as [Ha Ha_le_1].
  set (gamma := second_gadget_gamma n m).
  set (B := (2 * c + m ^ n)%R).
  assert (Hgamma_pos : 0 < gamma).
  { unfold gamma. apply second_gadget_gamma_pos. lra. }
  assert (Hgap : gamma * B - m ^ j >= gamma * (2 * c)).
  { unfold gamma, B. apply second_gadget_schedule_gap_2c; assumption. }
  assert (Has_bound : dot a s <= 2 * c).
  {
    rewrite <- Hstotal.
    apply dot_box_le_dot_1; auto.
    split; assumption.
  }
  unfold gaussian_pair_hinge, gaussian_pair_stats,
    second_gadget_g3, gaussian_schedule_class.
  simpl.
  apply hinge_zero_of_mul_le.
  - apply Rmax_lt_if_r.
    apply gaussian_schedule_sigma_dot_positive_all; assumption.
  - apply Rmult_Rmax_le; [lra| |].
    + rewrite second_gadget_sigma3_dot.
      unfold second_gadget_mu3, gaussian_schedule_mu.
      fold gamma B.
      rewrite const_schedule_distance.
      rewrite Hdot.
      fold gamma.
      assert (Hdotas_nonneg : 0 <= dot a s).
      { apply dot_vec_noneg_0; assumption. }
      replace (c * (gamma * gamma * m * dot a s))%R with
        ((gamma * gamma * c * dot a s) * m)%R by ring.
      replace ((gamma * B - m ^ j) * (gamma * B - m ^ j) * m)%R with
        (((gamma * B - m ^ j) * (gamma * B - m ^ j)) * m)%R by ring.
      apply Rmult_le_compat_r; [lra|].
      apply (gap_square_ge_gamma_xy gamma c (dot a s) (2 * c)); lra.
    + pose proof
        (gaussian_schedule_sigma_dot_le_second_gadget_gamma m a j Hm Ha Hdot Hj)
        as Hsched.
      unfold second_gadget_mu3, gaussian_schedule_mu.
      fold gamma B.
      rewrite const_schedule_distance.
      rewrite Hdot.
      fold gamma in Hsched.
      eapply Rle_trans with (r2 := (c * (gamma * gamma * m))%R).
      * apply Rmult_le_compat_l; [lra|exact Hsched].
      * replace (c * (gamma * gamma * m))%R with
          ((gamma * gamma * c) * m)%R by ring.
        replace ((gamma * B - m ^ j) * (gamma * B - m ^ j) * m)%R with
          (((gamma * B - m ^ j) * (gamma * B - m ^ j)) * m)%R by ring.
        apply Rmult_le_compat_r; [lra|].
        replace (gamma * gamma * c)%R with
          (gamma * gamma * c * 1)%R by ring.
        apply (gap_square_ge_gamma_xy gamma c 1 (2 * c)); lra.
Qed.

Lemma second_gadget_schedule_hinge_against_zero_1 :
  forall {n : nat} (k : nat) (m c : R) (a s : vec n),
    2 <= m ->
    1 <= c ->
    is_vec_leq 0 a ->
    dot a 1 = m ->
    (k <= S n)%nat ->
    hinge_against c a (second_gadget_g1 m c)
      (to_list (gaussian_schedule m k)) = 0%R.
Proof.
  induction k; intros.
  - simpl. reflexivity.
  - rewrite gaussian_schedule_snoc.
    rewrite hinge_against_snoc.
    rewrite IHk by (try assumption; lia).
    rewrite second_gadget_schedule_pair_hinge_zero_1 by (try assumption; lia).
    lra.
Qed.

Lemma second_gadget_schedule_hinge_against_zero_2 :
  forall {n : nat} (k : nat) (m c : R) (a s : vec n),
    (0 < n)%nat ->
    2 <= m ->
    1 <= c ->
    is_vec_leq 0 a ->
    is_vec_leq 0 s ->
    dot a 1 = m ->
    (k <= n)%nat ->
    hinge_against c a (second_gadget_g2 m c s)
      (to_list (gaussian_schedule m k)) = 0%R.
Proof.
  induction k; intros.
  - simpl. reflexivity.
  - rewrite gaussian_schedule_snoc.
    rewrite hinge_against_snoc.
    rewrite IHk by (try assumption; lia).
    rewrite second_gadget_schedule_pair_hinge_zero_2 by (try assumption; lia).
    lra.
Qed.

Lemma second_gadget_schedule_hinge_against_zero_3 :
  forall {n : nat} (k : nat) (m c : R) (a s : vec n),
    2 <= m ->
    1 <= c ->
    box_constraints a ->
    is_vec_leq 0 s ->
    dot a 1 = m ->
    dot s 1 = (2 * c)%R ->
    (k <= S n)%nat ->
    hinge_against c a (second_gadget_g3 m c s)
      (to_list (gaussian_schedule m k)) = 0%R.
Proof.
  induction k; intros.
  - simpl. reflexivity.
  - rewrite gaussian_schedule_snoc.
    rewrite hinge_against_snoc.
    rewrite IHk by (try assumption; lia).
    rewrite second_gadget_schedule_pair_hinge_zero_3 by (try assumption; lia).
    lra.
Qed.

Theorem second_gadget_schedule_hinge_form_app :
  forall {n : nat} (m c : R) (a s : vec n),
    (0 < n)%nat ->
    2 <= m ->
    1 <= c ->
    box_constraints a ->
    is_vec_leq 0 s ->
    dot a 1 = m ->
    dot s 1 = (2 * c)%R ->
    hinge_form c a
      (List.app (to_list (second_gadget_instance m c s))
        (to_list (gaussian_schedule m n))) =
      (hinge_form c a (to_list (second_gadget_instance m c s)) +
       hinge_form c a (to_list (gaussian_schedule m n)))%R.
Proof.
  intros n m c a s Hn Hm Hc Hbox Hs Hdot Hstotal.
  apply hinge_form_app_no_cross.
  intros g Hg.
  unfold second_gadget_instance in Hg.
  simpl in Hg.
  destruct Hg as [Hg | [Hg | [Hg | []]]]; subst.
  - apply second_gadget_schedule_hinge_against_zero_1;
      try solve [destruct Hbox; assumption | assumption | lia].
    auto.
  - apply second_gadget_schedule_hinge_against_zero_2;
      try solve [destruct Hbox; assumption | assumption | lia].
      auto.
  - apply second_gadget_schedule_hinge_against_zero_3;
      try solve [assumption | lia].
    auto.
Qed.

Corollary second_gadget_partition_schedule_hinge_form_app :
  forall (d : nat) (a s : vec (2 * d)),
    (1 < d)%nat ->
    1 <= dot s 1 / 2 ->
    box_constraints a ->
    perf_square_vec s ->
    dot a 1 = INR d ->
    hinge_form (dot s 1 / 2) a
      (List.app
        (to_list (second_gadget_partition_instance (INR d) s))
        (to_list (gaussian_schedule (INR d) (2 * d)))) =
      (hinge_form (dot s 1%Vec / 2) a
        (to_list (second_gadget_partition_instance (INR d) s)) +
       hinge_form (dot s 1%Vec / 2) a
        (to_list (gaussian_schedule (INR d) (2 * d))))%R.
Proof.
  intros d a s Hd Hc Hbox Hsquares Hdot.
  unfold second_gadget_partition_instance, second_gadget_c.
  apply second_gadget_schedule_hinge_form_app.
  - lia.
  - replace 2%R with (INR 2) by (simpl; lra).
    apply le_INR. lia.
  - exact Hc.
  - exact Hbox.
  - apply perf_square_non_neg. exact Hsquares.
  - exact Hdot.
  - lra.
Qed.

Theorem second_gadget_hinge_form_partition_iff :
  forall (d : nat) (a s : vec (2 * d)),
    (0 < d)%nat ->
    perf_square_vec s ->
    is_binary a ->
    dot a 1 = INR d ->
    hinge_form (dot s 1 / 2) a
      (to_list (second_gadget_partition_instance (INR d) s)) = 0%R <->
    dot a s = dot s 1 / 2.
Proof.
  intros d a s Hd Hsquares Hbin Hcard.
  set (m := INR d) in *.
  set (c := dot s 1 / 2) in *.
  set (gamma := second_gadget_gamma (2 * d) m).
  assert (Ha_nonneg : is_vec_leq 0 a).
  { apply is_binary_nonneg. exact Hbin. }
  assert (Hs_nonneg : is_vec_leq 0 s).
  { apply perf_square_non_neg. exact Hsquares. }
  assert (Hm_pos : 0 < m).
  { unfold m. rewrite <- INR_0. apply lt_INR. lia. }
  assert (Hm_nonneg : 0 <= m) by lra.
  assert (Hm_ge_1 : 1 <= m).
  { unfold m. rewrite <- INR_1. apply le_INR. lia. }
  assert (Hgamma_pos : 0 < gamma).
  { unfold gamma. apply second_gadget_gamma_pos. exact Hm_pos. }
  assert (Hgamma2_pos : 0 < gamma * gamma) by nra.
  assert (Hcoef_pos : 0 < gamma * gamma * m * m).
  { assert (0 < m * m) by nra. nra. }
  assert (Hc_nonneg : 0 <= c).
  {
    unfold c.
    pose proof (non_neg_dot_1 s Hs_nonneg).
    lra.
  }
  assert (Hdotas_nonneg : 0 <= dot a s).
  { apply dot_vec_noneg_0; assumption. }
  split.
  - intro Hzero.
    unfold second_gadget_partition_instance, second_gadget_c,
      second_gadget_instance in Hzero.
    fold c in Hzero.
    simpl in Hzero.
    assert (Z12 :
      gaussian_pair_hinge c a
        (second_gadget_g1 m c) (second_gadget_g2 m c s) = 0%R).
    {
      pose proof (gaussian_pair_hinge_nonneg c a
        (second_gadget_g1 m c) (second_gadget_g2 m c s)) as N12.
      pose proof (gaussian_pair_hinge_nonneg c a
        (second_gadget_g1 m c) (second_gadget_g3 m c s)) as N13.
      pose proof (gaussian_pair_hinge_nonneg c a
        (second_gadget_g2 m c s) (second_gadget_g3 m c s)) as N23.
      rewrite ! Rplus_0_r in Hzero.
      rewrite Rplus_assoc in Hzero.
      apply Rplus_eq_0_l in Hzero; auto.
      apply Rplus_le_le_0_compat; auto.
    }
    assert (Z13 :
      gaussian_pair_hinge c a
        (second_gadget_g1 m c) (second_gadget_g3 m c s) = 0%R).
    {
      pose proof (gaussian_pair_hinge_nonneg c a
        (second_gadget_g1 m c) (second_gadget_g2 m c s)) as N12.
      pose proof (gaussian_pair_hinge_nonneg c a
        (second_gadget_g1 m c) (second_gadget_g3 m c s)) as N13.
      pose proof (gaussian_pair_hinge_nonneg c a
        (second_gadget_g2 m c s) (second_gadget_g3 m c s)) as N23.
      rewrite ! Rplus_0_r in Hzero.
      rewrite Rplus_assoc in Hzero.
      rewrite Rplus_comm in Hzero.
      rewrite Rplus_assoc in Hzero.
      apply Rplus_eq_0_l in Hzero; auto.
      apply Rplus_le_le_0_compat; auto.
    }
    assert (H12mul :
      c *
        Rmax (dot a (second_gadget_sigma1 m))
          (dot a (second_gadget_sigma2 m)) <=
      dot a (sqvec (second_gadget_mu1 m c - second_gadget_mu2 m c s))).
    {
      unfold gaussian_pair_hinge, gaussian_pair_stats,
        second_gadget_g1, second_gadget_g2 in Z12.
      simpl in Z12.
      apply hinge_zero_mul_le in Z12.
      - exact Z12.
      - apply Rmax_lt_if_r.
        rewrite second_gadget_sigma2_dot.
        rewrite Hcard at 1.
        replace (d + (d + 0))%nat with (2 * d)%nat by lia.
        fold gamma.
        nra.
    }
    assert (Hsig2_le :
      gamma * gamma * m * m <=
      Rmax (dot a (second_gadget_sigma1 m))
        (dot a (second_gadget_sigma2 m))).
    {
      replace (gamma * gamma * m * m)%R
        with (dot a (second_gadget_sigma2 m)).
      - apply Rmax_r.
      - rewrite second_gadget_sigma2_dot.
        rewrite Hcard.
        fold gamma.
        ring.
    }
    assert (Hlower_mul :
      c * (gamma * gamma * m * m) <=
      dot a (sqvec (second_gadget_mu1 m c - second_gadget_mu2 m c s))) by nra.
    rewrite second_gadget_12_distance in Hlower_mul.
    rewrite (sq_sqrt_vec _ _ Hs_nonneg) in Hlower_mul.
    fold gamma in Hlower_mul.
    assert (Hlower : c <= dot a s).
    {
      replace (c * (gamma * gamma * m * m))%R
        with ((gamma * gamma * m * m) * c)%R in Hlower_mul by ring.
      replace (gamma * gamma * m * m * dot a s)%R
        with ((gamma * gamma * m * m) * dot a s)%R in Hlower_mul by ring.
      apply (Rmult_le_reg_l (gamma * gamma * m * m)); assumption.
    }
    destruct (Req_dec c 0) as [Hc0 | Hcneq].
    + assert (Hs0 : s = 0).
      {
        apply non_neg_dot_0.
        - exact Hs_nonneg.
        - unfold c in Hc0. lra.
      }
      rewrite Hs0.
      rewrite dot_comm, dot_0.
      unfold c in Hc0.
      subst c. auto.
    + assert (Hc_pos : 0 < c) by lra.
      assert (H13mul :
        c *
          Rmax (dot a (second_gadget_sigma1 m))
            (dot a (second_gadget_sigma3 m s)) <=
        dot a (sqvec (second_gadget_mu1 m c - second_gadget_mu3 m c))).
      {
        unfold gaussian_pair_hinge, gaussian_pair_stats,
          second_gadget_g1, second_gadget_g3 in Z13.
        simpl in Z13.
        apply hinge_zero_mul_le in Z13.
        - exact Z13.
        - apply Rmax_lt_if_l.
          rewrite second_gadget_sigma1_dot.
          rewrite Hcard at 1.
          replace (d + (d + 0))%nat with (2 * d)% nat by auto.
          fold gamma.
          nra.
      }
      assert (Hsig3_le :
        gamma * gamma * m * dot a s <=
        Rmax (dot a (second_gadget_sigma1 m))
          (dot a (second_gadget_sigma3 m s))).
      {
        replace (gamma * gamma * m * dot a s)%R
          with (dot a (second_gadget_sigma3 m s)).
        - apply Rmax_r.
        - rewrite second_gadget_sigma3_dot.
          fold gamma.
          ring.
      }
      assert (Hupper_mul :
        c * (gamma * gamma * m * dot a s) <=
        dot a (sqvec (second_gadget_mu1 m c - second_gadget_mu3 m c))) by nra.
      rewrite second_gadget_13_distance in Hupper_mul.
      rewrite Hcard in Hupper_mul.
      fold gamma in Hupper_mul.
      assert (Hupper : dot a s <= c).
      {
        replace (c * (gamma * gamma * m * dot a s))%R
          with ((gamma * gamma * m * c) * dot a s)%R in Hupper_mul by ring.
        replace (gamma * gamma * c * c * m)%R
          with ((gamma * gamma * m * c) * c)%R in Hupper_mul by ring.
        apply (Rmult_le_reg_l (gamma * gamma * m * c)); nra.
      }
      lra.
  - intro Hsum.
    assert (Hc_zero_or_ge_1 : (c = 0 \/ 1 <= c)%R).
    {
      destruct (binary_perf_square_dot_zero_or_ge_1 a s Hbin Hsquares)
        as [Hzero | Hge].
      - left. lra.
      - right. lra.
    }
    assert (Z12 :
      gaussian_pair_hinge c a
        (second_gadget_g1 m c) (second_gadget_g2 m c s) = 0%R).
    {
      unfold gaussian_pair_hinge, gaussian_pair_stats,
        second_gadget_g1, second_gadget_g2.
      simpl.
      apply hinge_zero_of_mul_le.
      - apply Rmax_lt_if_r.
        rewrite second_gadget_sigma2_dot.
        rewrite Hcard at 1.
        replace (d + (d + 0))%nat with (2 * d)% nat by auto.
        fold gamma.
        nra.
      - apply Rmult_Rmax_le; [exact Hc_nonneg| |].
        + rewrite second_gadget_sigma1_dot.
          rewrite second_gadget_12_distance.
          rewrite (sq_sqrt_vec _ _ Hs_nonneg) at 1.
          rewrite Hcard, Hsum at 1.
          replace (d + (d + 0))%nat with (2 * d)%nat by trivial.
          fold gamma.
          rewrite (Rmult_comm _ c).
          apply Rmult_le_compat_l; auto.
          rewrite ! (Rmult_assoc).
          apply Rmult_le_compat_l; [lra|].
          apply Rmult_le_compat_l; [lra|].
          nra.
        + rewrite second_gadget_sigma2_dot.
          rewrite second_gadget_12_distance.
          rewrite (sq_sqrt_vec _ _ Hs_nonneg) at 1.
          rewrite Hcard, Hsum at 1.
          fold gamma.
          nra.
    }
    assert (Z13 :
      gaussian_pair_hinge c a
        (second_gadget_g1 m c) (second_gadget_g3 m c s) = 0%R).
    {
      unfold gaussian_pair_hinge, gaussian_pair_stats,
        second_gadget_g1, second_gadget_g3.
      simpl.
      apply hinge_zero_of_mul_le.
      - apply Rmax_lt_if_l.
        rewrite second_gadget_sigma1_dot.
        rewrite Hcard at 1.
        replace (d + (d + 0))%nat with (2 * d)%nat by trivial.
        fold gamma.
        nra.
      - apply Rmult_Rmax_le; [exact Hc_nonneg| |].
        + rewrite second_gadget_sigma1_dot.
          rewrite second_gadget_13_distance.
          rewrite Hcard at 1 2.
          replace (d + (d + 0))%nat with (2 * d)%nat by trivial.
          fold gamma.
          destruct Hc_zero_or_ge_1 as [Hc0 | Hc1].
          -- rewrite Hc0. nra.
          -- rewrite (Rmult_comm _ c).
             rewrite ! (Rmult_assoc).
             apply Rmult_le_compat_l; auto.
             apply Rmult_le_compat_l; [lra|].
             apply Rmult_le_compat_l; [lra|].
             nra.
        + rewrite second_gadget_sigma3_dot.
          rewrite second_gadget_13_distance.
          rewrite Hcard, Hsum at 1.
          replace (d + (d + 0))%nat with (2 * d)%nat by trivial.
          fold gamma.
          nra.
    }
    assert (Z23 :
      gaussian_pair_hinge c a
        (second_gadget_g2 m c s) (second_gadget_g3 m c s) = 0%R).
    {
      assert (Hm_term :
        (m * m * dot a s <=
          dot a (sqvec (c * 1 + m * sqrtvec s)%Vec))%R).
      {
        eapply Rle_trans.
        - rewrite <- (sq_sqrt_vec _ _ Hs_nonneg) at 1.
          rewrite <- dot_mult_dist_r.
          rewrite <- sqvec_dist.
          apply red_23; auto.
          + apply vec_sqrt_nonneg; assumption.
          + apply vec_nonneg_mult_1. exact Hc_nonneg.
        - rewrite vec_plus_comm.
          right. reflexivity.
      }
      assert (Hc_term :
        (c * c * dot a 1%Vec <=
          dot a (sqvec (c * 1 + m * sqrtvec s)%Vec))%R).
      {
        replace (c * c * dot a 1%Vec)%R
          with (dot a (sqvec (c * 1))).
        - apply red_23; auto.
          + apply vec_nonneg_mult_1. exact Hc_nonneg.
          + apply vec_sqrt_nonneg; assumption.
        - rewrite sqvec_dist.
          rewrite dot_mult_dist_r.
          rewrite sqvec_1.
          reflexivity.
      }
      unfold gaussian_pair_hinge, gaussian_pair_stats,
        second_gadget_g2, second_gadget_g3.
      simpl.
      apply hinge_zero_of_mul_le.
      - apply Rmax_lt_if_l.
        rewrite second_gadget_sigma2_dot.
        rewrite Hcard at 1.
        replace (d + (d + 0))%nat with (2 * d)%nat by trivial.
        fold gamma.
        nra.
      - apply Rmult_Rmax_le; [exact Hc_nonneg| |].
        + rewrite second_gadget_sigma2_dot.
          rewrite second_gadget_23_distance.
          rewrite Hcard at 1.
          replace (d + (d + 0))% nat with (2 * d)% nat at 1 2 3 4 by trivial.
          fold gamma.
          rewrite Hsum in Hm_term.
          replace (c * (gamma * gamma * m * m))%R with
            (gamma * gamma * c * m * m)%R by lra.
          rewrite 2 (Rmult_assoc).
          apply Rmult_le_compat_l; [lra|].
          rewrite Rmult_comm.
          apply Hm_term.
        + rewrite second_gadget_sigma3_dot.
          rewrite second_gadget_23_distance.
          rewrite Hsum at 1.
          replace (d + (d + 0))% nat with (2 * d)% nat at 1 2 3 4 by trivial.
          fold gamma.
          replace (c * (gamma * gamma * m * c))%R with
            (gamma * gamma * c * c * m)%R by lra.
          rewrite 2 (Rmult_assoc).
          apply Rmult_le_compat_l; [lra|].
          rewrite <- Rmult_assoc.
          rewrite Hcard in Hc_term.
          apply Hc_term.
    }
    unfold second_gadget_partition_instance, second_gadget_c,
      second_gadget_instance.
    fold c.
    simpl.
    rewrite Z12, Z13, Z23 at 1.
    lra.
Qed.

Definition partition_gadget_schedule (d : nat) (s : vec (2 * d))
  : list (@gaussian (2 * d)) :=
  List.app
    (to_list (second_gadget_partition_instance (INR d) s))
    (to_list (gaussian_schedule (INR d) (2 * d))).

(* The recursive schedule contributes correction terms for coordinates
   [1..2*d-1].  The threshold includes the missing coordinate-[0] term so
   box constraints make the full correction tight exactly at binary points. *)
Definition partition_schedule_threshold (d : nat)
  (a s : vec (2 * d)) : R :=
  let n := (2 * d - 1)%nat in
  (dot s 1%Vec / 2 * INR n * (INR n + 1) / 2 -
   (3 * INR d / 2 - / (1 + dot a (canon_e 0))))%R.

Lemma is_binary_le_1 :
  forall {d : nat} (a : vec d),
    is_binary a -> is_vec_leq a 1.
Proof.
  induction d; intros a Hbin.
  - rewrite (nil_spec a). constructor.
  - rewrite (eta a) in *.
    inv Hbin.
    rewrite (eta 1).
    constructor.
    + simpl. destruct H2; subst; lra.
    + apply IHd. exact H3.
Qed.

Lemma is_binary_box_constraints :
  forall {d : nat} (a : vec d),
    is_binary a -> box_constraints a.
Proof.
  intros d a Hbin.
  split.
  - apply is_binary_nonneg. exact Hbin.
  - apply is_binary_le_1. exact Hbin.
Qed.

Lemma dot_canon_e_0 :
  forall {d : nat} (a : vec (S d)),
    dot a (canon_e 0) = hd a.
Proof.
  intros d a.
  rewrite (dot_step).
  simpl.
  rewrite dot_comm.
  rewrite dot_0.
  lra.
Qed.

Lemma dot_canon_e_shift :
  forall {d : nat} (a : vec (S d)) (i : nat),
    dot a (canon_e (S i)) = dot (tl a) (canon_e i).
Proof.
  intros d a i.
  rewrite dot_step.
  simpl. lra.
Qed.

Lemma gaussian_schedule_hinge_correction_shift :
  forall {d : nat} (n : nat) (a : vec (S d)),
    gaussian_schedule_hinge_correction a (S n) =
      (/ (1 + dot (tl a) (canon_e 0)) +
       gaussian_schedule_hinge_correction (tl a) n)%R.
Proof.
  intros d n a. revert d a.
  induction n; intros d a.
  - simpl. rewrite (dot_step a). simpl.
    rewrite Rmult_0_r. rewrite ! Rplus_0_l. lra.
  - simpl.
    simpl in IHn.
    rewrite IHn.
    rewrite (dot_step a).
    simpl. rewrite Rmult_0_r.
    rewrite Rplus_0_l.
    lra.
Qed.

Definition full_schedule_hinge_correction {d : nat} (a : vec d) : R :=
  match d as d return vec d -> R with
  | O => fun _ => 0%R
  | S n =>
      fun a =>
        (/ (1 + dot a (canon_e 0)) +
         gaussian_schedule_hinge_correction a n)%R
  end a.

Lemma full_schedule_hinge_correction_cons :
  forall {d : nat} (a : vec (S d)),
    full_schedule_hinge_correction a =
      (/ (1 + hd a) + full_schedule_hinge_correction (tl a))%R.
Proof.
  destruct d; intros a.
  - rewrite (nil_spec (tl a)).
    rewrite (eta a). cbn. rewrite (nil_spec (tl a)). simpl.
    rewrite Rmult_1_r.
    rewrite ! Rplus_0_r.
    trivial.
  - unfold full_schedule_hinge_correction.
    rewrite gaussian_schedule_hinge_correction_shift.
    rewrite dot_step.
    simpl. rewrite Rmult_1_r.
    replace (0%R::0) with (0: vec (S d)) by trivial.
    rewrite (dot_comm _ 0).
    rewrite (dot_0).
    rewrite Rplus_0_r.
    trivial.
Qed.

Lemma inv_one_plus_le_line :
  forall x : R,
    0 <= x <= 1 ->
    / (1 + x) <= 1 - x / 2.
Proof.
  intros x Hx.
  assert (Hpos : 0 < 1 + x) by lra.
  apply (Rmult_le_reg_r (1 + x)); [exact Hpos|].
  replace (/ (1 + x) * (1 + x))%R with 1%R by (field; lra).
  replace ((1 - x / 2) * (1 + x))%R with
    (1 + x * (1 - x) / 2)%R by field.
  nra.
Qed.

Lemma inv_one_plus_line_eq_binary :
  (forall x : R,
    0 <= x <= 1 ->
    / (1 + x) = 1 - x / 2 ->
    x = 0 \/ x = 1)%R.
Proof.
  intros x Hx Heq.
  assert (Hpos : 0 < 1 + x) by lra.
  assert (Hprod : (x * (1 - x) = 0)%R).
  {
    assert (Hmul :
      (1 = (1 - x / 2) * (1 + x))%R).
    {
      rewrite <- Heq.
      field. lra.
    }
    nra.
  }
  apply Rmult_integral in Hprod.
  destruct Hprod; lra.
Qed.

Lemma full_schedule_hinge_correction_le_line :
  forall {d : nat} (a : vec d),
    box_constraints a ->
    full_schedule_hinge_correction a <=
      INR d - dot a 1 / 2.
Proof.
  induction d; intros a [Ha0 Ha1].
  - rewrite (nil_spec a).
    simpl. lra.
  - rewrite full_schedule_hinge_correction_cons.
    rewrite dot_step.
    rewrite S_INR.
    simpl.
    rewrite (eta a) in Ha0, Ha1.
    inversion Ha0 as [| ? ? ? ? ? Ha_hd0 Ha_tl0]; subst; clear Ha0.
    inversion Ha1 as [| ? ? ? ? ? Ha_hd1 Ha_tl1]; subst; clear Ha1.
    inv_cleanup.
    pose proof (inv_one_plus_le_line (hd a) ltac:(lra)) as Hhd.
    pose proof (IHd (tl a) (conj Ha_tl0 Ha_tl1)) as Htl.
    lra.
Qed.

Lemma full_schedule_hinge_correction_eq_binary :
  forall {d : nat} (a : vec d),
    box_constraints a ->
    full_schedule_hinge_correction a =
      (INR d - dot a 1%Vec / 2)%R ->
    is_binary a.
Proof.
  induction d; intros a [Ha0 Ha1] Hcorr.
  - rewrite nil_spec.
    constructor.
  - rewrite full_schedule_hinge_correction_cons in Hcorr.
    rewrite dot_step in Hcorr.
    rewrite S_INR in Hcorr.
    simpl in Hcorr.
    rewrite (eta a) in Ha0, Ha1.
    inversion Ha0 as [| ? ? ? ? ? Ha_hd0 Ha_tl0]; subst; clear Ha0.
    inversion Ha1 as [| ? ? ? ? ? Ha_hd1 Ha_tl1]; subst; clear Ha1.
    inv_cleanup.
    pose proof (inv_one_plus_le_line (hd a) ltac:(lra)) as Hhd_le.
    pose proof
      (full_schedule_hinge_correction_le_line (tl a)
        (conj Ha_tl0 Ha_tl1)) as Htl_le.
    assert (Hhd_eq : (/ (1 + hd a) = 1 - hd a / 2)%R) by lra.
    assert (Htl_eq :
      full_schedule_hinge_correction (tl a) =
        (INR d - dot (tl a) 1%Vec / 2)%R) by lra.
    rewrite (eta a).
    constructor.
    + apply inv_one_plus_line_eq_binary; [lra|exact Hhd_eq].
    + apply IHd; [split; assumption|exact Htl_eq].
Qed.

Lemma full_schedule_hinge_correction_binary_line :
  forall {d : nat} (a : vec d),
    is_binary a ->
    full_schedule_hinge_correction a =
      (INR d - dot a 1%Vec / 2)%R.
Proof.
  induction d; intros a Hbin.
  - rewrite (nil_spec a).
    simpl. lra.
  - rewrite full_schedule_hinge_correction_cons.
    rewrite dot_step.
    rewrite S_INR.
    simpl.
    rewrite (eta a) in Hbin.
    inv Hbin.
    inv_cleanup.
    rewrite IHd by exact H3.
    destruct H2 as [Ha | Ha]; rewrite Ha; simpl; lra.
Qed.

Lemma schedule_full_correction_le_line :
  forall {D : nat} (n : nat) (a : vec D),
    D = S n ->
    box_constraints a ->
    (/ (1 + dot a (canon_e 0)) +
     gaussian_schedule_hinge_correction a n <=
      INR D - dot a 1%Vec / 2)%R.
Proof.
  intros D n a HD Hbox.
  subst D.
  change
    ((full_schedule_hinge_correction a <=
      INR (S n) - dot a 1%Vec / 2)%R).
  apply full_schedule_hinge_correction_le_line.
  exact Hbox.
Qed.

Lemma schedule_full_correction_eq_binary :
  forall {D : nat} (n : nat) (a : vec D),
    D = S n ->
    box_constraints a ->
    (/ (1 + dot a (canon_e 0)) +
     gaussian_schedule_hinge_correction a n =
      INR D - dot a 1%Vec / 2)%R ->
    is_binary a.
Proof.
  intros D n a HD Hbox Hcorr.
  subst D.
  change
    (is_binary a).
  apply full_schedule_hinge_correction_eq_binary.
  - exact Hbox.
  - exact Hcorr.
Qed.

Lemma schedule_full_correction_binary_line :
  forall {D : nat} (n : nat) (a : vec D),
    D = S n ->
    is_binary a ->
    (/ (1 + dot a (canon_e 0)) +
     gaussian_schedule_hinge_correction a n =
      INR D - dot a 1%Vec / 2)%R.
Proof.
  intros D n a HD Hbin.
  subst D.
  change
    ((full_schedule_hinge_correction a =
      INR (S n) - dot a 1%Vec / 2)%R).
  apply full_schedule_hinge_correction_binary_line.
  exact Hbin.
Qed.

Theorem partition_gadget_schedule_partition_iff :
  forall (d : nat) (a s : vec (2 * d)),
    (1 < d)%nat ->
    1 <= dot s 1 / 2 ->
    perf_square_vec s ->
    (box_constraints a /\
     dot a 1 = INR d /\
      hinge_form (dot s 1 / 2) a
        (partition_gadget_schedule d s) <=
      partition_schedule_threshold d a s) <->
    is_ec_partition a s.
Proof.
  intros d a s Hd Hc Hsquares.
  assert (Hm_ge_2 : 2 <= INR d).
  {
    replace 2%R with (INR 2) by (simpl; lra).
    apply le_INR. lia.
  }
  split.
  - intros [Hbox [Hcard Hhinge]].
    assert (Hnonneg : is_vec_leq 0 a) by (destruct Hbox; assumption).
    assert (Happ :
      hinge_form (dot s 1 / 2) a
        (partition_gadget_schedule d s) =
      (hinge_form (dot s 1%Vec / 2) a
        (to_list (second_gadget_partition_instance (INR d) s)) +
       hinge_form (dot s 1%Vec / 2) a
        (to_list (gaussian_schedule (INR d) (2 * d))))%R).
    {
      unfold partition_gadget_schedule.
      apply second_gadget_partition_schedule_hinge_form_app;
        assumption.
    }
    assert (Hschedule :
      hinge_form (dot s 1 / 2) a
        (to_list (gaussian_schedule (INR d) (2 * d))) =
      (dot s 1%Vec / 2 *
        INR (2 * d - 1) * (INR (2 * d - 1) + 1) / 2 -
       gaussian_schedule_hinge_correction a (2 * d - 1))%R).
    {
      assert (Hlen :
        to_list (@gaussian_schedule (2 * d)%nat (INR d) (2 * d)) =
        to_list (@gaussian_schedule (2 * d)%nat (INR d) (S (2 * d - 1)))).
      {
        assert (Hn : (2 * d)%nat = S (2 * d - 1)) by lia.
        now destruct Hn.
      }
      rewrite Hlen.
      rewrite gaussian_schedule_hinge_form_prefix_m_ge_2;
        try assumption.
      reflexivity.
    }
    set (G :=
      hinge_form (dot s 1 / 2) a
        (to_list (second_gadget_partition_instance (INR d) s))) in *.
    set (C :=
      (dot s 1%Vec / 2 *
        INR (2 * d - 1) * (INR (2 * d - 1) + 1) / 2)%R) in *.
    set (Corr := gaussian_schedule_hinge_correction a (2 * d - 1)) in *.
    set (K :=
      (3 * INR d / 2 - / (1 + dot a (canon_e 0)))%R) in *.
    rewrite Happ in Hhinge.
    rewrite Hschedule in Hhinge.
    unfold partition_schedule_threshold in Hhinge.
    change (G + (C - Corr) <= C - K)%R in Hhinge.
    assert (Hgadget_nonneg : 0 <= G).
    { unfold G. apply hinge_form_nonneg. }
    assert (Hfull_le :
      (/ (1 + dot a (canon_e 0)) +
       gaussian_schedule_hinge_correction a (2 * d - 1) <=
       3 * INR d / 2)%R).
    {
      pose proof
        (@schedule_full_correction_le_line
          (2 * d)%nat (2 * d - 1)%nat a ltac:(lia) Hbox) as Hle.
      rewrite Hcard in Hle.
      replace (INR (2 * d) - INR d / 2)%R with
        (3 * INR d / 2)%R in Hle.
      - exact Hle.
      - rewrite mult_INR. simpl. lra.
    }
    assert (HCorr_le_K : Corr <= K) by (unfold Corr, K; lra).
    assert (Hgadget_zero : G = 0%R).
    {
      assert (HG_le_0 : G <= 0).
      {
        apply (Rplus_le_reg_r (C - Corr)).
        eapply Rle_trans.
        - exact Hhinge.
        - rewrite Rplus_0_l.
          unfold Rminus.
          apply Rplus_le_compat_l.
          apply Ropp_le_contravar.
          exact HCorr_le_K.
      }
      apply Rle_antisym.
      - exact HG_le_0.
      - exact Hgadget_nonneg.
    }
    assert (Hfull_eq :
      (/ (1 + dot a (canon_e 0)) +
       gaussian_schedule_hinge_correction a (2 * d - 1) =
       INR (2 * d) - dot a 1%Vec / 2)%R).
    {
      assert (HK_le_Corr : K <= Corr).
      {
        rewrite Hgadget_zero in Hhinge.
        lra.
      }
      assert (HCorr_eq_K : Corr = K) by lra.
      unfold Corr, K in HCorr_eq_K.
      rewrite Hcard.
      replace (INR (2 * d) - INR d / 2)%R with
        (3 * INR d / 2)%R.
      - lra.
      - rewrite mult_INR. simpl. lra.
    }
    assert (Hbin : is_binary a).
    {
      apply
        (@schedule_full_correction_eq_binary
          (2 * d)%nat (2 * d - 1)%nat a ltac:(lia) Hbox).
      exact Hfull_eq.
    }
    pose proof
      (proj1
        (second_gadget_hinge_form_partition_iff d a s
          ltac:(lia) Hsquares Hbin Hcard)
        Hgadget_zero) as Hsum.
    unfold is_ec_partition.
    split; [exact Hbin|].
    split.
    + rewrite Hcard.
      rewrite mult_INR.
      simpl. lra.
    + exact Hsum.
  - intro Hpart.
    destruct Hpart as [Hbin_part [Hcard_half Hsum]].
    assert (Hbox : box_constraints a).
    { apply is_binary_box_constraints. exact Hbin_part. }
    assert (Hnonneg : is_vec_leq 0 a) by (destruct Hbox; assumption).
    assert (Hcard : dot a 1 = INR d).
    {
      rewrite Hcard_half.
      rewrite mult_INR.
      simpl. lra.
    }
    split; [exact Hbox|].
    split; [exact Hcard|].
    assert (Hgadget_zero :
      hinge_form (dot s 1 / 2) a
        (to_list (second_gadget_partition_instance (INR d) s)) = 0%R).
    {
      apply
        (proj2
          (second_gadget_hinge_form_partition_iff d a s
            ltac:(lia) Hsquares Hbin_part Hcard)).
      exact Hsum.
    }
    assert (Happ :
      hinge_form (dot s 1 / 2) a
        (partition_gadget_schedule d s) =
      (hinge_form (dot s 1%Vec / 2) a
        (to_list (second_gadget_partition_instance (INR d) s)) +
       hinge_form (dot s 1%Vec / 2) a
        (to_list (gaussian_schedule (INR d) (2 * d))))%R).
    {
      unfold partition_gadget_schedule.
      apply second_gadget_partition_schedule_hinge_form_app;
        assumption.
    }
    assert (Hschedule :
      hinge_form (dot s 1 / 2) a
        (to_list (gaussian_schedule (INR d) (2 * d))) =
      (dot s 1%Vec / 2 *
        INR (2 * d - 1) * (INR (2 * d - 1) + 1) / 2 -
       gaussian_schedule_hinge_correction a (2 * d - 1))%R).
    {
      assert (Hlen :
        to_list (@gaussian_schedule (2 * d)%nat (INR d) (2 * d)) =
        to_list (@gaussian_schedule (2 * d)%nat (INR d) (S (2 * d - 1)))).
      {
        assert (Hn : (2 * d)%nat = S (2 * d - 1)) by lia.
        now destruct Hn.
      }
      rewrite Hlen.
      rewrite gaussian_schedule_hinge_form_prefix_m_ge_2;
        try assumption.
      reflexivity.
    }
    assert (Hfull_eq :
      (/ (1 + dot a (canon_e 0)) +
       gaussian_schedule_hinge_correction a (2 * d - 1) =
       INR (2 * d) - dot a 1%Vec / 2)%R).
    {
      apply
        (@schedule_full_correction_binary_line
          (2 * d)%nat (2 * d - 1)%nat a ltac:(lia)).
      exact Hbin_part.
    }
    set (G :=
      hinge_form (dot s 1 / 2) a
        (to_list (second_gadget_partition_instance (INR d) s))) in *.
    set (C :=
      (dot s 1%Vec / 2 *
        INR (2 * d - 1) * (INR (2 * d - 1) + 1) / 2)%R) in *.
    set (Corr := gaussian_schedule_hinge_correction a (2 * d - 1)) in *.
    set (K :=
      (3 * INR d / 2 - / (1 + dot a (canon_e 0)))%R) in *.
    rewrite Happ.
    rewrite Hschedule.
    rewrite Hgadget_zero.
    unfold partition_schedule_threshold.
    change (0 + (C - Corr) <= C - K)%R.
    assert (HCorr_eq_K : Corr = K).
    {
      unfold K.
      rewrite Hcard in Hfull_eq.
      replace (INR (2 * d) - INR d / 2)%R with
        (3 * INR d / 2)%R in Hfull_eq.
      - lra.
      - rewrite mult_INR. simpl. lra.
    }
    rewrite HCorr_eq_K.
    rewrite Rplus_0_l.
    reflexivity.
Qed.



Close Scope vec_scope.
Close Scope R_scope.
