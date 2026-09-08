From Coq Require Import Arith.Arith Arith.PeanoNat Bool.Bool Lia Psatz.

Definition sq (x : nat) : nat := x * x.

Definition xplus (N : nat) (a : nat -> nat) (K i : nat) : nat :=
  sq (K ^ (N + i) + a i * K ^ (N - i)).

Definition xminus (N : nat) (a : nat -> nat) (K i : nat) : nat :=
  sq (K ^ (N + i) - a i * K ^ (N - i)).

Fixpoint sum_upto (m : nat) (f : nat -> nat) : nat :=
  match m with
  | 0 => 0
  | S m' => sum_upto m' f + f m'
  end.

Definition choose_sum (m : nat) (a : nat -> nat) (b : nat -> bool) : nat :=
  sum_upto m (fun i => if b i then a i else 0).

Definition left_sq_sum (N m : nat) (a : nat -> nat) (K : nat) (b : nat -> bool) : nat :=
  sum_upto m (fun i => if b i then xplus N a K i else xminus N a K i).

Definition right_sq_sum (N m : nat) (a : nat -> nat) (K : nat) (b : nat -> bool) : nat :=
  sum_upto m (fun i => if b i then xminus N a K i else xplus N a K i).

Lemma sq_gap :
  forall u v : nat,
    v <= u ->
    sq (u + v) = sq (u - v) + 4 * u * v.
Proof.
  intros u v Huv.
  unfold sq.
  nia.
Qed.

Lemma uv_form :
  forall N K i ai : nat,
    i <= N ->
    K ^ (N + i) * (ai * K ^ (N - i)) = ai * K ^ (2 * N).
Proof.
  intros N K i ai Hi.
  replace (K ^ (N + i) * (ai * K ^ (N - i)))
    with (ai * (K ^ (N + i) * K ^ (N - i))) by nia.
  rewrite <- Nat.pow_add_r.
  replace (N + i + (N - i)) with (2 * N) by lia.
  nia.
Qed.

Lemma upper_bound_root :
  forall N K i ai : nat,
    i <= N ->
    ai <= K ^ (2 * i) ->
    ai * K ^ (N - i) <= K ^ (N + i).
Proof.
  intros N K i ai Hi Hai.
  eapply Nat.le_trans.
  2: {
    rewrite Nat.pow_add_r.
    replace (2 * i + (N - i)) with (N + i) by lia.
    reflexivity.
  }
  assert (A: ai * K ^ (N - i) <=   K ^ (N - i) * K ^ (2 * i)).
  { rewrite Nat.mul_comm. apply Nat.mul_le_mono_l. exact Hai. }
  assert (B: K^(N-i) * K ^ (2*i) = K^(N+i)).
  { rewrite <- Nat.pow_add_r. f_equal. lia. }
  rewrite B in A.
  rewrite Nat.pow_add_r in A. exact A.
Qed.

Lemma xgap :
  forall N (a : nat -> nat) K i,
    i < N ->
    a i <= K ^ (2 * i) ->
    xplus N a K i = xminus N a K i + 4 * a i * K ^ (2 * N).
Proof.
  intros N a K i Hi Hai.
  unfold xplus, xminus.
  set (u := K ^ (N + i)).
  set (v := a i * K ^ (N - i)).
  assert (Hv : v <= u).
  {
    subst u v.
    apply upper_bound_root; lia.
  }
  rewrite sq_gap by exact Hv.
  subst u v.
  replace (4 * (K ^ (N + i) * (a i * K ^ (N - i))))
    with (4 * a i * K ^ (2 * N)).
  2: {
    rewrite uv_form by lia.
    nia.
  }
  f_equal.
  rewrite <- 2 Nat.mul_assoc.
  f_equal.
  rewrite Nat.mul_assoc.
  rewrite (Nat.mul_comm _ (a i)).
  rewrite <- Nat.mul_assoc.
  f_equal.
  rewrite <- Nat.pow_add_r.
  f_equal. lia.
Qed.

Lemma right_as_left :
  forall N m (a : nat -> nat) K (b : nat -> bool),
    right_sq_sum N m a K b = left_sq_sum N m a K (fun i => negb (b i)).
Proof.
  intros N m a K b.
  induction m as [|m IH]; simpl.
  - reflexivity.
  - cbn. unfold right_sq_sum, left_sq_sum in IH. rewrite IH.
    destruct (b m); reflexivity.
Qed.

Lemma left_decomp :
  forall N m (a : nat -> nat) K (b : nat -> bool),
    m <= N ->
    (forall i, i < m -> a i <= K ^ (2 * i)) ->
    left_sq_sum N m a K b
    =
    sum_upto m (fun i => xminus N a K i)
    + 4 * K ^ (2 * N) * choose_sum m a b.
Proof.
  intros N m a K b Hm Hbound.
  induction m as [|m IH].
  - cbn. lia.
  - assert (Hm' : m <= N) by lia.
    assert (Hbound' : forall i : nat, i < m -> a i <= K ^ (2 * i)).
    { intros i Hi. apply Hbound. lia. }
    unfold left_sq_sum.
    unfold left_sq_sum in IH.
    assert (A: m <= N) by lia.
    simpl sum_upto.
    rewrite (IH A Hbound').
    rewrite <- ! Nat.add_assoc.
    f_equal.
    unfold choose_sum.
    simpl sum_upto.
    rewrite xgap; auto.
    rewrite (Nat.add_comm (xminus N a K m) (4 * K ^ (2 * N) *
(sum_upto m
   (fun i : nat => if b i then a i else 0) +
 (if b m then a m else 0)))).
    rewrite Nat.mul_add_distr_l.
    rewrite <- Nat.add_assoc.
    f_equal.
    destruct (b m) eqn:Hbm; lia.
Qed.

Theorem square_partition_implies_partition_for_choice :
  forall N (a : nat -> nat) K (b : nat -> bool),
    1 <= K ->
    (forall i, i < N -> a i <= K ^ (2 * i)) ->
    left_sq_sum N N a K b = right_sq_sum N N a K b ->
    choose_sum N a b = choose_sum N a (fun i => negb (b i)).
Proof.
  intros N a K b HK Hbound Heq.
  rewrite right_as_left in Heq.
  rewrite (left_decomp N N a K b) in Heq; [|lia | exact Hbound].
  rewrite (left_decomp N N a K (fun i => negb (b i))) in Heq; [|lia | exact Hbound].
  assert (Hc : 0 < 4 * K ^ (2 * N)).
  {
    apply Nat.mul_pos_pos.
    - lia.
    - apply Nat.neq_0_lt_0.
      apply Nat.pow_nonzero.
      lia.
  }
  nia.
Qed.

Theorem exists_square_partition_implies_exists_partition :
  forall N (a : nat -> nat) K,
    1 <= K ->
    (forall i, i < N -> a i <= K ^ (2 * i)) ->
    (exists b, left_sq_sum N N a K b = right_sq_sum N N a K b) ->
    exists b, choose_sum N a b = choose_sum N a (fun i => negb (b i)).
Proof.
  intros N a K HK Hbound [b Hb].
  exists b.
  eapply square_partition_implies_partition_for_choice; eauto.
Qed.