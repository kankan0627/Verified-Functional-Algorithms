From Coq Require Import Strings.String. 
From Coq Require Import Setoid Morphisms.
From VFA Require Import Perm.
From VFA Require Import Sort.

Definition bag := list nat.

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | nil => 0
  | h :: t =>
      (if h =? v then 1 else 0) + count v t
  end.

Definition bag_eqv (b1 b2: bag) : Prop :=
  forall n, count n b1 = count n b2.

Lemma bag_eqv_refl : forall b, bag_eqv b b.
Proof. 
 unfold bag_eqv. auto. 
Qed.

Lemma bag_eqv_sym: forall b1 b2, bag_eqv b1 b2 -> bag_eqv b2 b1.
Proof.
 intros. 
 unfold bag_eqv in H. unfold bag_eqv.
 intros n. specialize (H n) as Hn. 
 rewrite Hn. auto. 
Qed.

Lemma bag_eqv_trans: forall b1 b2 b3, bag_eqv b1 b2 -> bag_eqv b2 b3 -> bag_eqv b1 b3.
Proof.
 intros. unfold bag_eqv in H.
 unfold bag_eqv in H0.  unfold bag_eqv.
 intros n. specialize (H n) as H1. 
  specialize (H0 n) as H2. rewrite H1.   
 rewrite H2. auto. 
Qed.

Lemma bag_eqv_cons : forall x b1 b2, bag_eqv b1 b2 -> bag_eqv (x::b1) (x::b2).
Proof.
  intros. unfold bag_eqv in H.  unfold bag_eqv.
  intros. simpl. bdestruct (x =? n).
  specialize (H n) as H1.
  - rewrite H1. auto. 
  - specialize (H n) as H1. rewrite H1. auto. 
Qed.

Definition is_a_sorting_algorithm' (f: list nat -> list nat) :=
  forall al, bag_eqv al (f al) /\ sorted (f al).

Lemma insert_bag: forall x l, bag_eqv (x::l) (insert x l).
Proof.
  intros x. induction l. 
  - unfold bag_eqv. intros. 
    simpl. bdestruct (x =? n); auto. 
  - unfold bag_eqv. intros.  simpl. 
    bdestruct (x =? n). 
    + bdestruct (a =? n).
      * bdestruct (x <=? a).
        -- simpl. apply Nat.eqb_eq in H.
           apply Nat.eqb_eq in H0. rewrite H. rewrite H0.
           auto. 
        -- simpl. apply Nat.eqb_eq in H0. rewrite H0.
           subst. unfold bag_eqv in IHl.
           specialize (IHl n) as Heq.
           simpl in Heq. rewrite Nat.eqb_refl in Heq.
           lia.
      * bdestruct (x <=? a).
        -- simpl. bdestruct (a =? n).
           ++ apply H0 in H2. inversion H2.
           ++ apply Nat.eqb_eq in H. rewrite H. auto.
        -- simpl. Search "=?". apply Nat.eqb_neq in H0. 
           rewrite H0. unfold bag_eqv in IHl.
           specialize (IHl n) as Heq. 
            simpl in Heq. apply Nat.eqb_eq in H. 
           rewrite H in Heq. lia. 
     + bdestruct (a =? n).
       * bdestruct (x <=? a).
        -- simpl. apply Nat.eqb_neq in H.
           apply Nat.eqb_eq in H0. rewrite H. rewrite H0.
           auto. 
        -- simpl. apply Nat.eqb_eq in H0. rewrite H0.
           subst. unfold bag_eqv in IHl.
           specialize (IHl n) as Heq.
           simpl in Heq. apply Nat.eqb_neq in H. rewrite H in Heq.
           lia.
      * bdestruct (x <=? a).
        -- simpl. bdestruct (a =? n).
           ++ apply H0 in H2. inversion H2.
           ++ apply Nat.eqb_neq in H. rewrite H. auto.
        -- simpl. apply Nat.eqb_neq in H0. 
           rewrite H0. unfold bag_eqv in IHl.
           specialize (IHl n) as Heq. 
            simpl in Heq. apply Nat.eqb_neq in H. 
           rewrite H in Heq. lia.
Qed. 

Theorem sort_bag: forall l, bag_eqv l (sort l).
Proof. 
  induction l.  
  - simpl. apply bag_eqv_refl.  
  - simpl. apply (bag_eqv_trans _ (a::(sort l)) _).
    + apply bag_eqv_cons. apply IHl. 
    + apply insert_bag. 
Qed.  

Theorem insertion_sort_correct:
  is_a_sorting_algorithm' sort.
Proof.
split. apply sort_bag. apply sort_sorted.
Qed.

Lemma perm_bag:
  forall al bl : list nat,
   Permutation al bl -> bag_eqv al bl.
Proof. 
  intros. 
  induction H. 
  - apply bag_eqv_refl. 
  - apply bag_eqv_cons. apply IHPermutation. 
  - unfold bag_eqv. intros. simpl. bdestruct (y =? n); bdestruct (x =? n); auto.
  - apply (bag_eqv_trans _ l' _); assumption. 
Qed.
   
Lemma bag_nil_inv : forall b, bag_eqv [] b -> b = [].
Proof.
   induction b.
   - auto. 
   - intros. unfold bag_eqv in H. simpl in H. 
     unfold bag_eqv in IHb. simpl in IHb.
     specialize (H a) as Heq. rewrite Nat.eqb_refl in Heq. 
     inversion Heq.  
Qed.

Lemma bag_cons_inv : forall l x n,
    S n = count x l ->
    exists l1 l2,
      l = l1 ++ x :: l2
      /\ count x (l1 ++ l2) = n.
Proof.
  induction l. 
  - intros. simpl in H. inversion H. 
  - intros. simpl in H. bdestruct (a =? x). 
    + simpl in H. inversion H. subst. exists []. 
      exists l. auto. 
    + simpl in H. apply IHl in H. destruct H as [l' [l'' H]].
      destruct H. subst. exists (a :: l'). exists l''.
      split. 
      * simpl. auto. 
      * simpl. apply Nat.eqb_neq in H0. rewrite H0. auto. 
Qed.

Lemma count_insert_other : forall l1 l2 x y,
    y <> x -> count y (l1 ++ x :: l2) = count y (l1 ++ l2).
Proof.
  induction l1. 
  - intros. simpl. bdestruct (x =? y).
    + symmetry in H0. apply H in H0. inversion H0. 
    + auto. 
  - intros. simpl. bdestruct (a =? y).
    + simpl. apply (IHl1 l2) in H. lia. 
    + simpl. apply (IHl1 l2) in H. lia.
Qed.

Lemma bag_perm:
  forall al bl, bag_eqv al bl -> Permutation al bl.
Proof.
  induction al. 
  - intros. apply bag_nil_inv in H. subst. apply perm_nil. 
  - intros.  unfold bag_eqv in H.  
    simpl in H. specialize (H a) as Heq. rewrite Nat.eqb_refl in Heq.
    simpl in Heq. apply bag_cons_inv in Heq. destruct Heq as [l1 [l2 Heq]].
    destruct Heq. subst bl. Search Permutation. apply Permutation_cons_app. 
    apply IHal. unfold bag_eqv. intros. bdestruct (a =? n).
    + subst n. symmetry. apply H1. 
    + apply Nat.eqb_neq in H0. specialize (H n) as Heq.
      rewrite H0 in Heq. simpl in Heq. 
      rewrite Heq. apply count_insert_other. 
      Locate Nat.eqb_refl.  apply Nat.eqb_neq in H0. intros contra. 
      symmetry in contra. apply H0 in contra. inversion contra. 
Qed.
   
Theorem bag_eqv_iff_perm:
  forall al bl, bag_eqv al bl <-> Permutation al bl.
Proof.
  intros. split. apply bag_perm. apply perm_bag.
Qed.

Corollary sort_specifications_equivalent:
    forall sort, is_a_sorting_algorithm sort <-> is_a_sorting_algorithm' sort.
Proof.
  unfold is_a_sorting_algorithm, is_a_sorting_algorithm'.
  split; intros;
  destruct (H al); split; auto;
  apply bag_eqv_iff_perm; auto.
Qed.


 