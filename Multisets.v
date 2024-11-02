From Coq Require Import Strings.String.   
From Coq Require Import FunctionalExtensionality.
From VFA Require Import Perm.
From VFA Require Import Sort.

Definition value := nat.
Definition multiset := value -> nat.

Definition empty : multiset :=
  fun x => 0.

Definition singleton (v: value) : multiset :=
  fun x => if x =? v then 1 else 0.

Definition union (a b : multiset) : multiset :=
  fun x => a x + b x.

Lemma union_assoc: forall a b c : multiset,
   union a (union b c) = union (union a b) c.
Proof.
  intros.
  extensionality x.
  unfold union. lia. 
Qed.

Lemma union_comm: forall a b : multiset,
   union a b = union b a.
Proof.
  intros.
  extensionality x.
  unfold union. lia. 
Qed.

Lemma union_swap : forall a b c : multiset,
    union a (union b c) = union b (union a c).
Proof.
  intros. rewrite union_assoc. rewrite union_assoc. 
  rewrite (union_comm a b). auto.
Qed. 

Fixpoint contents (al: list value) : multiset :=
  match al with
  | [] => empty
  | a :: bl => union (singleton a) (contents bl)
  end.

Example sort_pi_same_contents:
  contents (sort [3;1;4;1;5;9;2;6;5;3;5]) = contents [3;1;4;1;5;9;2;6;5;3;5].
Proof.
  extensionality x.
  repeat (destruct x; try reflexivity).
Qed.

Definition is_a_sorting_algorithm' (f: list nat -> list nat) := forall al,
    contents al = contents (f al) /\ sorted (f al).

Lemma insert_contents: forall x l,
     contents (insert x l) = contents (x :: l).
Proof.
 intros x. 
 induction l. 
 - simpl. reflexivity.
 - simpl. bdestruct (x <=? a).
   + simpl. auto. 
   + simpl. rewrite IHl. simpl. rewrite union_swap. auto. 
Qed.

Theorem sort_contents: forall l,
    contents l = contents (sort l).
Proof.
  induction l.
  - simpl. reflexivity.
  - simpl. rewrite insert_contents. simpl. rewrite IHl. auto.
Qed.  

Theorem insertion_sort_correct :
  is_a_sorting_algorithm' sort.
Proof.
  unfold is_a_sorting_algorithm'. 
  induction al.
  - split.
    + simpl. reflexivity. 
    + simpl. apply sorted_nil. 
  - split. 
    + simpl. rewrite insert_contents. simpl. 
      destruct IHal. rewrite H. auto. 
    + simpl. apply insert_sorted. destruct IHal. apply H0.
Qed.

Lemma perm_contents: forall al bl : list nat,
    Permutation al bl -> contents al = contents bl.
Proof.
  intros. 
  induction H. 
  - reflexivity. 
  - simpl. rewrite IHPermutation. reflexivity. 
  - simpl. rewrite union_swap. reflexivity. 
  - transitivity (contents l'); auto. 
Qed. 

Lemma contents_nil_inv : forall l, (forall x, 0 = contents l x) -> l = nil.
Proof.
  intros. 
  induction l.
  - reflexivity. 
  - simpl in H. specialize H with a.
    unfold union in H. unfold singleton in H. rewrite Nat.eqb_refl in H. inversion H. 
Qed.   

Lemma contents_cons_inv : forall l x n,
    S n = contents l x ->
    exists l1 l2,
      l = l1 ++ x :: l2
      /\ contents (l1 ++ l2) x = n.
Proof.
  induction l. 
  - intros. simpl in H. inversion H. 
  - intros.  simpl in H. unfold union in H.  unfold singleton in H.    
    destruct (x =? a) eqn:Hn.  
    + simpl in H. inversion H. apply Nat.eqb_eq in Hn. subst. 
      exists []. exists l. split. 
      * auto. 
      * simpl. auto. 
    + simpl in H.  apply IHl in H. destruct H as [l1 [l2 H]]. 
      destruct H. subst. exists (a :: l1). exists l2. split.
      * auto. 
      * simpl. unfold union. unfold singleton. rewrite Hn. auto. 
Qed.

Lemma contents_insert_other : forall l1 l2 x y,
    y <> x -> contents (l1 ++ x :: l2) y = contents (l1 ++ l2) y.
Proof.
  induction l1.
  - intros. simpl. 
    unfold union.
    unfold singleton. 
    rewrite <- Nat.eqb_neq in H.
    rewrite H. auto. 
  - intros. simpl. eapply IHl1 in H.
    unfold union. rewrite H. auto.
Qed.

Lemma contents_perm: forall al bl,
    contents al = contents bl -> Permutation al bl.
Proof.   
  intros al bl H0.
  assert (H: forall x, contents al x = contents bl x).
  { rewrite H0. auto. }
  clear H0.
  generalize dependent bl.  
  induction al; simpl; intros bl Hc. 
  - unfold empty in Hc. apply contents_nil_inv in Hc. rewrite Hc.
    apply perm_nil. 
  - unfold union in Hc. unfold singleton in Hc.
    specialize (Hc a) as Hca.
    rewrite Nat.eqb_refl in Hca. apply contents_cons_inv in Hca.
    destruct Hca as [lb1 [lb2 [Elb Hca]]].
    rewrite Elb in *.  rewrite Permutation_app_comm.
    simpl. apply perm_skip. rewrite Permutation_app_comm.
    apply IHal. intros x. bdestruct (x =? a).
    + subst x. symmetry. apply Hca.
    + rewrite <- (contents_insert_other _ _ a x H).
      rewrite <- Hc. apply Nat.eqb_neq in H. rewrite H. reflexivity.
Qed.

Theorem same_contents_iff_perm: forall al bl,
    contents al = contents bl <-> Permutation al bl.
Proof.
  intros.
  split.  
  - apply contents_perm. 
  - apply perm_contents. 
Qed.          
 
Theorem sort_specifications_equivalent: forall sort,
    is_a_sorting_algorithm sort <-> is_a_sorting_algorithm' sort.
Proof.
  intros. 
  split. 
  - intros. unfold is_a_sorting_algorithm in H. 
    unfold is_a_sorting_algorithm'. intros. split. 
    + specialize (H al) as Ha. destruct Ha. 
      apply perm_contents in H0. apply H0. 
    + specialize (H al) as H. 
      destruct H. apply H0.
  - intros. unfold is_a_sorting_algorithm' in H.
    unfold is_a_sorting_algorithm. intros al. 
     specialize (H al) as Ha. destruct Ha. 
     split. 
     + apply contents_perm. apply H0. 
     + apply H1.
Qed. 








   