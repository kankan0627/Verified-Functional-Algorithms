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

   
