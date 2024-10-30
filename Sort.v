Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From VFA Require Import Perm.

Fixpoint insert (i : nat) (l : list nat) :=
  match l with
  | [] => [i]
  | h :: t => if i <=? h then i :: h :: t else h :: insert i t
  end.

Fixpoint sort (l : list nat) : list nat :=
  match l with
  | [] => []
  | h :: t => insert h (sort t)
  end.

Example sort_pi :
  sort [3;1;4;1;5;9;2;6;5;3;5]
  = [1;1;2;3;3;4;5;5;5;6;9].
Proof. 
 simpl. auto. 
Qed.

Inductive sorted : list nat -> Prop :=
| sorted_nil :
    sorted []
| sorted_1 : forall x,
    sorted [x]
| sorted_cons : forall x y l,
    x <= y -> sorted (y :: l) -> sorted (x :: y :: l).

Check nth.
Check nth_error. 

Definition sorted'' (al : list nat) := forall i j,
    i < j < length al  ->  nth i al 0 <= nth j al 0.

Definition sorted' (al : list nat) := forall i j iv jv,
    i < j ->
    nth_error al i = Some iv ->
    nth_error al j = Some jv ->
    iv <= jv.

Definition is_a_sorting_algorithm (f: list nat -> list nat) := forall al,
    Permutation al (f al) /\ sorted (f al).

Lemma insert_sorted:
  forall a l, sorted l -> sorted (insert a l).
Proof.
 intros.   
 induction H.  
 - simpl. apply sorted_1. 
 - simpl. bdestruct (a <=? x). 
   +  apply sorted_cons. apply H. apply sorted_1. 
   + apply sorted_cons. 
     * lia. 
     * apply sorted_1. 
 - intros. simpl. bdestruct (a <=? x).  
   + apply sorted_cons. 
     * apply H1. 
     * apply sorted_cons. apply H. apply H0.
   + simpl in IHsorted.   bdestruct (a <=? y).
     * apply sorted_cons. 
       -- lia.
       -- apply IHsorted.
     * apply sorted_cons. 
       -- apply H. 
       -- apply IHsorted.
Qed.
      
Theorem sort_sorted: forall l, sorted (sort l).
Proof.
  induction l. 
  - simpl. apply sorted_nil.
  - simpl. apply insert_sorted. apply IHl.
Qed.

Lemma insert_perm: forall x l,
    Permutation (x :: l) (insert x l).
Proof.
  intros x.
  induction l. 
  - simpl. apply Permutation_refl.
  - simpl. bdestruct (x <=? a).
    + apply Permutation_refl.
    + replace (x :: a :: l) with ([x] ++ a :: l) by auto.
      replace (a :: insert x l) with ([] ++ a :: insert x l) by auto.
      apply Permutation_elt. simpl. apply IHl. 
Qed.
      
Theorem sort_perm: forall l, Permutation l (sort l).
Proof.
  induction l.        
  - simpl. apply perm_nil.
  - simpl. apply Permutation_trans with (a::(sort l)).
    + apply perm_skip. apply IHl. 
    + apply insert_perm.
Qed.

Theorem insertion_sort_correct:
    is_a_sorting_algorithm sort.
Proof.
  unfold is_a_sorting_algorithm. 
  intros. 
  split.
  - apply sort_perm. 
  - apply sort_sorted.
Qed.

Definition sorted_eq al  := 
  forall i j iv jv,
    i <= j ->
    nth_error al i = Some iv ->
    nth_error al j = Some jv ->
    iv <= jv.

Lemma sorted_eq_sorted' : forall al, sorted_eq al -> sorted' al.
Proof.
  intros al H i j iv jv Hl. 
  apply H. lia.
Qed.

Lemma sorted'_sorted_eq : forall al, sorted' al -> sorted_eq al.
Proof.
  intros al H i j iv jv Hl Hi Hj. 
  destruct (Nat.eq_dec i j).
  - rewrite e in Hi. rewrite Hi in Hj. inversion Hj. apply le_n.
  - apply (H i j); auto. lia.
Qed.

Lemma sorted_eq_nil : sorted_eq [].
Proof.
  intros i j iv jv _ Hi. destruct i; discriminate Hi.
Qed.

Lemma sorted_eq_1 : forall x, sorted_eq [x].
Proof.
  intros x i j iv jv Hl Hi Hj.
  destruct i; [| destruct i; discriminate Hi].
  destruct j; [| destruct j; discriminate Hj].
  inversion Hi. inversion Hj. lia.
Qed.

Lemma sorted_sorted_eq : forall al, sorted al -> sorted_eq al.
Proof.
  intros al Hs. induction Hs.
  - apply sorted_eq_nil.
  - apply sorted_eq_1.
  - intros i j iv jv Hl Hi Hj. destruct i; inversion Hi.
    + destruct j; inversion Hj.
      * lia.
      * subst iv. transitivity y.
          { assumption. }
          { apply (IHHs 0 j); auto. lia. }
      + destruct j.
        * lia.
        * apply (IHHs i j); auto. lia.
Qed.

Lemma sorted_sorted': forall al, sorted al -> sorted' al.
Proof.
  intros al H. exact (sorted_eq_sorted' _ (sorted_sorted_eq _ H)).
Qed.

Lemma sorted'_sorted : forall al, sorted' al -> sorted al.
Proof.
 induction al.   
 - intros. apply sorted_nil. 
 - intros. destruct al.  
   + apply sorted_1. 
   + apply sorted_cons.
     * eapply H. 
       -- assert (0 < 1).
          ++ lia.
          ++ apply H0. 
       -- simpl.  auto. 
       --  simpl. auto.
      * apply IHal. unfold sorted'. intros. 
        unfold sorted' in H. assert ((S i) < (S j)). 
        -- lia. 
        -- eapply H in H3.
           ++ apply H3. 
           ++ simpl. apply H1. 
           ++ simpl. apply H2. 
Qed. 

Lemma nth_error_insert : forall l a i iv,
    nth_error (insert a l) i = Some iv ->
    a = iv \/ exists i', nth_error l i' = Some iv.
Proof.
 induction l. 
 - intros. simpl in H. destruct i. 
   + simpl in H. injection H. intros. left. auto. 
   + simpl in H. right. exists i. auto.
 - intros. destruct i.
   + simpl in H. bdestruct (a0 <=? a).
     * injection H. intros. left. apply H1.
     * injection H. intros. subst. right. exists 0. simpl. auto.
   + simpl in H. bdestruct (a0 <=? a).
     * right. exists i. apply H. 
     * apply IHl in H. destruct H. 
       -- left. apply H.
       -- destruct H as [i' H].
          right. exists (S i'). simpl. apply H. 
Qed.

Lemma sorted_eq_cons : forall a b l,
  a <= b ->
  sorted_eq (b :: l) ->
  sorted_eq (a :: b :: l).
Proof.
  intros a b l Hab Hs i j iv jv Hl Hi Hj.
  destruct i; simpl in *.
  - injection Hi as Hi; subst iv.
    destruct j; simpl in *.
    + injection Hj as Hj; subst jv. apply le_n.
    + transitivity b. 
      * apply Hab.
      * unfold sorted_eq in Hs. apply (Hs 0 j); auto. lia.
  - destruct j; [lia |]. simpl in Hj.
    apply (Hs i j); auto. lia.
Qed.

Lemma sorted_eq_uncons : forall a l, sorted_eq (a :: l) -> sorted_eq l.
Proof.
  intros. unfold sorted_eq. intros. unfold sorted_eq in H.  
  apply (H (S i) (S j)); [lia | simpl; auto | simpl; auto].
Qed.
  
Lemma insert_sorted_eq : forall a l, sorted_eq l -> sorted_eq (insert a l).
Proof.
 intros. induction l. 
 - simpl. unfold sorted_eq. intros. destruct i.
   + simpl in H1. destruct j. 
     * simpl in H2. inversion H1. inversion H2. subst. auto. 
     * simpl in H2. destruct j. 
       -- simpl in H2. inversion H2.
       -- simpl in H2. inversion H2.
   + simpl in H1. destruct j.
     * inversion H0.
     * simpl in H2. apply (H i j); try lia; auto.
 - simpl. bdestruct (a <=? a0).
   + apply sorted_eq_cons. 
     * apply H0.
     * apply H.
   + unfold sorted_eq. intros.  
     * destruct i.  
       -- simpl in H2. destruct j. 
          ++ simpl in H3. inversion H2. inversion H3. subst. auto. 
          ++ simpl in H3. unfold sorted_eq in H.   
             apply nth_error_insert in H3. destruct H3.
             ** subst. inversion H2. subst. lia.
             ** destruct H3 as [k H3].
                apply (H 0 (S k)).
                --- lia.
                --- simpl. apply H2. 
                --- simpl. apply H3. 
        -- simpl in H2.  destruct j.
           ++ lia.
           ++ simpl in H3. apply sorted_eq_uncons in H. 
             apply IHl in H. 
              unfold sorted_eq in H. apply (H i j).
              ** lia. 
              ** apply H2.    
              ** apply H3. 
Qed.

Lemma insert_sorted':
  forall a l, sorted' l -> sorted' (insert a l).
Proof.
 intros. 
 apply sorted_eq_sorted'. 
  apply sorted'_sorted_eq in H.
  apply insert_sorted_eq. auto.
Qed.

Theorem sort_sorted': forall l, sorted' (sort l).
Proof.
  induction l. 
  - simpl. apply sorted_eq_sorted'. apply sorted_eq_nil. 
  - simpl. apply insert_sorted'. apply IHl. 
Qed. 


