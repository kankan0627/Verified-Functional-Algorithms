From VFA Require Import Perm.
From VFA Require Import Sort.
From Coq Require Import Recdef.

Fixpoint split {X:Type} (l:list X) : (list X * list X) :=
  match l with
  | [] => ([],[])
  | [x] => ([x],[])
  | x1::x2::l' =>
    let (l1,l2) := split l' in
    (x1::l1,x2::l2)
  end.

Print split.

Definition list_ind2_principle:=
    forall (A : Type) (P : list A -> Prop),
      P [] ->
      (forall (a:A), P [a]) ->
      (forall (a b : A) (l : list A), P l -> P (a :: b :: l)) ->
      forall l : list A, P l.


Lemma split_len': list_ind2_principle ->
    forall {X} (l:list X) (l1 l2: list X),
    split l = (l1,l2) ->
    length l1 <= length l /\
    length l2 <= length l.
Proof.
  unfold list_ind2_principle; intro IP.
  induction l using IP; intros.
  - inv H. lia.
  - inv H. simpl; lia.
  - inv H. destruct (split l) as [l1' l2']. inv H1.
    simpl.
    destruct (IHl l1' l2') as [P1 P2]; auto; lia.
Qed.

Definition list_ind2 :
  forall (A : Type) (P : list A -> Prop),
      P [] ->
      (forall (a:A), P [a]) ->
      (forall (a b : A) (l : list A), P l -> P (a :: b :: l)) ->
      forall l : list A, P l :=
  fun (A : Type)
      (P : list A -> Prop)
      (H : P [])
      (H0 : forall a : A, P [a])
      (H1 : forall (a b : A) (l : list A), P l -> P (a :: b :: l)) =>
    fix IH (l : list A) : P l :=
    match l with
    | [] => H
    | [x] => H0 x
    | x::y::l' => H1 x y l' (IH l')
    end.

Lemma split_len: forall {X} (l:list X) (l1 l2: list X),
    split l = (l1,l2) ->
    length l1 <= length l /\
    length l2 <= length l.
Proof.
 apply (@split_len' list_ind2).
Qed.

Lemma split_perm : forall {X:Type} (l l1 l2: list X),
    split l = (l1,l2) -> Permutation l (l1 ++ l2).
Proof.
  induction l as [| x | x1 x2 l1' IHl'] using list_ind2; intros.
  - simpl in H. inversion H. simpl. apply perm_nil.
  - simpl in H. inversion H. simpl. apply Permutation_refl. 
  - simpl in H. destruct (split l1') as [lx ly]. inv H.
    simpl. apply perm_skip. apply Permutation_cons_app.  
    apply IHl'. auto.
Qed.

Fixpoint merge l1 l2 {struct l1} :=
  let fix merge_aux l2 :=
  match l1, l2 with
  | [], _ => l2
  | _, [] => l1
  | a1::l1', a2::l2' =>
      if a1 <=? a2 then a1 :: merge l1' l2 else a2 :: merge_aux l2'
  end
  in merge_aux l2.
 
Lemma merge2 : forall (x1 x2:nat) r1 r2,
    x1 <= x2 ->
    merge (x1::r1) (x2::r2) =
    x1::merge r1 (x2::r2).
Proof.
  intros. simpl. destruct (x1 <=? x2) eqn:Heq. 
  - auto.
  - apply Nat.leb_nle in Heq. 
    apply Heq in H. inversion H. 
Qed.

Lemma merge_nil_l : forall l, merge [] l = l.
Proof.
  intros.  simpl. induction l; auto.
Qed.

Function mergesort (l: list nat) {measure length l} : list nat :=
  match l with
  | [] => []
  | [x] => [x]
  | _ => let (l1,l2) := split l in
         merge (mergesort l1) (mergesort l2)
  end.
Proof.
  - intros. simpl in teq1. destruct (split l1) as [lx ly] eqn:E;
    inversion teq1; apply split_len in E; simpl; destruct E; lia.
  - intros. simpl in teq1. destruct (split l1) as [lx ly] eqn:E.
     inversion teq1. simpl. apply split_len in E. destruct E. lia. 
Defined. 

Check mergesort_equation.

Lemma sorted_merge1 : forall x x1 l1 x2 l2,
    x <= x1 -> x <= x2 ->
    sorted (merge (x1::l1) (x2::l2)) ->
    sorted (x :: merge (x1::l1) (x2::l2)).
Proof.
  intros. simpl in *. destruct (x1 <=? x2) eqn:Heq.
  - apply sorted_cons. 
    + apply H. 
    + apply H1. 
  - apply sorted_cons. 
    + apply H0. 
    +  apply H1.
Qed.
      

Lemma sorted_merge : forall l1, sorted l1 ->
                     forall l2, sorted l2 ->
                     sorted (merge l1 l2).
Proof. 
  induction l1.  
  - intros H. induction l2.
    + intros. simpl. apply H. 
    + intros. simpl. apply H0. 
  - intros H. intros. induction l2. 
    + simpl. apply H. 
    + simpl. destruct (a <=? a0) eqn:Heq.
      * induction l1. 
        -- simpl. apply sorted_cons. 
           ++ apply Nat.leb_le in Heq. apply Heq. 
           ++ apply H0.  
        -- apply sorted_merge1. 
           ++ inversion H.  apply H3.
           ++ apply Nat.leb_le. apply Heq.
           ++ apply IHl1. inversion H.
              ** apply H5. 
              ** apply H0.
       * destruct l2. 
         -- apply sorted_cons. 
           ++ Search "<=?".  apply leb_iff_conv in Heq. lia. 
           ++ apply H. 
         -- simpl in IHl2.  destruct (a <=? n) eqn:Hn.
            ++ apply sorted_cons. 
               ** apply leb_iff_conv in Heq. lia.
               ** apply IHl2.
                   inversion H0. apply H5. 
            ++ apply sorted_cons. 
               ** inversion H0. apply H3. 
               ** apply IHl2. inversion H0. apply H5.
Qed.

Lemma mergesort_sorts: forall l, sorted (mergesort l).
Proof.
  apply mergesort_ind; intros.
  - apply sorted_nil. 
  - apply sorted_1. 
  - apply sorted_merge.
    + apply H.
    + apply H0. 
Qed.

Lemma merge_perm: forall (l1 l2: list nat),
    Permutation (l1 ++ l2) (merge l1 l2).
Proof.
  induction l1.
  - simpl. destruct l2. 
    + apply perm_nil. 
    + apply Permutation_refl. 
  - induction l2. 
    + simpl. rewrite app_nil_r. apply Permutation_refl. 
    + simpl. destruct (a <=? a0) eqn:Heq.
      * apply perm_skip. apply IHl1. 
      * simpl in IHl2.  destruct l2.  
        -- apply perm_trans with (l1++a::[a0]).
           ++ apply Permutation_middle.
           ++ replace (a0 :: a :: l1) with ([a0] ++ a :: l1) by auto. apply Permutation_elt.
              apply Permutation_app_comm. 
        -- destruct (a <=? n) eqn:Hn.  
           ++ simpl. apply perm_trans with (a0::a :: l1 ++ n :: l2).  
              ** replace (a :: l1 ++ a0 :: n :: l2) with ([a] ++ l1 ++ [a0] ++ [n] ++ l2) by auto. 
                 replace (a0 :: a :: l1 ++ n :: l2)  with ([a0] ++ [a] ++ l1 ++ [n] ++ l2) by auto. 
                 assert ([a] ++ l1 ++ [a0] ++ [n] ++ l2 = ([a] ++ l1 ++ [a0]) ++ ([n] ++ l2)).
                 --- rewrite <- app_assoc. rewrite <- app_assoc. auto.
                 ---  assert ([a0] ++ [a] ++ l1 ++ [n] ++ l2 = ([a0] ++ [a] ++ l1) ++ ([n] ++ l2)).
                     +++ rewrite <- app_assoc. rewrite <- app_assoc. auto.
                     +++ rewrite H. rewrite H0.  apply Permutation_app_tail. apply perm_trans with  ([a] ++ [a0] ++ l1).
                         *** apply perm_skip.  apply Permutation_app_comm.
                         *** apply perm_swap. 
             ** apply perm_skip. apply IHl2.   
            ++ apply perm_trans with (a0::a :: l1 ++ n :: l2). 
               ** replace (a :: l1 ++ a0 :: n :: l2) with ([a] ++ l1 ++ [a0] ++ [n] ++ l2) by auto. 
                 replace (a0 :: a :: l1 ++ n :: l2)  with ([a0] ++ [a] ++ l1 ++ [n] ++ l2) by auto. 
                 assert ([a] ++ l1 ++ [a0] ++ [n] ++ l2 = ([a] ++ l1 ++ [a0]) ++ ([n] ++ l2)).
                 --- rewrite <- app_assoc. rewrite <- app_assoc. auto.
                 ---  assert ([a0] ++ [a] ++ l1 ++ [n] ++ l2 = ([a0] ++ [a] ++ l1) ++ ([n] ++ l2)).
                     +++ rewrite <- app_assoc. rewrite <- app_assoc. auto.
                     +++ rewrite H. rewrite H0.  apply Permutation_app_tail. apply perm_trans with  ([a] ++ [a0] ++ l1).
                         *** apply perm_skip.  apply Permutation_app_comm.
                         *** apply perm_swap. 
               **  apply perm_skip. apply IHl2. 
Qed.

Lemma mergesort_perm: forall l, Permutation l (mergesort l).
Proof.
   apply mergesort_ind; intros.
   - apply perm_nil.
   - apply Permutation_refl.
   - subst _x. apply perm_trans with ((mergesort l1) ++ (mergesort l2)). 
     + apply perm_trans with (l1 ++ l2).
       * apply split_perm.  auto.
       * Search Permutation. apply Permutation_app. 
         -- apply H. 
         -- apply H0. 
     + apply merge_perm. 
Qed.



Theorem mergesort_correct:
  is_a_sorting_algorithm mergesort.
Proof.
  split.
  apply mergesort_perm.
  apply mergesort_sorts.
Qed.

 


 
