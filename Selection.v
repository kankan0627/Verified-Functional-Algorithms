Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From VFA Require Import Perm.
Hint Constructors Permutation : core.
From Coq Require Export Lists.List.

Fixpoint select (x: nat) (l: list nat) : nat * list nat :=
  match l with
  | [] => (x, [])
  | h :: t =>
    if x <=? h
    then let (j, l') := select x t
         in (j, h :: l')
    else let (j, l') := select h t
         in (j, x :: l')
  end.

Fail Fixpoint selsort (l : list nat) : list nat :=
  match l with
  | [] => []
  | x :: r => let (y, r') := select x r
            in y :: selsort r'
  end.

Fixpoint selsort (l : list nat) (n : nat) : list nat :=
  match l, n with
  | _, O => [] (* ran out of fuel *)
  | [], _ => []
  | x :: r, S n' => let (y, r') := select x r
                  in y :: selsort r' n'
end.

Example out_of_fuel: selsort [3;1;4;1;5] 3 <> [1;1;3;4;5].
Proof.
  simpl. intro. discriminate.
Qed.

Example extra_fuel: selsort [3;1;4;1;5] 10 = [1;1;3;4;5].
Proof.
  simpl. reflexivity.
Qed.

Definition selection_sort (l : list nat) : list nat :=
  selsort l (length l).

Example sort_pi :
  selection_sort [3;1;4;1;5;9;2;6;5;3;5] = [1;1;2;3;3;4;5;5;5;6;9].
Proof.
  unfold selection_sort.
  simpl. reflexivity.
Qed.

Inductive sorted: list nat -> Prop :=
 | sorted_nil: sorted []
 | sorted_1: forall i, sorted [i]
 | sorted_cons: forall i j l, i <= j -> sorted (j :: l) -> sorted (i :: j :: l).

Hint Constructors sorted : core.


Definition is_a_sorting_algorithm (f: list nat -> list nat) := forall al,
    Permutation al (f al) /\ sorted (f al).

Example pairs_example : forall (a c x : nat) (b d l : list nat),
    (a, b) = (let (c, d) := select x l in (c, d)) ->
    (a, b) = select x l.
Proof.
  intros. destruct (select x l) as [c' d'] eqn:E. auto.
Qed.

Lemma select_perm: forall x l y r,
    select x l = (y, r) -> Permutation (x :: l) (y :: r).
Proof.
 intros.
 generalize dependent x. generalize dependent y.
 generalize dependent r.
 induction l. 
 - intros. simpl in H. inversion H. subst. apply Permutation_refl.
 - intros. simpl in H. bdestruct (x <=? a). 
   + destruct (select x l) as [c' d'] eqn:E. inv H. eauto. 
   + destruct (select a l) as [c' d'] eqn:E. inv H. eauto. 
Qed.    

Lemma select_rest_length : forall x l y r,
    select x l = (y, r) -> length l = length r.
Proof.
  intros. apply select_perm in H. apply Permutation_length in H. 
  simpl in H. inv H. auto. 
Qed.
  
Lemma selsort_perm: forall n l,
    length l = n -> Permutation l (selsort l n).
Proof.
  induction n.
  - intros. simpl. destruct l.
    + apply perm_nil. 
    + inversion H. 
  - induction l.  
    + intros. inversion H.  
    + intros. simpl. destruct (select a l) as [c' d'] eqn:E. 
      apply select_perm in E. apply perm_trans with (c' :: d').
      * apply E.
      * apply perm_skip. apply IHn. 
      simpl in H. injection H. intros. apply Permutation_length in E.
      inversion E. apply H0.
Qed.  

Lemma selection_sort_perm: forall l,
    Permutation l (selection_sort l).
Proof.
   unfold selection_sort. 
   induction l. 
  - simpl. apply perm_nil. 
  - simpl. destruct (select a l) as [c' d'] eqn:E.  
    apply select_perm in E. apply perm_trans with (c' :: d').
    + apply E. 
    + apply perm_skip. apply selsort_perm.  
      apply Permutation_length in E. inversion E. auto. 
Qed.

Lemma select_fst_leq: forall al bl x y,
    select x al = (y, bl) ->
    y <= x.
Proof.
  induction al.
  - intros. simpl in H. inversion H. auto. 
  - intros. simpl in H. bdestruct (x <=? a). 
    + destruct (select x al) as [c' d'] eqn:E.  
      inversion H. subst. apply IHal in E. apply E. 
    + destruct (select a al) as [c' d'] eqn:E.
      inv H. apply IHal in E. lia. 
Qed.  

Definition le_all x xs := Forall (fun y => x <= y) xs.
Hint Unfold le_all : core.
Infix "<=*" := le_all (at level 70, no associativity).

Lemma le_all__le_one : forall lst y n,
    y <=* lst -> In n lst -> y <= n.
Proof.
  intros. unfold le_all in H. apply Forall_map in H. 
  rewrite map_id in H. Search In. generalize dependent n. Print le. 
   apply Forall_forall. apply H.
Qed. 
 
Lemma select_smallest: forall al bl x y,
    select x al = (y, bl) ->
    y <=* bl.
Proof.
 induction al.   
 - intros. unfold le_all. simpl in H. inversion H. apply Forall_nil. 
 - intros. unfold le_all. apply Forall_map.  
   rewrite map_id. simpl in H. bdestruct (x <=? a).  
   + destruct (select x al) as [c' d'] eqn:E.
     inversion H. subst. assert (select x al = (y, d')).
     * apply E. 
     * apply select_fst_leq in E. apply Forall_cons.
       -- lia. 
       -- apply IHal in H1. unfold le_all in H1.  
          apply Forall_map in H1. 
          rewrite map_id in H1. apply H1. 
   + destruct (select a al) as [c' d'] eqn:E. inversion H. 
     subst. apply Forall_cons. apply select_fst_leq in E.
     * lia. 
     * apply IHal in E. unfold le_all in E. apply Forall_map in E. 
       rewrite map_id in E. apply E. 
Qed.

Lemma select_in : forall al bl x y,
    select x al = (y, bl) ->
    In y (x :: al).
Proof.
  induction al.   
  - intros. simpl in H. inversion H. Search In. apply in_eq. 
  - intros. simpl. simpl in H. bdestruct (x <=? a).  
    + destruct (select x al) as [c' d'] eqn:E.
     inversion H. subst. apply IHal in E. simpl in E.
     destruct E. 
     * left. apply H1. 
     * right. right. apply H1. 
    + destruct (select a al) as [c' d'] eqn:E. inversion H. 
     subst. apply IHal in E. simpl in E.
     destruct E. 
     * right. left. apply H1. 
     * right. right. apply H1.
Qed. 

Lemma cons_of_small_maintains_sort: forall bl y n,
    n = length bl ->
    y <=* bl ->
    sorted (selsort bl n) ->
    sorted (y :: selsort bl n).
Proof.
  intros. destruct n. 
  - simpl. destruct bl.
    * apply sorted_1. 
    * apply sorted_1. 
  - simpl. destruct bl. 
    * apply sorted_1. 
    * simpl in H1. destruct (select n0 bl ) as [c' d'] eqn:E. 
      apply sorted_cons. 
      -- apply (le_all__le_one _ _ c') in H0.
         ++ apply H0. 
         ++ apply select_in in E. apply E. 
      -- apply H1. 
Qed.  

