Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String. 
From Coq Require Export Bool.Bool.
From Coq Require Export Arith.Arith.
From Coq Require Export Arith.PeanoNat.
From Coq Require Export Arith.EqNat.
From Coq Require Export Lia.
From Coq Require Export Lists.List.
Export ListNotations.
From Coq Require Export Permutation.

Locate "_ < _". (* "x < y" := lt x y *)
Check lt.

Locate "_ <? _". (* x <? y  := Nat.ltb x y *)
Check Nat.ltb : nat -> nat -> bool.

Check Nat.ltb_lt.

Print Nat.lt.

Definition geb (n m : nat) := m <=? n.
Hint Unfold geb : core.
Infix ">=?" := geb (at level 70) : nat_scope.

Definition gtb (n m : nat) := m <? n.
Hint Unfold gtb : core.
Infix ">?" := gtb (at level 70) : nat_scope.

Theorem lia_example1:
 forall i j k,
    i < j ->
    ~ (k - 3 <= j) ->
   k > i.
Proof.
  intros.  
  Search (~ _ <= _ -> _).
  apply not_le in H0.
  unfold gt in H0.
  unfold gt.
  Search (_ < _ -> _ < _ -> _ < _).
  apply Nat.lt_trans with j.
  apply H.
  apply Nat.lt_trans with (k-3).
  apply H0.
  (* Is k greater than k-3? On the integers, sure. But we're working
     with natural numbers, which truncate subtraction at zero. *)
Abort.

Theorem truncated_subtraction: ~ (forall k:nat, k > k - 3).
Proof.
 intros contra. 
 specialize (contra 0).
 simpl in contra.
 inversion contra.
Qed.

Theorem lia_example1:
 forall i j k,
    i < j ->
    ~ (k - 3 <= j) ->
   k > i.
Proof. 
  intros.
  apply not_le in H0. 
  unfold gt in H0.
  unfold gt.
  Search (_ < _ -> _ <= _ -> _ < _).
  apply Nat.lt_le_trans with j.
  apply H.
  apply Nat.le_trans with (k-3).
  Search (_ < _ -> _ <= _).
  apply Nat.lt_le_incl.
  auto. 
  apply Nat.le_sub_l.
Qed.

Theorem lia_example2:
forall i j k,
    i < j ->
    ~ (k - 3 <= j) ->
   k > i.
Proof. 
  intros.
  lia.
Qed.

Theorem lia_example_3 : forall (f : nat -> nat -> nat) a b x y,
    f x y > a * b -> f x y + 3 >= a * b.
Proof.
  intros. lia.
Qed.

Definition maybe_swap (al: list nat) : list nat :=
  match al with
  | a :: b :: ar => if a >? b then b :: a :: ar else a :: b :: ar
  | _ => al
  end.

Example maybe_swap_123:
  maybe_swap [1; 2; 3] = [1; 2; 3].
Proof. reflexivity. Qed.

Example maybe_swap_321:
  maybe_swap [3; 2; 1] = [2; 3; 1].
Proof. reflexivity. Qed.

Theorem maybe_swap_idempotent: forall al,
    maybe_swap (maybe_swap al) = maybe_swap al.
Proof.
  induction al. 
  - simpl. auto. 
  - simpl. destruct al. 
    + simpl.  auto. 
    + destruct (a >? n) eqn:Hn.
      * simpl. unfold gtb in Hn. unfold gtb.
        destruct (a <? n) eqn:Hnn.
        -- apply Nat.ltb_lt in Hn. apply Nat.ltb_lt in Hnn.
           assert (n<n).
           ++ apply Nat.lt_trans with a.
              ** apply Hn.  
              ** apply Hnn. 
           ++ apply Nat.lt_irrefl in H. inversion H.
        -- auto. 
       * simpl. rewrite Hn. auto. 
Qed.
          

Lemma eqb_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
 intros. apply iff_reflect. 
 split. 
 - intros. subst. apply Nat.eqb_eq. auto. 
 - intros. apply Nat.eqb_eq in H. auto.
Qed.  

Lemma ltb_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
intros. apply iff_reflect. split.
 - intros. apply Nat.ltb_lt. apply H. 
 - intros. apply Nat.ltb_lt in H. auto.
Qed. 

Lemma leb_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
intros. apply iff_reflect. split.
  - intros. apply Nat.leb_le. apply H. 
  - intros. apply Nat.leb_le in H. apply H.
Qed.  

Lemma gtb_reflect : forall x y, reflect (x > y) (x >? y).
Proof.
intros. apply iff_reflect. split.
  - intros. apply Nat.ltb_lt. auto.  
  - intros. apply Nat.ltb_lt in H. apply H.
Qed.

Lemma geb_reflect : forall x y, reflect (x >= y) (x >=? y).
Proof.
intros. apply iff_reflect. split.
  - intros. apply Nat.leb_le. apply H. 
  - intros. apply Nat.leb_le. apply H. 
Qed.

Example reflect_example1: forall a,
    (if a <? 5 then a else 2) < 6.
Proof.
 intros.
 specialize ltb_reflect with (x:=a) (y:=5).
 intros. destruct H eqn:Heq; lia. 
Qed. 

Hint Resolve ltb_reflect leb_reflect gtb_reflect geb_reflect eqb_reflect : bdestruct.

Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [ auto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply not_lt in H | apply not_le in H]]].

Example reflect_example2: forall a,
    (if a <? 5 then a else 2) < 6.
Proof.
  intros.
  bdestruct (a <? 5);
  lia.
Qed.

Theorem maybe_swap_idempotent_ref: forall al,
    maybe_swap (maybe_swap al) = maybe_swap al.
Proof.
  induction al.
  - simpl. auto. 
  - simpl. destruct al. 
    + auto. 
    + bdestruct (a >? n).
      * simpl.  bdestruct (n >? a).
        -- lia.
        -- auto.
      * simpl. bdestruct (a >? n).
        -- lia.
        -- auto.
Qed. 


Example butterfly: forall b u t e r f l y : nat,
  Permutation ([b;u;t;t;e;r]++[f;l;y]) ([f;l;u;t;t;e;r]++[b;y]).
Proof.
  intros.
  eapply Permutation_trans. 
  - apply Permutation_app_comm. 
  - apply Permutation_elt. 
    apply perm_skip. 
    apply perm_skip. 
    apply Permutation_cons_append. 
Qed.

Example butterfly_sample: forall b u t e r f l y : nat,
  Permutation ([b;u;t;t;e;r]++[f;l;y]) ([f;l;u;t;t;e;r]++[b;y]).
Proof.
   intros.
   change [b;u;t;t;e;r] with ([b]++[u;t;t;e;r]).
   change [f;l;u;t;t;e;r] with ([f;l]++[u;t;t;e;r]).
   remember [u;t;t;e;r] as utter. clear Hequtter.
   change [f;l;y] with ([f;l]++[y]).
   remember [f;l] as fl. clear Heqfl.
   replace ((fl ++ utter) ++ [b;y]) with (fl ++ utter ++ [b;y])
   by apply app_assoc.
  apply perm_trans with (fl ++ [y] ++ ([b] ++ utter)).
  - replace (fl ++ [y] ++ [b] ++ utter) with ((fl ++ [y]) ++ [b] ++ utter).
    + apply Permutation_app_comm.
    + rewrite <- app_assoc. reflexivity.
  - apply Permutation_app_head.
    apply perm_trans with (utter ++ [y] ++ [b]).
    + replace ([y] ++ [b] ++ utter) with (([y] ++ [b]) ++ utter).
      * apply Permutation_app_comm.
      * rewrite app_assoc. reflexivity.
    + apply Permutation_app_head.
      apply perm_swap.
Qed.

Check perm_skip.
Check perm_trans.
Check Permutation_refl. 
Check Permutation_app_comm.  
Check app_assoc. 
Check app_nil_r.
Check app_comm_cons.


Example permut_example: forall (a b: list nat),
  Permutation (5 :: 6 :: a ++ b) ((5 :: b) ++ (6 :: a ++ [])).
Proof.
  intros.
  replace  ((5 :: b) ++ 6 :: a ++ []) with  (5 :: b ++ 6 :: a ++ []).
  -  apply perm_skip. rewrite app_nil_r. rewrite app_comm_cons.
     apply Permutation_app_comm.
  -  rewrite <- app_comm_cons. auto. 
Qed.
 
Check Permutation_cons_inv. 
Check Permutation_length_1_inv.

Example not_a_permutation:
   ~ Permutation [1;1] [1;2].
Proof.
  intros contra. 
   apply Permutation_cons_inv in contra. 
   apply Permutation_length_1_inv in contra.
   inversion contra. 
Qed.

Theorem maybe_swap_perm: forall al,
  Permutation al (maybe_swap al).
Proof.
  induction al. 
  - simpl. apply perm_nil. 
  - simpl. induction al. 
    + apply Permutation_refl. 
    + bdestruct (a >? a0).
      * apply perm_swap. 
      * apply Permutation_refl. 
Qed.


Definition first_le_second (al: list nat) : Prop :=
  match al with
  | a :: b :: _ => a <= b
  | _ => True
  end.
Theorem maybe_swap_correct: forall al,
    Permutation al (maybe_swap al) /\ first_le_second (maybe_swap al).
Proof.
 intros. 
 induction al. 
 - simpl. split. 
   + apply perm_nil. 
   + auto. 
 - split.
   + apply maybe_swap_perm. 
   + simpl. induction al. 
     * simpl. auto. 
     * bdestruct (a >? a0).
       -- simpl. lia. 
       -- simpl. auto. 
Qed.

Ltac inv H := inversion H; clear H; subst.

Theorem Forall_perm: forall {A} (f: A -> Prop) al bl,
  Permutation al bl ->
  Forall f al -> Forall f bl.
Proof.
  intros.  
  induction H. 
  - apply Forall_nil. 
  - apply Forall_cons. 
    + apply Forall_inv in H0. apply H0. 
    + apply IHPermutation. apply Forall_inv_tail in H0. apply H0. 
  - assert((y :: x :: l) = ([y]++x::l)).
    + auto. 
    + rewrite H in H0. apply Forall_cons.
      * apply Forall_elt in H0. apply H0.
      * apply Forall_cons. 
        -- apply Forall_inv in H0. apply H0.
        -- apply Forall_inv_tail in H0. apply Forall_inv_tail in H0. apply H0.
   - apply IHPermutation2.  apply IHPermutation1. apply H0. 
Qed.    




