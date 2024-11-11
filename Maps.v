From Coq Require Import Bool.Bool.
From Coq Require Import Logic.FunctionalExtensionality.
From VFA Require Import Perm.

Definition total_map (A : Type) : Type := nat -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A : Type} (m : total_map A) (x : nat) (v : A) : total_map A :=
  fun x' => if x =? x' then v else m x'.

Definition examplemap :=
  t_update (t_update (t_empty false) 1 false) 3 true.

Example update_example1 : examplemap 0 = false.
Proof.
 unfold examplemap.
 unfold t_update. simpl. unfold t_empty. auto. 
Qed.

Example update_example2 : examplemap 1 = false.
Proof.
 unfold examplemap.
 unfold t_update. simpl. auto. 
Qed.

Example update_example3 : examplemap 2 = false.
Proof.
 unfold examplemap.
 unfold t_update. simpl. unfold t_empty. auto. 
Qed.


Example update_example4 : examplemap 3 = true. 
Proof.
 unfold examplemap.
 unfold t_update. simpl. auto. 
Qed.

Lemma t_apply_empty: forall A x v, @t_empty A v x = v.
Proof.
  intros. unfold t_empty. auto.
Qed.

Lemma t_update_eq : forall A (m: total_map A) x v,
  (t_update m x v) x = v.
Proof.
  intros. unfold t_update. 
  simpl. rewrite Nat.eqb_refl. auto.
Qed.

Theorem t_update_neq : forall (X:Type) v x1 x2 (m : total_map X),
  x1 <> x2 -> (t_update m x1 v) x2 = m x2.
Proof.
  intros. unfold t_update. rewrite <- Nat.eqb_neq in H.
  rewrite H. auto. 
Qed.

Lemma t_update_shadow : forall A (m: total_map A) v1 v2 x,
    t_update (t_update m x v1) x v2
  = t_update m x v2.
Proof.
  intros. unfold t_update. apply functional_extensionality. 
  intros. destruct (x =? x0) eqn:Hn; auto.
Qed.

Theorem t_update_same : forall X x (m : total_map X),
  t_update m x (m x) = m.
Proof.
  intros. apply functional_extensionality. 
  intros. unfold t_update. destruct (x =? x0) eqn:Hn.
  - rewrite Nat.eqb_eq in Hn. subst. auto.
  - auto. 
Qed.

Theorem t_update_permute : forall (X:Type) v1 v2 x1 x2
                             (m : total_map X),
  x2 <> x1 ->
    (t_update (t_update m x2 v2) x1 v1)
  = (t_update (t_update m x1 v1) x2 v2).
Proof.
  intros. apply functional_extensionality. 
  intros. unfold t_update. destruct (x1 =? x) eqn:H1.
  - destruct (x2 =? x) eqn:H2.
    + rewrite Nat.eqb_eq in H1.  rewrite Nat.eqb_eq in H2. subst. 
      assert (x=x). 
      * auto. 
      * apply H in H0. inversion H0. 
    + auto. 
  - auto. 
Qed.

Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A := t_empty None.

Definition update {A : Type} (m : partial_map A) (x : nat) (v : A) : partial_map A :=
  t_update m x (Some v). 

Lemma apply_empty : forall A x, @empty A x = None.
Proof. 
  intros. unfold empty. unfold t_empty. auto.
Qed. 

Lemma update_eq : forall A (m: partial_map A) x v,
  (update m x v) x = Some v.
Proof.
  intros.
  unfold update. 
  unfold t_update. 
  rewrite Nat.eqb_refl. auto.
Qed. 

Theorem update_neq : forall (X:Type) v x1 x2 (m : partial_map X),
  x2 <> x1 -> (update m x2 v) x1 = m x1.
Proof.
 intros.
 unfold update. 
  unfold t_update. 
  rewrite <- Nat.eqb_neq in H.
  rewrite H. auto.
Qed. 

Lemma update_shadow : forall A (m: partial_map A) v1 v2 x,
  update (update m x v1) x v2 = update m x v2.
Proof.
intros.
 unfold update. 
  unfold t_update. 
apply functional_extensionality. 
intros. destruct (x =? x0) eqn:H0; auto. 
Qed. 

Theorem update_same : forall X v x (m : partial_map X),
  m x = Some v -> update m x v = m.
Proof.
intros.
 unfold update. 
  unfold t_update. 
apply functional_extensionality. 
intros. destruct (x =? x0) eqn:H0; auto. 
apply Nat.eqb_eq in H0. subst. auto. 
Qed. 

Theorem update_permute : forall (X:Type) v1 v2 x1 x2 (m : partial_map X),
  x2 <> x1 ->
    (update (update m x2 v2) x1 v1)
  = (update (update m x1 v1) x2 v2).
Proof.
intros.
 unfold update. 
  unfold t_update. 
apply functional_extensionality. 
intros. destruct (x1 =? x) eqn:H1.
 - destruct (x2 =? x) eqn:H2.
    + rewrite Nat.eqb_eq in H1.  rewrite Nat.eqb_eq in H2. subst. 
      assert (x=x). 
      * auto. 
      * apply H in H0. inversion H0. 
    + auto. 
  - auto.  
Qed.



