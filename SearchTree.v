Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import String.  
From Coq Require Import Logic.FunctionalExtensionality.
From VFA Require Import Perm.
From VFA Require Import Maps.
From VFA Require Import Sort.

Definition key := nat.

Inductive tree (V : Type) : Type :=
| E
| T (l : tree V) (k : key) (v : V) (r : tree V).

Arguments E {V}.
Arguments T {V}.

Definition ex_tree : tree string :=
  (T (T E 2 "two" E) 4 "four" (T E 5 "five" E))%string.

Definition empty_tree {V : Type} : tree V := E.

Fixpoint bound {V : Type} (x : key) (t : tree V) :=
  match t with
  | E => false
  | T l y v r => if x <? y then bound x l
                else if x >? y then bound x r
                     else true
  end.

Fixpoint lookup {V : Type} (d : V) (x : key) (t : tree V) : V :=
  match t with
  | E => d
  | T l y v r => if x <? y then lookup d x l
                else if x >? y then lookup d x r
                     else v
  end.

Fixpoint insert {V : Type} (x : key) (v : V) (t : tree V) : tree V :=
  match t with
  | E => T E x v E
  | T l y v' r => if x <? y then T (insert x v l) y v' r
                  else if x >? y then T l y v' (insert x v r)
                  else T l x v r
  end.

Module Tests.

Open Scope string_scope.

  Example bst_ex1 :
    insert 5 "five" (insert 2 "two" (insert 4 "four" empty_tree)) = ex_tree.
  Proof. reflexivity. Qed.

  Example bst_ex2 : lookup "" 5 ex_tree = "five".
  Proof. reflexivity. Qed.

  Example bst_ex3 : lookup "" 3 ex_tree = "".
  Proof. reflexivity. Qed.
 
  Example bst_ex4 : bound 3 ex_tree = false.
  Proof. reflexivity. Qed.

End Tests.

Module NotBst.

Open Scope string_scope.

Definition t : tree string :=
    T (T E 5 "five" E) 4 "four" (T E 2 "two" E).


Example not_bst_lookup_wrong :
    lookup "" 2 t <> "two".
Proof.
  simpl. intros contra. inversion contra. 
Qed.

End NotBst.

Fixpoint ForallT {V : Type} (P: key -> V -> Prop) (t: tree V) : Prop :=
  match t with
  | E => True
  | T l k v r => P k v /\ ForallT P l /\ ForallT P r
  end.

Inductive BST {V : Type} : tree V -> Prop :=
| BST_E : BST E
| BST_T : forall l x v r,
    ForallT (fun y _ => y < x) l ->
    ForallT (fun y _ => y > x) r ->
    BST l ->
    BST r ->
    BST (T l x v r).

Hint Constructors BST : core.

Example is_BST_ex :
  BST ex_tree.
Proof.
 unfold ex_tree. apply BST_T. 
  - simpl. auto. 
  - simpl. auto.
  - apply BST_T. 
    + simpl. auto. 
    + simpl. auto.
    + apply BST_E. 
    + apply BST_E. 
  - apply BST_T. 
    + simpl. auto. 
    + simpl. auto.
    + apply BST_E. 
    + apply BST_E. 
Qed.

Example not_BST_ex :
  ~ BST NotBst.t.
Proof.
  intros contra. 
  unfold NotBst.t in contra. 
  inversion contra. 
  simpl in H3. destruct H3. Search "<". lia. 
Qed. 

Theorem empty_tree_BST : forall (V : Type),
    BST (@empty_tree V).
Proof.
  intros. 
  unfold empty_tree. 
  apply BST_E. 
Qed.

Lemma ForallT_insert : forall (V : Type) (P : key -> V -> Prop) (t : tree V),
    ForallT P t -> forall (k : key) (v : V),
      P k v -> ForallT P (insert k v t).
Proof.
  intros. induction t.
  - simpl. auto. 
  - simpl. destruct (k <? k0) eqn:Heq. 
    + simpl. inversion H. split. 
      *  apply H1. 
      * destruct H2. apply IHt1 in H2. split.
        -- apply H2. 
        -- apply H3. 
    + apply Nat.ltb_ge in  Heq. destruct (k >? k0) eqn:Hek.
      * simpl. inversion H. split. 
        -- apply H1. 
        -- destruct H2. apply IHt2 in H3. split.
           ++ apply H2. 
           ++ apply H3.
      * simpl. inversion H. destruct H2. 
        split.
        -- apply H0. 
        -- split. 
           ++ apply H2. 
           ++ apply H3. 
Qed. 
 
Theorem insert_BST : forall (V : Type) (k : key) (v : V) (t : tree V),
    BST t -> BST (insert k v t).
Proof.
   intros. 
   generalize dependent k. generalize dependent v. 
   induction H. 
   - intros. simpl. apply BST_T. 
     + simpl. auto. 
     + simpl. auto. 
     + apply BST_E. 
     + apply BST_E. 
   - simpl. intros. destruct (k <? x) eqn:Heq.
     + apply BST_T. 
       * apply ForallT_insert.  
         -- apply H. 
         -- apply Nat.ltb_lt in Heq.  apply Heq. 
       * apply H0. 
       * apply IHBST1. 
       * apply H2. 
     + destruct (k >? x) eqn:Hek.
       * apply BST_T. 
         -- apply H. 
         -- apply ForallT_insert.
            ++ apply H0. 
            ++ Search ">?".  Search reflect. 
               specialize (gtb_reflect k x).  intros. apply reflect_iff in H3.
               apply H3 in Hek. apply Hek. 
         -- apply H1. 
         -- apply IHBST2. 
       * apply BST_T.
         -- specialize (gtb_reflect k x).  intros. Search reflect. rewrite Hek in H3.
            inversion H3. Search "<?". apply Nat.ltb_ge in Heq. Search ">". apply not_gt in H4.
            assert (x = k).
            ++ lia. 
            ++ subst. apply H. 
         -- specialize (gtb_reflect k x).  intros. Search reflect. rewrite Hek in H3.
            inversion H3. Search "<?". apply Nat.ltb_ge in Heq. Search ">". apply not_gt in H4.
            assert (x = k).
            ++ lia. 
            ++ subst. apply H0.
         -- apply H1. 
         -- apply H2. 
Qed.  
         
Theorem lookup_empty : forall (V : Type) (d : V) (k : key),
    lookup d k empty_tree = d.
Proof.
  intros. simpl. auto.
Qed.

Theorem lookup_insert_eq : forall (V : Type) (t : tree V) (d : V) (k : key) (v : V),
    lookup d k (insert k v t) = v.
Proof.
  intros. induction t.  
  - simpl. destruct (k <? k) eqn:Hkk.
    + rewrite Nat.ltb_irrefl in Hkk. inversion Hkk. 
    + destruct (k >? k) eqn:Hk.
      *  Search ">".  specialize (gtb_reflect k k).  intros. apply reflect_iff in H.
               apply H in Hk. apply Arith_prebase.gt_irrefl_stt in Hk. inversion Hk. 
      * auto. 
  - simpl. destruct (k <? k0) eqn:Hkk0.
    + simpl. rewrite Hkk0. apply IHt1. 
    + destruct (k >? k0) eqn:Heq.
      * simpl. rewrite Hkk0. rewrite Heq. apply IHt2. 
      * simpl.  destruct (k <? k) eqn:Hkk.
        -- rewrite Nat.ltb_irrefl in Hkk. inversion Hkk. 
        -- destruct (k >? k) eqn:Hk.
           ++  specialize (gtb_reflect k k).  intros. apply reflect_iff in H.
               apply H in Hk. apply Arith_prebase.gt_irrefl_stt in Hk. inversion Hk. 
      ++ auto.
Qed. 

























