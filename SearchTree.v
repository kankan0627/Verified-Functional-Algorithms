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
               apply H in Hk.  apply Arith_prebase.gt_irrefl_stt in Hk. inversion Hk. 
      ++ auto.
Qed. 

Ltac bdestruct_guard :=
  match goal with
  | |- context [ if ?X =? ?Y then _ else _ ] => bdestruct (X =? Y)
  | |- context [ if ?X <=? ?Y then _ else _ ] => bdestruct (X <=? Y)
  | |- context [ if ?X <? ?Y then _ else _ ] => bdestruct (X <? Y)
  | |- context [ if ?X >=? ?Y then _ else _ ] => bdestruct (X >=? Y)
  | |- context [ if ?X >? ?Y then _ else _ ] => bdestruct (X >? Y)
  end.


Ltac bdall :=
  repeat (simpl; bdestruct_guard; try lia; auto).

Theorem lookup_insert_eq' :
  forall (V : Type) (t : tree V) (d : V) (k : key) (v : V),
    lookup d k (insert k v t) = v.
Proof.
  induction t; intros; bdall.
Qed.

Theorem lookup_insert_neq :
  forall (V : Type) (t : tree V) (d : V) (k k' : key) (v : V),
   k <> k' -> lookup d k' (insert k v t) = lookup d k' t.
Proof. 
  induction t; intros; bdall.
Qed.

Theorem bound_default :
  forall (V : Type) (k : key) (d : V) (t : tree V),
    bound k t = false -> lookup d k t = d.
Proof.
  induction t.
  - intros. simpl. auto.
  - intros. bdall.
    + apply IHt1. inversion H. Search "<?". apply Nat.ltb_lt in H0. 
      rewrite H0. auto. 
    + apply IHt2. inversion H. Search "<?". apply Nat.ltb_ge in H0. 
      rewrite H0. specialize (gtb_reflect k k0).  intros. Search reflect. apply reflect_iff in H2.
      apply H2 in H1. rewrite H1. auto.
    + inversion H. apply Nat.ltb_ge in H0.  rewrite H0 in H3. destruct (k >? k0) eqn:Hk. 
      * specialize (gtb_reflect k k0). intros. apply reflect_iff in H2. apply H2 in Hk. 
        assert (k > k). { lia. } apply Arith_prebase.gt_irrefl_stt in H4. inversion H4. 
      * inversion H3. 
Qed.

Check lookup_empty. 
Check t_apply_empty. 
Check lookup_insert_eq.  
Check t_update_eq. 
Check lookup_insert_neq. 
Check t_update_neq. 
Check t_update_shadow.
Check t_update_same.
Check t_update_permute.

Lemma lookup_insert_shadow :
  forall (V : Type) (t : tree V) (v v' d: V) (k k' : key),
    lookup d k' (insert k v (insert k v' t)) = lookup d k' (insert k v t).
Proof.
  intros. bdestruct (k =? k').
  - subst k'. rewrite lookup_insert_eq.  rewrite lookup_insert_eq. auto.
  - assert (k <> k').
    + auto.
    + eapply lookup_insert_neq in H. rewrite H. 
      assert (k <> k').
      * auto.
      * eapply lookup_insert_neq in H1. rewrite H1. 
        eapply lookup_insert_neq in H0. rewrite H0.
        auto. 
Qed.

Lemma lookup_insert_same :
  forall (V : Type) (k k' : key) (d : V) (t : tree V),
    lookup d k' (insert k (lookup d k t) t) = lookup d k' t.
Proof. 
  intros. bdestruct (k =? k').
  - subst k'. rewrite lookup_insert_eq. auto.
  - eapply lookup_insert_neq in H. rewrite H. 
    auto. 
Qed.

Lemma lookup_insert_permute :
  forall (V : Type) (v1 v2 d : V) (k1 k2 k': key) (t : tree V),
    k1 <> k2 ->
    lookup d k' (insert k1 v1 (insert k2 v2 t))
    = lookup d k' (insert k2 v2 (insert k1 v1 t)).
Proof.
  intros. bdestruct (k1 =? k'). 
  - subst k'. assert (k2<>k1).
    + lia. 
    + eapply lookup_insert_neq in H0. rewrite H0. 
      rewrite lookup_insert_eq. rewrite lookup_insert_eq. auto. 
  - assert (k1 <> k').
    + lia. 
    + eapply lookup_insert_neq in H0. rewrite H0. bdestruct (k2 =? k').
      * subst k'. rewrite lookup_insert_eq. rewrite lookup_insert_eq. auto.
      * assert (k2 <> k'). 
      -- lia. 
      --  eapply lookup_insert_neq in H2. rewrite H2. 
        eapply lookup_insert_neq in H3.   rewrite H3.
        eapply lookup_insert_neq in H1. rewrite H1. auto.
Qed.     

Lemma insert_shadow_equality : forall (V : Type) (t : tree V) (k : key) (v v' : V),
    insert k v (insert k v' t) = insert k v t.
Proof.
  induction t; intros; bdall.
  - rewrite IHt1; auto.
  - rewrite IHt2; auto.
Qed.

Lemma insert_same_equality_breaks :
  exists (V : Type) (d : V) (t : tree V) (k : key),
      insert k (lookup d k t) t <> t.
Proof.
  exists string.
  exists EmptyString.
  exists (T (T E 5 "five"%string E) 4 "four"%string (T E 2 "two"%string E)).
  exists 2. 
  simpl. intros contra. inversion contra.
Qed.

Lemma insert_permute_equality_breaks :
  exists (V : Type) (v1 v2 : V) (k1 k2 : key) (t : tree V),
    k1 <> k2 /\ insert k1 v1 (insert k2 v2 t) <> insert k2 v2 (insert k1 v1 t).
Proof.
   exists string.
   exists "five"%string. 
   exists "one"%string.
   exists 5. exists 3.
   exists (T E 2 "two"%string E).
   split. 
   - intros contra. inversion contra.
   - simpl. intros contra. inversion contra.
Qed.   

Fixpoint elements {V : Type} (t : tree V) : list (key * V) :=
  match t with
  | E => []
  | T l k v r => elements l ++ [(k, v)] ++ elements r
  end.

Example elements_ex :
    elements ex_tree = [(2, "two"); (4, "four"); (5, "five")]%string.
Proof. reflexivity. Qed.

Definition elements_complete_spec :=
  forall (V : Type) (k : key) (v d : V) (t : tree V),
    bound k t = true ->
    lookup d k t = v ->
    In (k, v) (elements t).

Theorem elements_complete : elements_complete_spec.
Proof.
 unfold elements_complete_spec. 
 intros. induction t. 
 - simpl in H. inversion H.
 -  simpl in *. destruct (k <? k0) eqn:Hk.
   + apply in_or_app. left. apply IHt1. 
     * apply H.
     * apply H0. 
   + destruct (k >? k0) eqn:Hkk.
     * apply in_or_app. right. Search In. apply in_cons. 
       apply IHt2. 
       -- apply H.
       -- apply H0.
     * subst v0. assert (k=k0). 
       -- Search ">?". apply Nat.ltb_ge in Hk. specialize (gtb_reflect k k0).  intros.
           rewrite Hkk in H0. Search reflect. inversion H0. apply not_gt in H1.  
           lia.
       -- subst k0. apply in_elt. 
Qed.

Definition elements_correct_spec :=
  forall (V : Type) (k : key) (v d : V) (t : tree V),
    BST t ->
    In (k, v) (elements t) ->
    bound k t = true /\ lookup d k t = v.

Check Forall_app.

Definition uncurry {X Y Z : Type} (f : X -> Y -> Z) '(a, b) :=
  f a b.

Hint Transparent uncurry : core.

Lemma elements_preserves_forall : forall (V : Type) (P : key -> V -> Prop) (t : tree V),
    ForallT P t ->
    Forall (uncurry P) (elements t).
Proof.
  intros. induction t. 
  - simpl. apply Forall_nil. 
  - simpl. apply Forall_app. 
    split. 
    + apply IHt1. inversion H. destruct H1. apply H1.
    + simpl. apply Forall_cons.  
      * inversion H. unfold uncurry. apply H0.
      * apply IHt2. inversion H. destruct H1. apply H2. 
Qed.      

Lemma elements_preserves_relation :
  forall (V : Type) (k k' : key) (v : V) (t : tree V) (R : key -> key -> Prop),
    ForallT (fun y _ => R y k') t
    -> In (k, v) (elements t)
    -> R k k'.
Proof.
 intros. apply elements_preserves_forall in H. 
  unfold uncurry in H. simpl in H. rewrite Forall_forall in H. 
 apply H in H0. apply H0.
Qed.

Theorem elements_correct : elements_correct_spec.
Proof. 
  unfold elements_correct_spec.  
  intros.          
  induction H.  
  - simpl in H0. inversion H0. 
  - simpl. simpl in H0. apply in_app_or in H0. destruct H0. 
    + destruct (k <? x) eqn:Heq. 
      * apply IHBST1. apply H0. 
      * apply Nat.ltb_ge in Heq. 
        assert (x=k \/ x<k).
        -- lia.
        -- destruct H4. 
           ++ apply elements_preserves_relation with (k:=k) (v:=v) in H.
              ** subst. apply Nat.lt_irrefl in H. inversion H.
              ** apply H0.
           ++ unfold gtb. apply elements_preserves_relation with (k:=k) (v:=v) in H. 
              ** assert (k<k). 
                 --- lia. 
                 --- apply Nat.lt_irrefl in H5. inversion H5. 
              ** apply H0.
     + simpl in H0. destruct H0. 
       * inversion H0. unfold gtb. rewrite Nat.ltb_irrefl. auto.
       * destruct (k <? x) eqn:Heq. 
         -- apply elements_preserves_relation with (k:=k) (v:=v) in H1.
            ++ apply Nat.ltb_lt in Heq. assert (x<x). 
                 --- lia. 
                 --- apply Nat.lt_irrefl in H4. inversion H4.
            ++ apply H0. 
         -- apply Nat.ltb_ge in Heq. assert (x=k \/ x<k).
        ++ lia.
        ++ destruct H4. 
           ** apply elements_preserves_relation with (k:=k) (v:=v) in H1.
              --- subst. apply Nat.lt_irrefl in H1. inversion H1.
              --- apply H0.
           ** unfold gtb. Search "<?". apply Nat.ltb_lt in H4. rewrite H4.
              apply IHBST2. apply H0.   
Qed.

Theorem elements_complete_inverse :
  forall (V : Type) (k : key) (v : V) (t : tree V),
    BST t ->
    bound k t = false ->
    ~ In (k, v) (elements t).
Proof.
  intros. intros contra. 
  unshelve eapply elements_correct in H; auto. 
  apply H in contra. 
  destruct contra.
  rewrite H1 in H0.
  inversion H0. 
Qed.  
              
Lemma bound_value : forall (V : Type) (k : key) (t : tree V),
    bound k t = true -> exists v, forall d, lookup d k t = v.
Proof.
  intros. 
  induction t. 
  - simpl in H. inversion H. 
  - simpl in *.  destruct (k <? k0) eqn:Hk1.
    + apply IHt1 in H. apply H. 
    + destruct (k >? k0) eqn:Hk2.
      * apply IHt2 in H. apply H.  
      * exists v. auto.
Qed.  

Theorem elements_correct_inverse :
  forall (V : Type) (k : key) (t : tree V),
    (forall v, ~ In (k, v) (elements t)) ->
    bound k t = false.
Proof.
 intros V k t Hi. apply not_true_is_false. intros Hb.
  destruct (bound_value _ _ _ Hb) as [v Hl].
  apply (Hi v). exact (elements_complete _ _ _ _ _ Hb (Hl v)).
Qed.


Lemma sorted_app: forall l1 l2 x,
  Sort.sorted l1 -> Sort.sorted l2 ->
  Forall (fun n => n < x) l1 -> Forall (fun n => n > x) l2 ->
  Sort.sorted (l1 ++ x :: l2).
Proof.
  intros. induction H. 
  - simpl. induction l2. 
    + apply sorted_1. 
    + apply sorted_cons. 
      Search Forall. apply Forall_cons_iff in H2.
      destruct H2. 
      * lia. 
      * apply H0. 
  - replace ([x0] ++ x :: l2) with (x0 :: x :: l2) by auto.
    apply sorted_cons. 
    Search Forall. 
    + apply Forall_inv in H1.  lia. 
    + induction l2. 
      * apply sorted_1.
      * apply sorted_cons. 
      Search Forall. apply Forall_cons_iff in H2.
      destruct H2. 
      -- lia. 
      -- apply H0.
  - rewrite <- app_comm_cons.  rewrite <- app_comm_cons.  
    apply sorted_cons. 
    + apply H.
    + rewrite app_comm_cons. apply IHsorted. 
      Search Forall. apply Forall_cons. 
      *  apply Forall_cons_iff in H1.
        destruct H1.   Search Forall. apply Forall_inv in H4. 
        apply H4. 
      * apply Forall_cons_iff in H1. destruct H1. 
       apply Forall_cons_iff in H4. destruct H4. apply H5. 
Qed.

Definition list_keys {V : Type} (lst : list (key * V)) :=
  map fst lst.

Theorem sorted_elements : forall (V : Type) (t : tree V),
    BST t -> Sort.sorted (list_keys (elements t)).
Proof.
  intros. 
  induction H. 
  - simpl. apply sorted_nil.
  - simpl.  unfold list_keys. rewrite map_app. simpl.  
    apply sorted_app. 
    + apply IHBST1. 
    + apply IHBST2.
    + apply Forall_forall. 
      intros. apply in_map_iff in H3. 
      destruct H3 as [x' H3].
      destruct H3. destruct x'. simpl in H3. subst. 
      eapply elements_preserves_relation in H.
      * apply H. 
      * apply H4.
    + apply Forall_forall. 
      intros. apply in_map_iff in H3. destruct H3 as [x' H3].
      destruct H3. destruct x'.
      simpl in H3. subst.   
      eapply elements_preserves_relation in H0.
      * apply H0. 
      * apply H4.
Qed.

Print NoDup.

Definition disjoint {X:Type} (l1 l2: list X) := forall (x : X),
    In x l1 -> ~ In x l2.















