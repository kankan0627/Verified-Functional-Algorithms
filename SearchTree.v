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

Lemma NoDup_append : forall (X:Type) (l1 l2: list X),
  NoDup l1 -> NoDup l2 -> disjoint l1 l2 ->
  NoDup (l1 ++ l2).
Proof. 
  intros X l1 l2 H.
  generalize dependent l2.
  induction H.  
  - intros. rewrite app_nil_l. apply H. 
  - intros. simpl.  Search NoDup. apply NoDup_cons. 
    + Search In. intros contra. apply in_app_iff in contra. 
      destruct contra. 
      * apply H in H3. inversion H3. 
      * unfold disjoint in H2. 
       specialize H2 with x. apply H2.  
       -- simpl. left. auto.  
       --  apply H3. 
    + apply IHNoDup. 
      * apply H1. 
      * unfold disjoint. intros. unfold disjoint in H2.
        apply H2. simpl. right. apply H3. 
Qed.

Theorem elements_nodup_keys : forall (V : Type) (t : tree V),
    BST t ->
    NoDup (list_keys (elements t)).
Proof.
  intros. 
  induction H. 
  - simpl. apply NoDup_nil.
  - simpl.  unfold list_keys. rewrite map_app. simpl. 
    Search NoDup. apply NoDup_append. 
    + unfold list_keys in IHBST1. apply IHBST1. 
    + apply NoDup_cons. intros contra. 
      * Search In. apply in_map_iff in contra.   
        destruct contra as [x' Hc]. 
        destruct x'. destruct Hc. 
        simpl in H3. subst. apply elements_preserves_relation with (k:=x) (v:=v0) in H0.
        -- apply Nat.lt_irrefl in H0. inversion H0. 
        -- apply H4.
      * apply IHBST2.
    + unfold disjoint. intros.
      intros contra. simpl in contra. apply in_map_iff in H3.
      destruct contra. 
      * subst.  destruct H3 as [x' H3]. destruct x'. destruct H3. 
        simpl in H3. subst. 
       eapply elements_preserves_relation with (k:=x0) (v:=v0) in H.
       -- apply Nat.lt_irrefl in H. inversion H. 
       -- apply H4. 
      * apply in_map_iff in H4. destruct H3 as [x' H3]. destruct x'. destruct H3. 
        simpl in H3. subst. 
    destruct H4 as [x' H4]. destruct x'. destruct H4. 
        simpl in H3. subst. 
        apply elements_preserves_relation with (k:=x0) (v:=v0) in H.
       -- apply elements_preserves_relation with (k:=x0) (v:=v1) in H0.
          ++ assert (x0 < x0). 
             ** lia.
             **  apply Nat.lt_irrefl in H3. inversion H3. 
          ++ apply H4.
       -- apply H5. 
Qed.   
      
Fixpoint fast_elements_tr {V : Type} (t : tree V)
         (acc : list (key * V)) : list (key * V) :=
  match t with
  | E => acc
  | T l k v r => fast_elements_tr l ((k, v) :: fast_elements_tr r acc)
  end.


Definition fast_elements {V : Type} (t : tree V) : list (key * V) :=
  fast_elements_tr t [].

Lemma fast_elements_tr_helper :
  forall (V : Type) (t : tree V) (lst : list (key * V)),
    fast_elements_tr t lst = elements t ++ lst.
Proof.
  intros V. induction t. 
  - intros. simpl. auto.
  - intros. simpl. rewrite app_assoc_reverse. rewrite IHt2.  rewrite IHt1. 
    rewrite app_comm_cons. auto.
Qed.


Lemma fast_elements_eq_elements : forall (V : Type) (t : tree V),
    fast_elements t = elements t.
Proof.
  intros V.
  induction t. 
  - simpl. unfold fast_elements. simpl. auto.
  - unfold fast_elements. simpl. rewrite fast_elements_tr_helper.
    rewrite fast_elements_tr_helper. rewrite app_nil_r. auto. 
Qed.

Corollary fast_elements_correct :
  forall (V : Type) (k : key) (v d : V) (t : tree V),
    BST t ->
    In (k, v) (fast_elements t) ->
    bound k t = true /\ lookup d k t = v.
Proof.
  intros. apply elements_correct. 
  - apply H.
  - rewrite <- fast_elements_eq_elements. apply H0. 
Qed. 

Lemma elements_empty : forall (V : Type),
    @elements V empty_tree = [].
Proof.
  intros. simpl. reflexivity.
Qed.

Fixpoint kvs_insert {V : Type} (k : key) (v : V) (kvs : list (key * V)) :=
  match kvs with
  | [] => [(k, v)]
  | (k', v') :: kvs' =>
    if k <? k' then (k, v) :: kvs
    else if k >? k' then (k', v') :: kvs_insert k v kvs'
         else (k, v) :: kvs'
  end.

Lemma kvs_insert_split :
  forall (V : Type) (v v0 : V) (e1 e2 : list (key * V)) (k k0 : key),
    Forall (fun '(k',_) => k' < k0) e1 ->
    Forall (fun '(k',_) => k' > k0) e2 ->
    kvs_insert k v (e1 ++ (k0,v0):: e2) =
    if k <? k0 then
      (kvs_insert k v e1) ++ (k0,v0)::e2
    else if k >? k0 then
           e1 ++ (k0,v0)::(kvs_insert k v e2)
         else
           e1 ++ (k,v)::e2.
Proof.
  intros.
  destruct (k <? k0) eqn:Heq.
  - induction e1. 
    + simpl. rewrite Heq. auto.
    +  Search Forall. simpl. destruct a. destruct (k <? k1).
      * auto. 
      * destruct (k >? k1). 
        -- Search Forall. apply Forall_inv_tail in H.
           apply IHe1 in H. rewrite H. auto.
        -- auto.
   - Search "<?". destruct (k >? k0) eqn:Hn.
     + induction e1.
       * simpl. rewrite Heq.  rewrite Hn. auto. 
       * simpl. destruct a. destruct (k <? k1) eqn:Hk.
         -- Search Forall.  apply Forall_inv in H.  
            Search ">?".  
            specialize gtb_reflect with (x:=k) (y:=k0). intros.
            rewrite Hn in H1. Search reflect. 
 apply reflect_iff in H1. assert (true = true).
 ++ auto. 
 ++ apply H1 in H2. 
apply Nat.ltb_lt in Hk. assert (k1 > k0).
    ** lia.
    ** assert (k0>k0).
       --- lia. 
       --- Search ">".  apply Arith_prebase.gt_irrefl_stt in H4. inversion H4. 
       -- destruct (k >? k1) eqn:Hneq.
          ++  apply Forall_inv_tail in H. apply IHe1 in H. rewrite H. auto.
          ++ apply Nat.ltb_ge in Hk.  apply Forall_inv in H. 
             unfold gtb in Hneq. Search "<?".  apply Nat.ltb_ge in Hneq. 
             Search "<?". unfold gtb in Hn. apply Nat.ltb_lt in Hn.
             assert (k<k). 
             ** lia. 
             ** apply Arith_prebase.gt_irrefl_stt in H1. inversion H1. 
       + induction e1.
         * simpl. rewrite Heq.  rewrite Hn. auto. 
         * simpl. destruct a.          
            destruct (k <? k1) eqn:Hek. apply Forall_inv in H. Search "<?". 
            apply Nat.ltb_ge in Heq. apply Nat.ltb_lt in Hek. assert (k<k).
            -- lia. 
            -- apply Arith_prebase.gt_irrefl_stt in H1. inversion H1.
        -- destruct (k >? k1) eqn:Hee.
           ++ apply Forall_inv_tail in H. apply IHe1 in H. 
              rewrite H. auto. 
           ++ apply Forall_inv in H. apply Nat.ltb_ge in Heq.
              unfold gtb in Hee. apply Nat.ltb_ge in Hee. assert (k<k).
            ** lia. 
            ** apply Arith_prebase.gt_irrefl_stt in H1. inversion H1.
Qed.

Lemma kvs_insert_elements : forall (V : Type) (t : tree V),
    BST t ->
    forall (k : key) (v : V),
      elements (insert k v t) = kvs_insert k v (elements t).
Proof.
  intros. 
  induction H. 
  - simpl. auto.
  - simpl. apply elements_preserves_forall in H. 
    unfold uncurry in H.  
    apply elements_preserves_forall in H0.
    unfold uncurry in H0. 
    destruct (k <? x) eqn:Hkx. 
    + simpl. eapply kvs_insert_split in H. rewrite H. 
      * rewrite Hkx in *. rewrite IHBST1. auto. 
      * apply H0. 
    +  destruct (k >? x) eqn:Heq.
      * simpl. eapply kvs_insert_split in H0. rewrite H0.
        -- rewrite Hkx. rewrite Heq. rewrite IHBST2. auto.
        -- apply H.
      * simpl. eapply kvs_insert_split in H0.
        -- rewrite H0. rewrite Hkx. rewrite Heq. auto. 
        -- apply H. 
Qed.

Fixpoint map_of_list {V : Type} (el : list (key * V)) : partial_map V :=
  match el with
  | [] => empty
  | (k, v) :: el' => update (map_of_list el') k v
  end.

Definition Abs {V : Type} (t : tree V) : partial_map V :=
  map_of_list (elements t).

Definition find {V : Type} (d : V) (k : key) (m : partial_map V) : V :=
  match m k with
  | Some v => v
  | None => d
  end.

Definition map_bound {V : Type} (k : key) (m : partial_map V) : bool :=
  match m k with
  | Some _ => true
  | None => false
  end.

Lemma in_fst : forall (X Y : Type) (lst : list (X * Y)) (x : X) (y : Y),
    In (x, y) lst -> In x (map fst lst).
Proof.
  intros. induction lst. 
  - simpl in H. inversion H.
  - simpl in *. destruct H. 
    + subst. simpl. left. auto. 
    + right. apply IHlst. apply H. 
Qed.

Lemma in_map_of_list : forall (V : Type) (el : list (key * V)) (k : key) (v : V),
    NoDup (map fst el) ->
    In (k,v) el -> (map_of_list el) k = Some v.
Proof.
  intros. 
  induction el. 
  - simpl in H0. inversion H0. 
  - simpl in *. destruct a. destruct H0.  
    + inversion H0. rewrite update_eq. auto. 
    + simpl in H. apply NoDup_cons_iff in H.
      destruct H. Locate update_eq. destruct (k0 =? k) eqn:Heq.
      * rewrite Nat.eqb_eq in Heq.  subst k0. 
        apply in_fst in H0. apply H in H0.  inversion H0. 
      * rewrite Nat.eqb_neq in Heq. eapply update_neq  in Heq. rewrite Heq.
        apply IHel. 
        -- apply H1. 
        -- apply H0. 
Qed.

Lemma not_in_map_of_list : forall (V : Type) (el : list (key * V)) (k : key),
    ~ In k (map fst el) -> (map_of_list el) k = None.
Proof.
  intros. 
  induction el.  
  - simpl in *. Search empty.  apply apply_empty. 
  - simpl in *. destruct a. simpl in H. Search (~ (_ \/ _)).  
    apply Decidable.not_or in H. destruct H. eapply update_neq in H.
    rewrite H. apply IHel. apply H0. 
Qed.

Lemma empty_relate : forall (V : Type),
    @Abs V empty_tree = empty.
Proof.
  reflexivity.
Qed.

Theorem bound_relate : forall (V : Type) (t : tree V) (k : key),
    BST t ->
    map_bound k (Abs t) = bound k t.
Proof.
 unfold Abs. 
  intros V t k H. unfold map_bound. destruct (bound k t) eqn:E. 
  - destruct (bound_value _ _ _ E) as [v Hl].
    rewrite in_map_of_list with (v := v).
    + reflexivity.
    + exact (elements_nodup_keys _ _ H).
    + exact (elements_complete _ _ _ _ _ E (Hl v)). 
  - rewrite not_in_map_of_list.   
    + reflexivity.
    + destruct (elements t) eqn:Ht.  
      * simpl. intros contra. inversion contra. 
      * simpl. intros contra. destruct contra. 
        -- destruct p. simpl in H0. subst k0. 
           assert (In (k, v) (elements t)).
           ++ rewrite Ht. simpl. left. auto. 
           ++ specialize (elements_complete_inverse V k v t H E).
              intros. apply H1 in H0. inversion H0. 
        -- Search In. destruct p.
            apply in_map_iff in H0.
            destruct H0 as [x' H0]. destruct x'.
            simpl in H0. destruct H0. subst k. assert (In (k1, v0) (elements t)).
            ++ rewrite Ht. simpl. right. apply H1. 
            ++ specialize (elements_complete_inverse V k1 v0 t H E).
              intros. apply H2 in H0. inversion H0.
Qed. 

Lemma lookup_relate : forall (V : Type) (t : tree V) (d : V) (k : key),
    BST t -> find d k (Abs t) = lookup d k t.
Proof.
   unfold Abs.  
   intros V t d k H. unfold find. destruct (bound k t) eqn:E. 
  - destruct (bound_value _ _ _ E) as [v Hl]. 
    rewrite in_map_of_list with (v := v).
    + symmetry. auto.
    + exact (elements_nodup_keys _ _ H).
    + exact (elements_complete _ _ _ _ _ E (Hl v)). 
  - rewrite not_in_map_of_list.   
    + eapply bound_default in E. symmetry. apply E. 
    + destruct (elements t) eqn:Ht.  
      * simpl. intros contra. inversion contra. 
      * simpl. intros contra. destruct contra. 
        -- destruct p. simpl in H0. subst k0. 
           assert (In (k, v) (elements t)).
           ++ rewrite Ht. simpl. left. auto. 
           ++ specialize (elements_complete_inverse V k v t H E).
              intros. apply H1 in H0. inversion H0. 
        --  destruct p.
            apply in_map_iff in H0.
            destruct H0 as [x' H0]. destruct x'.
            simpl in H0. destruct H0. subst k. assert (In (k1, v0) (elements t)).
            ++ rewrite Ht. simpl. right. apply H1. 
            ++ specialize (elements_complete_inverse V k1 v0 t H E).
              intros. apply H2 in H0. inversion H0.
Qed. 

Lemma insert_relate : forall (V : Type) (t : tree V) (k : key) (v : V),
  BST t -> Abs (insert k v t) = update (Abs t) k v.
Proof.
  unfold Abs.
  intros.
  rewrite kvs_insert_elements; auto.
  remember (elements t) as l.
  clear -l. induction l. 
  - simpl. auto.
  - simpl. destruct a. destruct (k <? k0) eqn:H1.
    + simpl. auto. 
    + destruct (k >? k0) eqn:H2.
      * simpl. rewrite IHl. Search update. 
        rewrite update_permute. auto. unfold gtb in H2. 
        rewrite Nat.ltb_lt in H2. lia.
      * simpl. unfold gtb in H2. Search "<?". apply Nat.ltb_ge in H1. 
        apply Nat.ltb_ge in H2. assert (k=k0).
        -- lia.
        -- subst k0. Search update. rewrite update_shadow. auto.
Qed. 
  
 
