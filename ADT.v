From Coq Require Import String.   
From VFA Require Import Perm.
From VFA Require Import Maps.
From VFA Require Import SearchTree.

Module Type Table.

Parameter table : Type.
Definition key := nat.
Parameter V : Type.
Parameter default : V.
Parameter empty : table.
Parameter get : key -> table -> V.
Parameter set : key -> V -> table -> table.
Axiom get_empty_default : forall (k : key),
      get k empty = default.
Axiom get_set_same : forall (k : key) (v : V) (t : table),
      get k (set k v t) = v.
Axiom get_set_other : forall (k k' : key) (v : V) (t : table),
      k <> k' -> get k' (set k v t) = get k' t.
End Table.

Module Type ValType.
  Parameter V : Type.
  Parameter default : V.
End ValType.

Module FunTable (VT : ValType) <: Table.
  Definition V := VT.V.
  Definition default := VT.default.
  Definition key := nat.
  Definition table := key -> V.

  Definition empty : table :=
    fun _ => default.

  Definition get (k : key) (t : table) : V := t k.

  Definition set (k : key) (v : V) (t : table) : table :=
    fun k' => if k =? k' then v else t k'.

Theorem get_empty_default: forall (k : key),
   get k empty = default.
Proof. 
   intros. unfold get. unfold empty. auto. 
Qed.

Theorem get_set_same: forall (k : key) (v : V) (t : table), 
      get k (set k v t) = v.
Proof.
   intros.  unfold set. unfold get. rewrite Nat.eqb_refl. auto.
Qed.

Theorem get_set_other: forall (k k' : key) (v : V) (t : table),
      k <> k' -> get k' (set k v t) = get k' t.
Proof.
intros. unfold set. unfold get. apply Nat.eqb_neq in H. 
rewrite H. auto.
Qed.

End FunTable.

Module StringVal.
  Definition V := string.
  Definition default := ""%string.
End StringVal.

Module FunTableExamples.
Module StringFunTable := FunTable StringVal.
Import StringFunTable.
Open Scope string_scope.

Example ex1 : get 0 empty = "".
Proof. reflexivity. Qed.

Example ex2 : get 0 (set 0 "A" empty) = "A".
Proof. reflexivity. Qed.

Example ex3 : get 1 (set 0 "A" empty) = "".
Proof. reflexivity. Qed.

End FunTableExamples.

Module NatVal.
Definition V := nat.
Definition default := 0.
End NatVal.

Module NatFunTableExamples.
Module NatFunTable := FunTable NatVal.
Import NatFunTable.

Example ex1 : get 0 empty = 0.
Proof. reflexivity. Qed.

Example ex2 : get 0 (set 0 1 empty) = 1.
Proof. reflexivity. Qed.

Example ex3 : get 1 (set 0 1 empty) = 0.
Proof. reflexivity. Qed.

End NatFunTableExamples.

Module ListsTable (VT : ValType) <: Table.
Definition V := VT.V.
Definition default := VT.default.
Definition key := nat.
Definition table := list (key * V).
Definition empty : table := [].

Fixpoint get (k : key) (t : table) : V :=
  match t with
  | (k', v') :: t' => if k =? k' then v' else (get k t')
  | [] => default
  end.

Definition set (k : key) (v : V) (t : table) : table := (k,v)::t.


Theorem get_empty_default: forall (k : key),
   get k empty = default.
Proof.
   intros. simpl. auto.
Qed. 

Theorem get_set_same: forall (k : key) (v : V) (t : table),
  get k (set k v t) = v.
Proof.
  intros. unfold set. simpl. rewrite Nat.eqb_refl. auto.   
Qed.

Theorem get_set_other: forall (k k' : key) (v : V) (t : table),
   k <> k' -> get k' (set k v t) = get k' t.
Proof.
   intros. unfold set. simpl. rewrite Nat.eqb_sym.   
   apply Nat.eqb_neq in H. rewrite H. auto.  
Qed.

End ListsTable.

Module StringListsTableExamples.
Module StringListsTable := ListsTable StringVal.
Import StringListsTable.
Open Scope string_scope.

Example ex1 : get 0 empty = "".
Proof.
  simpl. auto.
Qed.

Example ex2 : get 0 (set 0 "A" empty) = "A".
Proof.
   simpl. auto.
Qed.

Example ex3 : get 1 (set 0 "A" empty) = "".
Proof.
  simpl. auto.
Qed.

End StringListsTableExamples.

Module TreeTable (VT : ValType) <: Table.

Definition V := VT.V.
Definition default := VT.default.
Definition key := nat.
Definition table := tree V.

Definition empty : table := 
    @empty_tree V.

Definition get (k : key) (t: table) : V := 
    lookup default k t.

Definition set (k : key) (v : V) (t : table) : table :=
    insert k v t.

Theorem get_empty_default: forall (k : key),
      get k empty = default.
Proof.
  intros. unfold get. apply lookup_empty. 
Qed.

Theorem get_set_same: forall (k : key) (v : V) (t : table),
      get k (set k v t) = v.
Proof.
  intros. unfold set. unfold get. apply lookup_insert_eq. 
Qed.

Theorem get_set_other: forall (k k' : key) (v : V) (t : table),
      k <> k' -> get k' (set k v t) = get k' t.
Proof.
   intros. unfold set. unfold get. apply lookup_insert_neq.  apply H.
Qed.

End TreeTable.

Module Type ETable_first_attempt.

Include Table.

Parameter bound : key -> table -> bool.
Parameter elements : table -> list (key * V).

Axiom elements_complete : forall (k : key) (v : V) (t : table),
  bound k t = true ->
  get k t = v ->
  In (k, v) (elements t).

Axiom elements_correct : forall (k : key) (v : V) (t : table),
  In (k, v) (elements t) ->
  bound k t = true /\ get k t = v.

End ETable_first_attempt.

Module TreeETable_first_attempt (VT : ValType) <: ETable_first_attempt.

Include TreeTable VT.

Check get : key -> table -> V.

Definition bound (k : key) (t : table) : bool :=
    SearchTree.bound k t.

Definition elements (t : table) : list (key * V) :=
    SearchTree.elements t.

Theorem elements_complete : forall (k : key) (v : V) (t : table),
      bound k t = true ->
      get k t = v ->
      In (k, v) (elements t).
Proof.
intros k v t Hbound Hlookup. unfold get in Hlookup.
pose proof (SearchTree.elements_complete) as Hcomplete.
unfold elements_complete_spec in Hcomplete. 
apply Hcomplete with default. 
(* Stuck *)
Admitted.

Theorem elements_correct : forall (k : key) (v : V) (t : table),
   In (k, v) (elements t) ->
   bound k t = true /\ get k t = v.
Proof.
intros k v t Hin.
pose proof (SearchTree.elements_correct) as Hcorrect.
unfold elements_correct_spec in Hcorrect.
apply Hcorrect.
Admitted.

End TreeETable_first_attempt.

Module Type ETable.
Include Table.
  
Parameter rep_ok : table -> Prop.
Parameter bound : key -> table -> bool.
Parameter elements : table -> list (key * V).

Axiom empty_ok : rep_ok empty.

Axiom set_ok : forall (k : key) (v : V) (t : table),
      rep_ok t -> rep_ok (set k v t).

Axiom bound_empty : forall (k : key),
      bound k empty = false.

Axiom bound_set_same : forall (k : key) (v : V) (t : table),
      bound k (set k v t) = true.

Axiom bound_set_other : forall (k k' : key) (v : V) (t : table),
      k <> k' -> bound k' (set k v t) = bound k' t.

Axiom elements_complete : forall (k : key) (v : V) (t : table),
      rep_ok t ->
      bound k t = true ->
      get k t = v ->
      In (k, v) (elements t).

Axiom elements_correct : forall (k : key) (v : V) (t : table),
      rep_ok t ->
      In (k, v) (elements t) ->
      bound k t = true /\ get k t = v.

End ETable.

Module TreeETable (VT : ValType) <: ETable.
Include TreeTable VT.

Definition rep_ok (t : table) : Prop :=
    BST t.

Definition bound (k : key) (t : table) : bool :=
    SearchTree.bound k t.

Definition elements (t : table) : list (key * V) :=
    SearchTree.elements t.

Theorem empty_ok : rep_ok empty.
Proof. 
unfold rep_ok. unfold empty. unfold empty_tree. apply BST_E.
Qed. 

Theorem set_ok : forall (k : key) (v : V) (t : table),
      rep_ok t -> rep_ok (set k v t).
Proof.
apply insert_BST.
Qed.

Theorem bound_empty : forall (k : key),
      bound k empty = false.
Proof.
reflexivity.
Qed.

Theorem bound_set_same : forall (k : key) (v : V) (t : table),
      bound k (set k v t) = true.
Proof.
intros k v t. unfold bound, set. induction t; bdall.
Qed.

Theorem bound_set_other : forall (k k' : key) (v : V) (t : table),
      k <> k' -> bound k' (set k v t) = bound k' t.
Proof.
intros k k' v t Hneq. unfold bound, set. induction t; bdall.
Qed.

Theorem elements_complete : forall (k : key) (v : V) (t : table),
      rep_ok t ->
      bound k t = true ->
      get k t = v ->
      In (k, v) (elements t).
Proof.
intros k v t Hbound Hlookup.
pose proof SearchTree.elements_complete as Hcomplete.
unfold elements_complete_spec in Hcomplete. unfold get.  
apply Hcomplete. apply Hlookup.
Qed.

Theorem elements_correct : forall (k : key) (v : V) (t : table),
      rep_ok t ->
      In (k, v) (elements t) ->
      bound k t = true /\ get k t = v.
Proof.
intros k v t. simpl. intros Hin.
pose proof SearchTree.elements_correct as Hcorrect.
unfold elements_correct_spec in Hcorrect.
apply Hcorrect; assumption.
Qed.

End TreeETable.

Module StringTreeETableExample.

Module StringTreeETable := TreeETable StringVal.
Import StringTreeETable.
Open Scope string_scope.

Example ex1 :
   In (0, "A") (elements (set 0 "A" (set 1 "B" empty))).
Proof.
apply elements_complete;
auto using empty_ok, set_ok, bound_set_same, get_set_same.
Qed.

End StringTreeETableExample.

Module TreeETableFullyEncapsulated (VT : ValType) : ETable.
Include TreeTable VT.

Definition rep_ok (t : table) : Prop :=
    BST t.

Definition bound (k : key) (t : table) : bool :=
    SearchTree.bound k t.

Definition elements (t : table) : list (key * V) :=
    SearchTree.elements t.

Theorem empty_ok : rep_ok empty.
Proof.
apply empty_tree_BST.
Qed.

Theorem set_ok : forall (k : key) (v : V) (t : table),
   rep_ok t -> rep_ok (set k v t).
Proof.
apply insert_BST.
Qed.

Theorem bound_empty : forall (k : key),
   bound k empty = false.
Proof.
reflexivity.
Qed.

Theorem bound_set_same : forall (k : key) (v : V) (t : table),
  bound k (set k v t) = true.
Proof.
  intros k v t. unfold bound, set. induction t; bdall.
Qed.

Theorem bound_set_other : forall (k k' : key) (v : V) (t : table),
  k <> k' -> bound k' (set k v t) = bound k' t.
Proof.
  intros k k' v t Hneq. unfold bound, set. induction t; bdall.
Qed.

Theorem elements_complete : forall (k : key) (v : V) (t : table),
   rep_ok t ->
   bound k t = true ->
   get k t = v ->
   In (k, v) (elements t).
Proof.
  intros k v t Hbound Hlookup.
  pose proof SearchTree.elements_complete as Hcomplete.
  unfold elements_complete_spec in Hcomplete.
  apply Hcomplete; assumption.
Qed.

Theorem elements_correct : forall (k : key) (v : V) (t : table),
  rep_ok t ->
  In (k, v) (elements t) ->
  bound k t = true /\ get k t = v.
Proof.
  intros k v t. simpl. intros Hin.
  pose proof SearchTree.elements_correct as Hcorrect.
  unfold elements_correct_spec in Hcorrect.
  apply Hcorrect; assumption.
Qed.

End TreeETableFullyEncapsulated.

Module OverlyEncapsulatedExample.

Module StringTreeETableFullyEncapsulated := TreeETableFullyEncapsulated StringVal.
Import StringTreeETableFullyEncapsulated.
Open Scope string_scope.

Fail Example ex1 : get 0 empty = "".
  (* fails with an error about "" not having type V *)
End OverlyEncapsulatedExample.

Print OverlyEncapsulatedExample.StringTreeETableFullyEncapsulated.V.

Module Type SimpleTable.
  Parameter key : Type.
  Parameter V : Type.
  Parameter default : V.
  Parameter table : Type.
End SimpleTable.

Module SimpleStringTable1 : SimpleTable.
  Definition key := nat.
  Definition V := string.
  Definition default : string := "".
  Definition table := tree V.
End SimpleStringTable1.
(* V is abstract. *)
Print SimpleStringTable1.V.

Module Type SimpleTable2 := SimpleTable with Definition V := string.

Module SimpleStringTable2 : SimpleTable2.
  Definition key := nat.
  Definition V := string.
  Definition default : string := "".
  Definition table := tree V.
End SimpleStringTable2.

(* V is exposed, but default is abstract. *)
Print SimpleStringTable2.V.
Print SimpleStringTable2.default.

Module Type SimpleTable3 := SimpleTable
  with Definition V := string
  with Definition default := ""%string.

Module SimpleStringTable3 : SimpleTable3.
  Definition key := nat.
  Definition V := string.
  Definition default : string := "".
  Definition table := tree V.
End SimpleStringTable3.

(* Both V and default are exposed. *)
Print SimpleStringTable3.V.
Print SimpleStringTable3.default.

Module TreeETableEncapsulated (VT : ValType) : (ETable with Definition V := VT.V with Definition default := VT.default).
Include TreeTable VT.

Definition rep_ok (t : table) : Prop :=
    BST t.
  
Definition bound (k : key) (t : table) : bool :=
    SearchTree.bound k t.

Definition elements (t : table) : list (key * V) :=
    SearchTree.elements t.

Theorem empty_ok : rep_ok empty.
Proof.
  apply empty_tree_BST.
Qed.

Theorem set_ok : forall (k : key) (v : V) (t : table),
   rep_ok t -> rep_ok (set k v t).
Proof.
  apply insert_BST.
Qed.

Theorem bound_empty : forall (k : key),
  bound k empty = false.
Proof.
  reflexivity.
Qed.

Theorem bound_set_same : forall (k : key) (v : V) (t : table),
  bound k (set k v t) = true.
Proof.
  intros k v t. unfold bound, set. induction t; bdall.
Qed.

Theorem bound_set_other : forall (k k' : key) (v : V) (t : table),
      k <> k' -> bound k' (set k v t) = bound k' t.
Proof.
  intros k k' v t Hneq. unfold bound, set. induction t; bdall.
Qed.

Theorem elements_complete : forall (k : key) (v : V) (t : table),
    rep_ok t ->
    bound k t = true ->
    get k t = v ->
    In (k, v) (elements t).
Proof.
  intros k v t Hbound Hlookup.
  pose proof SearchTree.elements_complete as Hcomplete.
  unfold elements_complete_spec in Hcomplete.
  apply Hcomplete; assumption.
Qed.

Theorem elements_correct : forall (k : key) (v : V) (t : table),
    rep_ok t ->
    In (k, v) (elements t) ->
    bound k t = true /\ get k t = v.
Proof.
  intros k v t. simpl. intros Hin.
  pose proof SearchTree.elements_correct as Hcorrect.
  unfold elements_correct_spec in Hcorrect.
  apply Hcorrect; assumption.
Qed.

End TreeETableEncapsulated.

Module NicelyEncapsulatedExample.

Module StringTreeETableEncapsulated := TreeETableEncapsulated StringVal.
Import StringTreeETableEncapsulated.
Open Scope string_scope.

Example ex1 : get 0 empty = "".
Proof.
    Fail unfold get. 
    Fail reflexivity.
  
    apply get_empty_default.
Qed.

End NicelyEncapsulatedExample.

Definition map_update {V : Type} (k : key) (v : V) (m : partial_map V) : partial_map V :=
  update m k v.
Definition map_find {V : Type} := @find V.
Definition empty_map {V : Type} := @Maps.empty V.

Module Type ETableAbs.

  Parameter table : Type.
  Definition key := nat.
  Parameter V : Type.
  Parameter default : V.
  Parameter empty : table.
  Parameter get : key -> table -> V.
  Parameter set : key -> V -> table -> table.
  Parameter bound : key -> table -> bool.
  Parameter elements : table -> list (key * V).
  Parameter Abs : table -> partial_map V.
  Parameter rep_ok : table -> Prop.

  Axiom empty_ok :
      rep_ok empty.

  Axiom set_ok : forall (k : key) (v : V) (t : table),
      rep_ok t -> rep_ok (set k v t).

  Axiom empty_relate :
      Abs empty = empty_map.

  Axiom bound_relate : forall (t : table) (k : key),
      rep_ok t ->
      map_bound k (Abs t) = bound k t.

  Axiom lookup_relate : forall (t : table) (k : key),
      rep_ok t ->
      map_find default k (Abs t) = get k t.

  Axiom insert_relate : forall (t : table) (k : key) (v : V),
      rep_ok t ->
      map_update k v (Abs t) = Abs (set k v t).

  Axiom elements_relate : forall (t : table),
      rep_ok t ->
      Abs t = map_of_list (elements t).

End ETableAbs.

Module ListETableAbs (VT : ValType) <: ETableAbs.

Definition V := VT.V.
Definition default := VT.default.
Definition key := nat.
Definition table := list (key * V).
Definition empty : table := [].

Fixpoint get (k : key) (t : table) : V :=
  match t with
  | (k', v') :: t' => if k =? k' then v' else (get k t')
  | [] => default
  end.

Definition set (k : key) (v : V) (t : table) : table := (k,v)::t.

Fixpoint bound (k : key) (t : table) : bool := 
  match t with
  | [] => false
  | (k', v') :: t' => if k =? k' then true
                      else bound k t'
  end.

Definition elements (t : table) : list (key * V) := t.

Definition Abs (t : table) : partial_map V := SearchTree.map_of_list t.
 
Definition rep_ok (t : table) : Prop := 
   forall (P : (key * V) -> Prop), (forall (x : (key * V)), P x) -> Forall P t.
  
Theorem empty_ok : rep_ok empty.
Proof.
  unfold rep_ok. intros. apply Forall_nil. 
Qed.

Theorem set_ok : forall (k : key) (v : V) (t : table),
      rep_ok t -> rep_ok (set k v t).
Proof.
  intros.  
  unfold rep_ok, set.  
  intros. apply Forall_cons_iff. 
  unfold rep_ok in H. 
  split.  
  - apply H0.
  - apply H in H0. apply H0. 
Qed.

Theorem empty_relate :
   Abs empty = empty_map.
Proof.
  unfold Abs. simpl. reflexivity. 
Qed.

Theorem bound_relate : forall (t : table) (k : key),
   rep_ok t ->
   map_bound k (Abs t) = bound k t.
Proof.
  intros. induction t. 
  - simpl.  unfold Abs. simpl.  
unfold map_bound. rewrite apply_empty. auto.
  - unfold Abs. simpl. destruct a. unfold map_bound. 
    destruct (k =? k0) eqn:Heq.
    + rewrite Nat.eqb_eq in Heq. subst k0. 
      rewrite update_eq. auto.
    + rewrite Nat.eqb_sym in Heq.
      rewrite Nat.eqb_neq in Heq. eapply update_neq  in Heq.
      rewrite Heq.  apply IHt. unfold rep_ok in H. unfold rep_ok.
      intros. apply H in H0. apply Forall_cons_iff in H0. 
      destruct H0. apply H1. 
Qed.

Theorem lookup_relate : forall (t : table) (k : key),
   rep_ok t ->
   map_find default k (Abs t) = get k t.
Proof.
  intros. induction t. 
  - unfold Abs. unfold map_find. unfold find. 
    simpl. auto. 
  - unfold Abs. unfold map_find. unfold find. simpl. destruct a. 
     destruct (k =? k0) eqn:Heq.
    + rewrite Nat.eqb_eq in Heq. subst k0. 
      rewrite update_eq. auto.
    + rewrite Nat.eqb_sym in Heq.
      rewrite Nat.eqb_neq in Heq. eapply update_neq  in Heq.
      rewrite Heq.  apply IHt. unfold rep_ok in H. unfold rep_ok.
      intros. apply H in H0. apply Forall_cons_iff in H0. 
      destruct H0. apply H1. 
Qed.

Theorem insert_relate : forall (t : table) (k : key) (v : V),
   rep_ok t ->
   map_update k v (Abs t) = Abs (set k v t).
Proof.
  intros. induction t. 
  - unfold Abs. unfold map_update. simpl. auto.
  - unfold Abs. unfold map_update. simpl. auto.
Qed.

Theorem elements_relate : forall (t : table),
      rep_ok t ->
      Abs t = map_of_list (elements t).
Proof.
  intros. induction t. 
  - unfold Abs. simpl. auto. 
 - unfold Abs. simpl. auto.
Qed.

End ListETableAbs.

(* Instantiate functor for sake of autograding. *)
Module StringListETableAbs := ListETableAbs StringVal.

Module Type Queue.
  Parameter V : Type.
  Parameter queue : Type.
  Parameter empty: queue.
  Parameter is_empty : queue -> bool.
  Parameter enq : queue -> V -> queue.
  Parameter deq : queue -> queue.
  Parameter peek : V -> queue -> V.
  Axiom is_empty_empty : is_empty empty = true.
  Axiom is_empty_nonempty : forall q v, is_empty (enq q v) = false.
  Axiom peek_empty : forall d, peek d empty = d.
  Axiom peek_nonempty : forall d q v, peek d (enq q v) = peek v q.
  Axiom deq_empty : deq empty = empty.
  Axiom deq_nonempty : forall q v, deq (enq q v) = if is_empty q then q else enq (deq q) v.
End Queue.

Module ListQueue <: Queue.
  Definition V := nat. (* for simplicity *)
  Definition queue := list V.
  Definition empty : queue := [].
  Definition is_empty (q : queue) : bool := if ((length q) =? 0) then true else false.
  Definition enq (q : queue) (v : V) : queue := q ++ [v].  
  
  Definition deq (q : queue) : queue := 
     match q with 
      | [] => empty
      | h::q' => q'
     end.
  
  Definition peek (default : V) (q : queue) : V := 
    match q with 
      | [] => default
      | h::q' => h
     end.
  
Theorem is_empty_empty : is_empty empty = true.
Proof.
  unfold is_empty. simpl. auto. 
Qed.

Theorem is_empty_nonempty : forall q v,
      is_empty (enq q v) = false.
Proof.
  intros. unfold is_empty. unfold enq. rewrite last_length. 
  specialize Nat.neq_succ_0 with (Datatypes.length q).
  intros. apply Nat.eqb_neq in H. rewrite H. auto. 
Qed.

Theorem peek_empty : forall d,
    peek d empty = d.
Proof.
  intros. simpl. auto.
Qed. 

Theorem peek_nonempty : forall d q v,
   peek d (enq q v) = peek v q.
Proof.
  intros. induction q. 
 - simpl. auto. 
 - simpl. auto.
Qed. 

Theorem deq_empty :
    deq empty = empty.
Proof.
  auto. 
Qed.     

Theorem deq_nonempty : forall q v,
    deq (enq q v) = if is_empty q then q else enq (deq q) v.
Proof.
  intros. induction q. 
  - simpl. auto. 
  - simpl. auto.
Qed.


End ListQueue.

Module Type QueueAbs.
  Parameter V : Type.
  Parameter queue : Type.
  Parameter empty : queue.
  Parameter is_empty : queue -> bool.
  Parameter enq : queue -> V -> queue.
  Parameter deq : queue -> queue.
  Parameter peek : V -> queue -> V.
  Parameter Abs : queue -> list V.
  Axiom empty_relate : Abs empty = [].
  Axiom enq_relate : forall q v, Abs (enq q v) = (Abs q) ++ [v].
  Axiom peek_relate : forall d q, peek d q = hd d (Abs q).
  Axiom deq_relate : forall q, Abs (deq q) = tl (Abs q).
End QueueAbs.

Module TwoListQueueAbs <: QueueAbs.

  Definition V := nat. (* for simplicity *)

  Definition queue : Type := list V * list V.
  (* (f, b) represents a queue with a front list f and a back list
     b, where the back list is stored in reverse order. *)

  Definition Abs '((f, b) : queue) : list V :=
    f ++ (rev b).

  Definition empty : queue :=
    ([], []).

  Definition is_empty (q: queue) :=
    match q with
    | ([], []) => true
    | _ => false
    end.

  Definition enq '((f, b) : queue) (v : V) :=
    (f, v :: b).

  Definition deq (q : queue) :=
    match q with
    | ([], []) => ([], [])
    | ([], b) =>
      match rev b with
      | [] => ([], [])
      | _ :: f => (f, [])
      end
    | (_ :: f, b) => (f, b)
    end.

  Definition peek (d : V) (q : queue) :=
    match q with
    | ([], []) => d
    | ([], b) =>
      match rev b with
      | [] => d
      | v :: _ => v
      end
    | (v :: _, _) => v
    end.

Theorem empty_relate : Abs empty = [].
Proof.











