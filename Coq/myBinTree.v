(* Bartłomiej Królikowski *)

Require Import Arith.

Inductive BinTree (A : Type) : Type :=
| Node : A -> BinTree A -> BinTree A -> BinTree A
| Empty : BinTree A.

Inductive Maybe (A : Type) : Type :=
| Just : A -> Maybe A
| Nothing : Maybe A.

Fixpoint insert (A : Type) (ord : A -> A -> bool) (a : A) (T : BinTree A) : BinTree A :=
match T with
  | Node _ a' Tl Tr =>
  if ord a a'
    then Node A a' (insert A ord a Tl) Tr
    else Node A a' Tl (insert A ord a Tr)
  | Empty _ => Node A a (Empty A) (Empty A)
end.

Fixpoint find (A : Type) (ord : A -> A -> bool) (a : A) (T : BinTree A) : bool :=
match T with
  | Node _ a' Tl Tr =>
  if ord a a'
    then if ord a' a
           then true
           else find A ord a Tl
    else find A ord a Tr
  | Empty _ => false
end.

Fixpoint min (A : Type) (T : BinTree A) : Maybe A :=
match T with
  | Node _ a (Empty _) _ => Just A a
  | Node _ _ Tl _ => min A Tl
  | Empty _ => Nothing A
end.

Fixpoint max (A : Type) (T : BinTree A) : Maybe A :=
match T with
  | Node _ a _ (Empty _) => Just A a
  | Node _ _ _ Tr => max A Tr
  | Empty _ => Nothing A
end.

Fixpoint removeMax (A : Type) (T : BinTree A) : BinTree A :=
match T with
  | Node _ _ Tl (Empty _) => Tl
  | Node _ a Tl Tr => Node A a Tl (removeMax A Tr)
  | Empty _ => Empty A
end.

Definition root (A : Type) (T : BinTree A) : Maybe A :=
match T with
  | Node _ a _ _ => Just A a
  | Empty _ => Nothing A
end.

Definition remove (A : Type) (T : BinTree A) : BinTree A :=
match T with
  | Node _ _ Tl Tr =>
  match max A Tl with
    | Just _ a => Node A a (removeMax A Tl) Tr
    | Nothing _ => Tr
  end
  | Empty _ => Empty A
end.

Fixpoint delete (A : Type) (ord : A -> A -> bool) (a : A) (T : BinTree A) : BinTree A :=
match T with
  | Node _ a' Tl Tr =>
  if ord a a'
    then if ord a' a
           then remove A T
           else Node A a' (delete A ord a Tl) Tr
    else Node A a' Tl (delete A ord a Tr)
  | Empty _ => Empty A
end.

Fixpoint size (A : Type) (T : BinTree A) : nat :=
match T with
  | Node _ _ Tl Tr => 1 + size A Tl + size A Tr
  | Empty _ => 0
end.

Inductive Elem (A : Type) (a : A) : BinTree A -> Prop :=
| elem_root : forall Tl Tr : BinTree A, Elem A a (Node A a Tl Tr)
| elem_left :
  forall T : BinTree A, Elem A a T ->
  forall (a' : A) (T' : BinTree A), Elem A a (Node A a' T T')
| elem_right :
  forall T : BinTree A, Elem A a T ->
  forall (a' : A) (T' : BinTree A), Elem A a (Node A a' T' T).

Inductive BSTProperty (A : Type) (ord : A -> A -> Prop) : BinTree A -> Prop :=
| BST_node :
  forall (Tl Tr : BinTree A) (a : A),
    BSTProperty A ord Tl ->
    BSTProperty A ord Tr ->
    (forall a' : A, Elem A a' Tl -> ord a' a) ->
    (forall a' : A, Elem A a' Tr -> ord a a') ->
      BSTProperty A ord (Node A a Tl Tr)
| BST_empty : BSTProperty A ord (Empty A).

Fact bool_fun :
  forall (A : Type) (rel : A -> A -> bool) (a a' : A),
    rel a a' = true \/ rel a a' = false.
Proof.
  intros. destruct (rel a a').
  - left. reflexivity.
  - right. reflexivity.
Qed.

Fact empty_elem :
  forall (A : Type) (a : A), ~Elem A a (Empty A).
Proof.
  intros A a H. inversion H.
Qed.

Definition single (A : Type) (a : A) : BinTree A := (Node A a (Empty A) (Empty A)).

Fact single_elem :
  forall (A : Type) (a a' : A), Elem A a (single A a') -> a = a'.
Proof.
  intros. inversion H.
  - reflexivity.
  - inversion H1.
  - inversion H1.
Qed.

Fact BST_single :
  forall (A : Type) (ord : A -> A -> bool) (a : A),
    BSTProperty A (fun a' a'' : A => ord a' a'' = true) (single A a).
Proof.
  intros. unfold single. apply BST_node.
  - apply BST_empty.
  - apply BST_empty.
  - intros. inversion H.
  - intros. inversion H.
Qed.

Fact BST_trans :
  forall (A : Type) (ord : A -> A -> Prop) (a : A) (Tl Tr : BinTree A),
  (forall b c d : A, ord b c -> ord c d -> ord b d) ->
  BSTProperty A ord (Node A a Tl Tr) ->
  forall a' a'' : A, Elem A a' Tl -> Elem A a'' Tr -> ord a' a''.
Proof.
  intros. inversion H0. apply (H a' a a'').
  - apply H8. exact H1.
  - apply H9. exact H2.
Qed.

Fact find_correct :
  forall (A : Type) (ord : A -> A -> bool),
  (forall a a' : A, ord a a' = true -> ord a' a = true -> a = a') ->
  forall (a : A) (T : BinTree A), find A ord a T = true -> Elem A a T.
Proof.
  induction T.
  - cbn. specialize (bool_fun A ord). intro. specialize (H0 a0 a) as H1. specialize (H0 a a0).
    destruct H0.
    + destruct H1.
      * intros. rewrite (H a a0).
        -- apply elem_root.
        -- exact H0.
        -- exact H1.
      * rewrite H0, H1. intros. apply elem_left. apply IHT1. exact H2.
    + rewrite H0. intros. apply elem_right. apply IHT2. exact H2.
  - cbn. intros. inversion H0.
Qed.

Fact find_equiv_correct :
  forall (A : Type) (ord : A -> A -> bool) (a : A) (T : BinTree A),
  find A ord a T = true ->
  exists a' : A, Elem A a' T /\ ord a a' = true /\ ord a' a = true.
Proof.
  induction T; cbn.
  - specialize (bool_fun A ord). intro. specialize (H a0 a) as H'. specialize (H a a0).
    destruct H; rewrite H.
    + destruct H'; rewrite H0; intros.
      * exists a0. split.
        -- apply elem_root.
        -- split.
           ++ exact H.
           ++ exact H0.
      * destruct IHT1.
        -- exact H1.
        -- exists x. destruct H2. split.
           ++ apply elem_left. exact H2.
           ++ exact H3.
    + intros. destruct IHT2.
      * exact H0.
      * exists x. destruct H1. split.
        -- apply elem_right. exact H1.
        -- exact H2.
  - intros. inversion H.
Qed.

Fact find_left :
  forall (A : Type) (ord : A -> A -> bool) (a : A) (T : BinTree A),
  Elem A a T ->
  find A ord a T = true ->
  forall (a' : A) (T' : BinTree A),
  BSTProperty A (fun b b' : A => ord b b' = true) (Node A a' T T') ->
    find A ord a (Node A a' T T') = true.
Proof.
  intros. cbn. inversion H1. rewrite H7.
  - specialize (bool_fun A ord a' a). intros. destruct H9; rewrite H9.
    + reflexivity.
    + exact H0.
  - exact H.
Qed.

Fact find_right :
  forall (A : Type) (ord : A -> A -> bool) (a : A) (T : BinTree A),
  Elem A a T ->
  find A ord a T = true ->
  forall (a' : A) (T' : BinTree A),
  BSTProperty A (fun b b' : A => ord b b' = true) (Node A a' T' T) ->
    find A ord a (Node A a' T' T) = true.
Proof.
  intros. cbn. inversion H1. rewrite H8.
  - specialize (bool_fun A ord a a'). intros. destruct H9; rewrite H9.
    + reflexivity.
    + exact H0.
  - exact H.
Qed.

Fact find_correct_r :
  forall (A : Type) (ord : A -> A -> bool),
  (forall a : A, ord a a = true) ->
  forall (a : A) (T : BinTree A),
    BSTProperty A (fun a' a'' : A => ord a' a'' = true) T ->
    Elem A a T -> find A ord a T = true.
Proof.
  intros. induction H1.
  - cbn. rewrite H. reflexivity.
  - apply find_left.
    + exact H1.
    + apply IHElem. inversion H0. exact H5.
    + exact H0.
  - apply find_right.
    + exact H1.
    + apply IHElem. inversion H0. exact H6.
    + exact H0.
Qed.

Fact insert_increase :
  forall (A : Type) (ord : A -> A -> bool) (a : A) (T : BinTree A),
    size A (insert A ord a T) = S (size A T).
Proof.
  induction T; cbn.
  - specialize (bool_fun A ord a a0). intros. destruct H; rewrite H; cbn; f_equal.
    + rewrite IHT1. cbn. reflexivity.
    + rewrite IHT2. apply Nat.add_succ_r.
  - reflexivity.
Qed.

Fact insert_correct :
  forall (A : Type) (ord : A -> A -> bool) (a : A) (T : BinTree A),
    Elem A a (insert A ord a T).
Proof.
  induction T; cbn.
  - destruct (ord a a0).
    + apply elem_left. exact IHT1.
    + apply elem_right. exact IHT2.
  - apply elem_root.
Qed.

Fact insert_extends :
  forall (A : Type) (a : A) (T : BinTree A),
  Elem A a T ->
  forall (ord : A -> A -> bool) (a' : A), Elem A a (insert A ord a' T).
Proof.
  intros A a T H. induction H; intros; cbn.
  - destruct (ord a' a); apply elem_root.
  - destruct (ord a'0 a'); apply elem_left; trivial.
  - destruct (ord a'0 a'); apply elem_right; trivial.
Qed.

Lemma insert_elem :
  forall (A : Type) (ord : A -> A -> bool) (a a' : A) (T : BinTree A),
    Elem A a (insert A ord a' T) -> a = a' \/ Elem A a T.
Proof.
  induction T; cbn; intros.
  - destruct (ord a' a0); inversion H.
    + right. apply elem_root.
    + destruct IHT1.
      * exact H1.
      * left. exact H4.
      * right. apply elem_left. exact H4.
    + right. apply elem_right. exact H1.
    + right. apply elem_root.
    + right. apply elem_left. exact H1.
    + destruct IHT2.
      * exact H1.
      * left. exact H4.
      * right. apply elem_right. exact H4.
  - left. apply single_elem. unfold single. exact H.
Qed.

Theorem insert_BST_correct :
  forall (A : Type) (ord : A -> A -> bool) (T : BinTree A),
  (forall a a' : A, ord a a' = false -> ord a' a = true) ->
  BSTProperty A (fun a a' => ord a a' = true) T ->
  forall a : A, BSTProperty A (fun a a' => ord a a' = true) (insert A ord a T).
Proof.
  intros A ord T ordLin H. induction H.
  - cbn. specialize (bool_fun A ord). intros. specialize (H3 a0 a).
    destruct H3; rewrite H3; apply BST_node.
    + apply IHBSTProperty1.
    + apply H0.
    + intros. specialize (insert_elem A ord a' a0 Tl H4). intro. destruct H5.
      * rewrite H5. exact H3.
      * apply H1. exact H5.
    + exact H2.
    + apply H.
    + apply IHBSTProperty2.
    + exact H1.
    + intros. specialize (insert_elem A ord a' a0 Tr H4). intro. destruct H5.
      * rewrite H5. apply ordLin. exact H3.
      * apply H2. exact H5.
  - cbn. intros. apply BST_single.
Qed.

Fact min_node_node :
  forall (A : Type) (a a' : A) (Tl Tmid Tr : BinTree A),
    min A (Node A a (Node A a' Tl Tmid) Tr) = min A (Node A a' Tl Tmid).
Proof.
  trivial.
Qed.

Fact min_node_empty :
  forall (A : Type) (a : A) (Tr : BinTree A),
    min A (Node A a (Empty A) Tr) = Just A a.
Proof.
  trivial.
Qed.

Fact min_empty :
  forall A : Type,
    min A (Empty A) = Nothing A.
Proof.
  trivial.
Qed.

Fact min_success :
  forall (A : Type) (Tl Tr : BinTree A) (a : A),
  exists (a' : A), min A (Node A a Tl Tr) = Just A a'.
Proof.
  induction Tl; intros.
  - rewrite min_node_node. apply IHTl1.
  - cbn. exists a. reflexivity.
Qed.

Lemma min_elem :
  forall (A : Type) (T : BinTree A) (a : A),
    min A T = Just A a -> Elem A a T.
Proof.
  induction T.
  - destruct T1.
    + rewrite min_node_node. intros. apply elem_left. apply IHT1. exact H.
    + cbn. intros. injection H. intros. rewrite H0. apply elem_root.
  - cbn. intros. inversion H.
Qed.

Theorem min_correct :
  forall (A : Type) (ord : A -> A -> Prop) (T : BinTree A) (a a' : A),
  (forall b : A, ord b b) ->
  (forall b b' b'' : A, ord b b' -> ord b' b'' -> ord b b'') ->
  BSTProperty A ord T ->
    Elem A a T -> min A T = Just A a' -> ord a' a.
Proof.
  intros. induction H1; inversion H2.
  - destruct Tl.
    + apply H1. apply min_elem. rewrite min_node_node in H3. exact H3.
    + cbn in H3. injection H3. intros. rewrite H5. apply H.
  - apply IHBSTProperty1.
    + exact H6.
    + destruct Tl.
      * rewrite min_node_node in H3. exact H3.
      * inversion H6.
  - destruct Tl.
    + apply (BST_trans A ord a0 (Node A a1 Tl1 Tl2) Tr).
      * exact H0.
      * apply BST_node; trivial.
      * apply min_elem. rewrite min_node_node in H3. exact H3.
      * exact H6.
    + cbn in H3. injection H3. intros. rewrite <- H9. apply H4. exact H6.
Qed.

Fact max_node_node :
  forall (A : Type) (a a' : A) (Tl Tmid Tr : BinTree A),
    max A (Node A a Tl (Node A a' Tmid Tr)) = max A (Node A a' Tmid Tr).
Proof.
  trivial.
Qed.

Fact max_node_empty :
  forall (A : Type) (a : A) (Tl : BinTree A),
    max A (Node A a Tl (Empty A)) = Just A a.
Proof.
  trivial.
Qed.

Fact max_empty :
  forall A : Type,
    max A (Empty A) = Nothing A.
Proof.
  trivial.
Qed.

Fact max_success :
  forall (A : Type) (Tl Tr : BinTree A) (a : A),
  exists (a' : A), max A (Node A a Tl Tr) = Just A a'.
Proof.
  induction Tr; intros.
  - rewrite max_node_node. apply IHTr2.
  - cbn. exists a. reflexivity.
Qed.

Lemma max_elem :
  forall (A : Type) (T : BinTree A) (a : A),
    max A T = Just A a -> Elem A a T.
Proof.
  induction T.
  - destruct T2.
    + rewrite max_node_node. intros. apply elem_right. apply IHT2. exact H.
    + cbn. intros. injection H. intros. rewrite H0. apply elem_root.
  - cbn. intros. inversion H.
Qed.

Theorem max_correct :
  forall (A : Type) (ord : A -> A -> Prop) (T : BinTree A) (a a' : A),
  (forall b : A, ord b b) ->
  (forall b b' b'' : A, ord b b' -> ord b' b'' -> ord b b'') ->
  BSTProperty A ord T ->
    Elem A a T -> max A T = Just A a' -> ord a a'.
Proof.
  intros. induction H1; inversion H2.
  - destruct Tr.
    + apply H4. apply max_elem. rewrite max_node_node in H3. exact H3.
    + cbn in H3. injection H3. intros. rewrite H5. apply H.
  - destruct Tr.
    + apply (BST_trans A ord a0 Tl (Node A a1 Tr1 Tr2)).
      * exact H0.
      * apply BST_node; trivial.
      * exact H6.
      * apply max_elem. rewrite max_node_node in H3. exact H3.
    + cbn in H3. injection H3. intros. rewrite <- H9. apply H1. exact H6.
  - apply IHBSTProperty2.
    + exact H6.
    + destruct Tr.
      * rewrite max_node_node in H3. exact H3.
      * inversion H6.
Qed.

Fact root_node :
  forall (A : Type) (a : A) (Tl Tr : BinTree A), root A (Node A a Tl Tr) = Just A a.
Proof.
  trivial.
Qed.

Fact root_empty :
  forall (A : Type), root A (Empty A) = Nothing A.
Proof.
  trivial.
Qed.

Fact root_elem :
  forall (A : Type) (a : A) (T : BinTree A), root A T = Just A a -> Elem A a T.
Proof.
  destruct T; cbn; intros.
  - injection H. intros. rewrite H0. apply elem_root.
  - inversion H.
Qed.

Fact size_node :
  forall (A : Type) (a : A) (Tl Tr : BinTree A),
    size A (Node A a Tl Tr) = S (size A Tl + size A Tr).
Proof.
  trivial.
Qed.

Fact size_empty :
  forall A : Type, size A (Empty A) = 0.
Proof.
  trivial.
Qed.

Fact removeMax_decrease :
  forall (A : Type) (T : BinTree A), size A (removeMax A T) = size A T - 1.
Proof.
  induction T; cbn.
  - destruct T2.
    + rewrite size_node. rewrite IHT2. cbn. rewrite Nat.add_succ_r. cbn. rewrite Nat.sub_0_r.
      reflexivity.
    + cbn. symmetry. rewrite Nat.sub_0_r. apply Nat.add_0_r.
  - reflexivity.
Qed.

Lemma removeMax_incl :
  forall (A : Type) (a : A) (T : BinTree A),
    Elem A a (removeMax A T) -> Elem A a T.
Proof.
  induction T; cbn.
  - destruct T2; intros.
    + inversion H.
      * apply elem_root.
      * apply elem_left. exact H1.
      * apply elem_right. apply IHT2. cbn. exact H1.
    + apply elem_left. exact H.
  - exact id.
Qed.

Lemma removeMax_elem :
  forall (A : Type) (a : A) (T : BinTree A),
    Elem A a T -> Elem A a (removeMax A T) \/ max A T = Just A a.
Proof.
  intros. induction H.
  - cbn. destruct Tr.
    + left. apply elem_root.
    + right. reflexivity.
  - left. cbn. destruct T'.
    + apply elem_left. exact H.
    + exact H.
  - destruct IHElem.
    + left. cbn. destruct T.
      * apply elem_right. exact H0.
      * cbn in H0. inversion H0.
    + right. cbn. destruct T.
      * exact H0.
      * cbn in H0. inversion H0.
Qed.

Theorem removeMax_BST_correct :
  forall (A : Type) (ord : A -> A -> Prop) (T : BinTree A),
    BSTProperty A ord T -> BSTProperty A ord (removeMax A T).
Proof.
  intros. induction H.
  - cbn. destruct Tr.
    + apply BST_node.
      * exact H.
      * exact IHBSTProperty2.
      * exact H1.
      * intros. apply H2. apply removeMax_incl. exact H3.
    + exact H.
  - cbn. apply BST_empty.
Qed.

Fact remove_decrease :
  forall (A : Type) (T : BinTree A), size A (remove A T) = size A T - 1.
Proof.
  destruct T; cbn.
  - destruct T1.
    + destruct (max_success A T1_1 T1_2 a0). rewrite H. rewrite size_node.
      rewrite removeMax_decrease. cbn. f_equal. f_equal. apply Nat.sub_0_r.
    + cbn. symmetry. apply Nat.sub_0_r.
  - reflexivity.
Qed.

Lemma remove_incl :
  forall (A : Type) (a : A) (T : BinTree A),
    Elem A a (remove A T) -> Elem A a T.
Proof.
  destruct T; cbn.
  - destruct T1.
    + destruct (max_success A T1_1 T1_2 a1). rewrite H. intro. inversion H0.
      * apply elem_left. apply max_elem. exact H.
      * apply elem_left. apply removeMax_incl. cbn. exact H2.
      * apply elem_right. exact H2.
    + cbn. intros. apply elem_right. exact H.
  - exact id.
Qed.

Lemma remove_elem :
  forall (A : Type) (a : A) (T : BinTree A),
    Elem A a T -> Elem A a (remove A T) \/ root A T = Just A a.
Proof.
  intros. destruct H.
  - right. cbn. reflexivity.
  - left. cbn. destruct T.
    + destruct (max_success A T1 T2 a0). rewrite H0.
      destruct (removeMax_elem A a (Node A a0 T1 T2)).
      * exact H.
      * apply elem_left. exact H1.
      * rewrite H0 in H1. injection H1. intros. rewrite H2. apply elem_root.
    + inversion H.
  - left. cbn. destruct T'.
    + destruct (max_success A T'1 T'2 a0). rewrite H0. apply elem_right. exact H.
    + cbn. exact H.
Qed.

Theorem remove_BST_correct :
  forall (A : Type) (ord : A -> A -> Prop) (T : BinTree A),
  (forall a : A, ord a a) ->
  (forall a b c : A, ord a b -> ord b c -> ord a c) ->
  BSTProperty A ord T ->
    BSTProperty A ord (remove A T).
Proof.
  intros. destruct H1; cbn.
  - destruct Tl.
    + destruct (max_success A Tl1 Tl2 a0). rewrite H3. apply BST_node.
      * apply removeMax_BST_correct. exact H1_.
      * exact H1_0.
      * intros. apply (max_correct A ord (Node A a0 Tl1 Tl2)).
        -- exact H.
        -- exact H0.
        -- exact H1_.
        -- apply removeMax_incl. exact H4.
        -- exact H3.
      * intros.
        apply (BST_trans A ord a (Node A a0 Tl1 Tl2) Tr).
        -- exact H0.
        -- apply BST_node; trivial.
        -- apply max_elem. exact H3.
        -- exact H4.
    + cbn. exact H1_0.
  - apply BST_empty.
Qed.

Fact delete_decrease :
  forall (A : Type) (ord : A -> A -> bool) (a : A) (T : BinTree A),
  (forall a' : A, ord a' a' = true) ->
  BSTProperty A (fun a' a'' : A => ord a' a'' = true) T ->
    Elem A a T -> size A (delete A ord a T) = size A T - 1.
Proof.
  intros. induction H1; cbn; inversion H0.
  - rewrite H. fold (remove A (Node A a Tl Tr)). apply remove_decrease.
  - rewrite H7.
    + specialize (bool_fun A ord a' a). intro. destruct H9; rewrite H9.
      * fold (remove A (Node A a T T')). apply remove_decrease.
      * cbn. rewrite IHElem.
        -- destruct T.
          ++ cbn. rewrite Nat.sub_0_r. reflexivity.
          ++ inversion H1.
        -- exact H5.
    + exact H1.
  - rewrite H8.
    + specialize (bool_fun A ord a a'). intro. destruct H9; rewrite H9.
      * fold (remove A (Node A a T' T)). apply remove_decrease.
      * cbn. rewrite IHElem.
        -- destruct T.
          ++ cbn. rewrite Nat.add_succ_r. cbn. f_equal. f_equal. apply Nat.sub_0_r.
          ++ inversion H1.
        -- exact H6.
    + exact H1.
Qed.

Fact delete_find_decrease :
  forall (A : Type) (ord : A -> A -> bool) (a : A) (T : BinTree A),
  find A ord a T = true ->
    size A (delete A ord a T) = size A T - 1.
Proof.
  induction T; cbn.
  - specialize (bool_fun A ord). intro. specialize (H a0 a) as H0. specialize (H a a0).
    destruct H; rewrite H.
    + destruct H0; rewrite H0; intros.
      * fold (remove A (Node A a T1 T2)). apply remove_decrease.
      * cbn. rewrite IHT1.
        -- destruct T1; cbn.
          ++ f_equal. f_equal. apply Nat.sub_0_r.
          ++ cbn in H1. inversion H1.
        -- exact H1.
    + intros. cbn. rewrite IHT2.
      * destruct T2; cbn.
        -- rewrite Nat.add_succ_r. cbn. f_equal. f_equal. apply Nat.sub_0_r.
        -- cbn in H1. inversion H1.
      * exact H1.
  - reflexivity.
Qed.

Fact delete_not_find_ident :
  forall (A : Type) (ord : A -> A -> bool) (a : A) (T : BinTree A),
    find A ord a T = false -> delete A ord a T = T.
Proof.
  induction T; cbn.
  - specialize (bool_fun A ord). intro. specialize (H a0 a) as H0. specialize (H a a0).
    destruct H; rewrite H.
    + destruct H0; rewrite H0.
      * intro. inversion H1.
      * intro. rewrite IHT1; trivial.
    + intro. rewrite IHT2; trivial.
  - reflexivity.
Qed.

Fact delete_decrease_find :
  forall (A : Type) (ord : A -> A -> bool) (a : A) (T : BinTree A),
  size A (delete A ord a T) = size A T - 1 ->
    find A ord a T = true \/ T = Empty A.
Proof.
  induction T.
  - cbn. specialize (bool_fun A ord). intro. specialize (H a0 a) as H1.
    specialize (H a a0) as H0. destruct H0; rewrite H0.
    + destruct H1; rewrite H1; cbn.
      * intros. left. reflexivity.
      * rewrite Nat.sub_0_r. rewrite <- Nat.add_succ_l. rewrite Nat.add_cancel_r. intro.
        destruct IHT1.
        -- destruct T1; cbn in *.
          ++ injection H2. intro. rewrite H3. symmetry. apply Nat.sub_0_r.
          ++ reflexivity.
        -- left. exact H3.
        -- rewrite H3 in H2. cbn in H2. inversion H2.
    + cbn. rewrite Nat.sub_0_r. rewrite <- Nat.add_succ_r. rewrite Nat.add_cancel_l. intro.
      destruct IHT2.
      * destruct T2; cbn in *.
        -- injection H2. intro. rewrite H3. symmetry. apply Nat.sub_0_r.
        -- reflexivity.
      * left. exact H3.
      * rewrite H3 in H2. cbn in H2. inversion H2.
  - intro. right. reflexivity.
Qed.

Lemma delete_incl :
  forall (A : Type) (ord : A -> A -> bool) (a a' : A) (T : BinTree A),
    Elem A a (delete A ord a' T) -> Elem A a T.
Proof.
  induction T; cbn.
  - specialize (bool_fun A ord). intro. specialize (H a' a0) as H0. specialize (H a0 a').
    destruct H0; rewrite H0.
    + destruct H; rewrite H.
      * destruct T1.
        -- destruct (max_success A T1_1 T1_2 a1). rewrite H1. intro. inversion H2.
          ++ apply elem_left. apply max_elem. exact H1.
          ++ apply elem_left. apply removeMax_incl. cbn. exact H4.
          ++ apply elem_right. exact H4.
        -- cbn. intro. apply elem_right. exact H1.
      * intro. inversion H1.
        -- apply elem_root.
        -- apply elem_left. apply IHT1. exact H3.
        -- apply elem_right. exact H3.
    + intro. inversion H1.
      * apply elem_root.
      * apply elem_left. exact H3.
      * apply elem_right. apply IHT2. exact H3.
  - exact id.
Qed.

Lemma delete_elem :
  forall (A : Type) (ord : A -> A -> bool) (a a' : A) (T : BinTree A),
    Elem A a T -> Elem A a (delete A ord a' T) \/ find A ord a' T = true.
Proof.
  intros. specialize (bool_fun A ord). intro. induction H; cbn.
  - intros. specialize (H0 a a') as H1. specialize (H0 a' a).
    destruct H0; rewrite H.
    + destruct H1; rewrite H0.
      * right. reflexivity.
      * left. apply elem_root.
    + left. apply elem_root.
  - specialize (H0 a'0 a') as H1. specialize (H0 a' a'0). destruct H0; rewrite H0.
    + destruct H1; rewrite H1.
      * right. reflexivity.
      * destruct IHElem.
        -- left. apply elem_left. exact H2.
        -- right. exact H2.
    + left. apply elem_left. exact H.
  - specialize (H0 a'0 a') as H1. specialize (H0 a' a'0). destruct H0; rewrite H0.
    + destruct H1; rewrite H1.
      * right. reflexivity.
      * left. apply elem_right. exact H.
    + destruct IHElem.
      * left. apply elem_right. exact H2.
      * right. exact H2.
Qed.

Theorem delete_BST_correct :
  forall (A : Type) (ord : A -> A -> bool) (a : A) (T : BinTree A),
  (forall a' : A, ord a' a' = true) ->
  (forall b c d : A, ord b c = true -> ord c d = true -> ord b d = true) ->
  BSTProperty A (fun b b' : A => ord b b' = true) T ->
    BSTProperty A (fun b b' : A => ord b b' = true) (delete A ord a T).
Proof.
  intros. induction H1; cbn.
  - specialize (bool_fun A ord). intro. specialize (H3 a0 a) as H4. specialize (H3 a a0).
    destruct H3; rewrite H3.
    + destruct H4; rewrite H4.
      * destruct Tl.
        -- destruct (max_success A Tl1 Tl2 a1). rewrite H5. apply BST_node.
          ++ apply removeMax_BST_correct. exact H1_.
          ++ exact H1_0.
          ++ intros.
apply (max_correct A (fun b b' : A => ord b b' = true) (Node A a1 Tl1 Tl2)); trivial.
apply removeMax_incl. exact H6.
          ++ intros. apply (H0 x a0 a').
            ** apply H1. apply max_elem. exact H5.
            ** apply H2. exact H6.
        -- cbn. exact H1_0.
      * apply BST_node; trivial. intros. apply H1. apply (delete_incl A ord a' a). exact H5.
    + apply BST_node; trivial. intros. apply H2. apply (delete_incl A ord a' a). exact H5.
  - apply BST_empty.
Qed.

Theorem insert_delete_inverse :
  forall (A : Type) (ord : A -> A -> bool) (a : A) (T : BinTree A),
  ord a a = true ->
  find A ord a T = false ->
    delete A ord a (insert A ord a T) = T.
Proof.
  induction T.
  - cbn. specialize (bool_fun A ord). intro. specialize (H a0 a) as H0. specialize (H a a0).
    destruct H; rewrite H.
    + destruct H0; rewrite H0.
      * intros. inversion H2.
      * cbn. rewrite H. rewrite H0. intros. rewrite IHT1; trivial.
    + cbn. rewrite H. intros. rewrite IHT2; trivial.
  - cbn. intros. rewrite H. reflexivity.
Qed.
