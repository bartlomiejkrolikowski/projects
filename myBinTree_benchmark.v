(* Bartłomiej Królikowski *)

Load "myBinTree". (* path to myBintree.v*)

Fixpoint insert_t (A : Type) (t : nat) (ord : A -> A -> bool) (a : A) (T : BinTree A) :
  BinTree A * nat :=
match T with
  | Node _ a' Tl Tr =>
  if ord a a'
    then let Tt := insert_t A (S t) ord a Tl
         in  (Node A a' (fst Tt) Tr, snd Tt)
    else let Tt := insert_t A (S t) ord a Tr
         in  (Node A a' Tl (fst Tt), snd Tt)
  | Empty _ => (Node A a (Empty A) (Empty A), t)
end.

Definition insert' (A : Type) : (A -> A -> bool) -> A -> BinTree A -> BinTree A * nat :=
  insert_t A 1.

Fixpoint find_t (A : Type) (t : nat) (ord : A -> A -> bool) (a : A) (T : BinTree A) :
  bool * nat:=
match T with
  | Node _ a' Tl Tr =>
  if ord a a'
    then if ord a' a
           then (true, t)
           else find_t A (S t) ord a Tl
    else find_t A (S t) ord a Tr
  | Empty _ => (false, t)
end.

Definition find' (A : Type) : (A -> A -> bool) -> A -> BinTree A -> bool * nat :=
  find_t A 1.

Fixpoint min_t (A : Type) (t : nat) (T : BinTree A) : Maybe A * nat :=
match T with
  | Node _ a (Empty _) _ => (Just A a, (S t))
  | Node _ _ Tl _ => min_t A (S t) Tl
  | Empty _ => (Nothing A, t)
end.

Definition min' (A : Type) : BinTree A -> Maybe A * nat := min_t A 1.

Fixpoint max_t (A : Type) (t : nat) (T : BinTree A) : Maybe A * nat :=
match T with
  | Node _ a _ (Empty _) => (Just A a, (S t))
  | Node _ _ _ Tr => max_t A (S t) Tr
  | Empty _ => (Nothing A, t)
end.

Definition max' (A : Type) : BinTree A -> Maybe A * nat := max_t A 1.

Fixpoint removeMax_t (A : Type) (t : nat) (T : BinTree A) : BinTree A * nat :=
match T with
  | Node _ _ Tl (Empty _) => (Tl, (S t))
  | Node _ a Tl Tr => let Tt := removeMax_t A (S t) Tr
                      in  (Node A a Tl (fst Tt), snd Tt)
  | Empty _ => (Empty A, t)
end.

Definition removeMax' (A : Type) : BinTree A -> BinTree A * nat :=
  removeMax_t A 1.

Definition root' (A : Type) (T : BinTree A) : Maybe A * nat :=
match T with
  | Node _ a _ _ => (Just A a, 1)
  | Empty _ => (Nothing A, 1)
end.

Definition remove' (A : Type) (T : BinTree A) : BinTree A * nat :=
match T with
  | Node _ _ Tl Tr =>
  match max' A Tl with
    | (Just _ a, t) => let Tt := removeMax' A Tl
                     in  (Node A a (fst Tt) Tr, 1 + t + snd Tt)
    | (Nothing _, t) => (Tr, 1 + t)
  end
  | Empty _ => (Empty A, 1)
end.

Fixpoint delete_t (A : Type) (t : nat) (ord : A -> A -> bool) (a : A) (T : BinTree A) :
  BinTree A * nat :=
match T with
  | Node _ a' Tl Tr =>
  if ord a a'
    then if ord a' a
           then let Tt := remove' A T
                in  (fst Tt, 1 + snd Tt)
           else let Tt := delete_t A (S t) ord a Tl
                in  (Node A a' (fst Tt) Tr, 1 + snd Tt)
    else let Tt := delete_t A (S t) ord a Tr
         in  (Node A a' Tl (fst Tt), snd Tt)
  | Empty _ => (Empty A, t)
end.

Definition delete' (A : Type) : (A -> A -> bool) -> A -> BinTree A -> BinTree A * nat :=
  delete_t A 1.

Fixpoint size' (A : Type) (T : BinTree A) : nat * nat :=
match T with
  | Node _ _ Tl Tr => let Stl := size' A Tl
                      in  let Str := size' A Tr
                          in  (1 + fst Stl + fst Str, 1 + snd Stl + snd Str)
  | Empty _ => (0, 1)
end.

Fixpoint height (A : Type) (T : BinTree A) : nat :=
match T with
  | Node _ _ Tl Tr => 1 + Nat.max (height A Tl) (height A Tr)
  | Empty _ => 0
end.

Fact insert_t_equiv :
  forall (A : Type) (ord : A -> A -> bool) (a : A) (T : BinTree A) (t : nat),
    fst (insert_t A t ord a T) = insert A ord a T.
Proof.
  induction T; intros; cbn.
  - destruct (ord a a0); cbn; f_equal; trivial.
  - trivial.
Qed.

Fact insert'_equiv :
  forall (A : Type) (ord : A -> A -> bool) (a : A) (T : BinTree A),
    fst (insert' A ord a T) = insert A ord a T.
Proof.
  unfold insert'. intros. apply insert_t_equiv.
Qed.

Fact find_t_equiv :
  forall (A : Type) (ord : A -> A -> bool) (a : A) (T : BinTree A) (t : nat),
    fst (find_t A t ord a T) = find A ord a T.
Proof.
  induction T; intros; cbn.
  - destruct (ord a a0).
   + destruct (ord a0 a).
     * trivial.
     * apply IHT1.
   + apply IHT2.
  - trivial.
Qed.

Fact find'_equiv :
  forall (A : Type) (ord : A -> A -> bool) (a : A) (T : BinTree A),
    fst (find' A ord a T) = find A ord a T.
Proof.
  unfold find'. intros. apply find_t_equiv.
Qed.

Fact min_t_equiv :
  forall (A : Type) (T : BinTree A) (t : nat),
    fst (min_t A t T) = min A T.
Proof.
  induction T; intros; cbn.
  - destruct T1.
    + apply IHT1.
    + trivial.
  - trivial.
Qed.

Fact min'_equiv :
  forall (A : Type) (T : BinTree A),
    fst (min' A T) = min A T.
Proof.
  unfold min'. intros. apply min_t_equiv.
Qed.

Fact max_t_equiv :
  forall (A : Type) (T : BinTree A) (t : nat),
    fst (max_t A t T) = max A T.
Proof.
  induction T; intros; cbn.
  - destruct T2.
    + apply IHT2.
    + trivial.
  - trivial.
Qed.

Fact max'_equiv :
  forall (A : Type) (T : BinTree A),
    fst (max' A T) = max A T.
Proof.
  unfold max'. intros. apply max_t_equiv.
Qed.

Fact removeMax_t_equiv :
  forall (A : Type) (T : BinTree A) (t : nat),
    fst (removeMax_t A t T) = removeMax A T.
Proof.
  induction T; intros; cbn.
  - destruct T2.
    + unfold fst. f_equal. apply IHT2.
    + trivial.
  - trivial.
Qed.

Fact removeMax'_equiv :
  forall (A : Type) (T : BinTree A),
    fst (removeMax' A T) = removeMax A T.
Proof.
  unfold removeMax'. intros. apply removeMax_t_equiv.
Qed.

Fact root'_equiv :
  forall (A : Type) (T : BinTree A),
    fst (root' A T) = root A T.
Proof.
  destruct T; trivial.
Qed.

Fact remove'_equiv :
  forall (A : Type) (T : BinTree A),
    fst (remove' A T) = remove A T.
Proof.
  destruct T; cbn.
  - assert (forall (A B : Type) (p : A * B), p = (fst p, snd p)).
    + destruct p. trivial.
    + rewrite H with (Maybe A) nat (max' A T1). rewrite max'_equiv. destruct (max A T1).
      * cbn. f_equal. apply removeMax'_equiv.
      * trivial.
  - trivial.
Qed.

Fact delete_t_equiv :
  forall (A : Type) (ord : A -> A -> bool) (a : A) (T : BinTree A) (t : nat),
    fst (delete_t A t ord a T) = delete A ord a T.
Proof.
  induction T; intros; cbn.
  - destruct (ord a a0); cbn.
    + destruct (ord a0 a); cbn.
      * assert (forall (A B : Type) (p : A * B), p = (fst p, snd p)).
        -- destruct p. trivial.
        -- rewrite H with (Maybe A) nat (max' A T1). rewrite max'_equiv. destruct (max A T1).
          ++ cbn. f_equal. apply removeMax'_equiv.
          ++ trivial.
      * f_equal. apply IHT1.
    + f_equal. apply IHT2.
  - trivial.
Qed.

Fact delete'_equiv :
  forall (A : Type) (ord : A -> A -> bool) (a : A) (T : BinTree A),
    fst (delete' A ord a T) = delete A ord a T.
Proof.
  unfold delete'. intros. apply delete_t_equiv.
Qed.

Fact size'_equiv :
  forall (A : Type) (T : BinTree A),
    fst (size' A T) = size A T.
Proof.
  induction T; cbn.
  - f_equal. f_equal; assumption.
  - trivial.
Qed.

Lemma insert_t_complex :
  forall (A : Type) (ord : A -> A -> bool) (a : A) (T : BinTree A) (t : nat),
    snd (insert_t A t ord a T) <= t + height A T.
Proof.
  induction T; intros; cbn.
  - destruct (ord a  a0); cbn.
    + apply Nat.le_trans with (S t + height A T1).
      * apply IHT1.
      * rewrite Nat.add_succ_r. rewrite <- Nat.add_succ_l. apply Nat.add_le_mono_l.
        apply Nat.le_max_l.
    + apply Nat.le_trans with (S t + height A T2).
      * apply IHT2.
      * rewrite Nat.add_succ_r. rewrite <- Nat.add_succ_l. apply Nat.add_le_mono_l.
        apply Nat.le_max_r.
  - rewrite Nat.add_0_r. apply Nat.le_refl.
Qed.

Theorem insert'_complex :
  forall (A : Type) (ord : A -> A -> bool) (a : A) (T : BinTree A),
    snd (insert' A ord a T) <= 1 + height A T.
Proof.
  unfold insert'. intros. apply insert_t_complex.
Qed.

Lemma find_t_complex :
  forall (A : Type) (ord : A -> A -> bool) (a : A) (T : BinTree A) (t : nat),
    snd (find_t A t ord a T) <= t + height A T.
Proof.
  induction T; intros; cbn.
  - destruct (ord a a0).
   + destruct (ord a0 a).
     * cbn. apply Nat.le_add_r.
     * apply Nat.le_trans with (S t + height A T1).
       -- apply IHT1.
       -- rewrite Nat.add_succ_r. rewrite <- Nat.add_succ_l. apply Nat.add_le_mono_l.
          apply Nat.le_max_l.
   + apply Nat.le_trans with (S t + height A T2).
     * apply IHT2.
     * rewrite Nat.add_succ_r. rewrite <- Nat.add_succ_l. apply Nat.add_le_mono_l.
       apply Nat.le_max_r.
  - intuition.
Qed.

Theorem find'_complex :
  forall (A : Type) (ord : A -> A -> bool) (a : A) (T : BinTree A),
    snd (find' A ord a T) <= 1 + height A T.
Proof.
  unfold find'. intros. apply find_t_complex.
Qed.

Lemma min_t_complex :
  forall (A : Type) (T : BinTree A) (t : nat),
    snd (min_t A t T) <= t + height A T.
Proof.
  induction T; intros; cbn.
  - destruct T1.
    + apply Nat.le_trans with (S t + height A (Node A a0 T1_1 T1_2)).
      * apply IHT1.
      * rewrite Nat.add_succ_r. rewrite <- Nat.add_succ_l. apply Nat.add_le_mono_l.
        apply Nat.le_max_l.
    + cbn. rewrite Nat.add_succ_r. intuition.
  - intuition.
Qed.

Theorem min'_complex :
  forall (A : Type) (T : BinTree A),
    snd (min' A T) <= 1 + height A T.
Proof.
  unfold min'. intros. apply min_t_complex.
Qed.

Lemma max_t_complex :
  forall (A : Type) (T : BinTree A) (t : nat),
    snd (max_t A t T) <= t + height A T.
Proof.
  induction T; intros; cbn.
  - destruct T2.
    + apply Nat.le_trans with (S t + height A (Node A a0 T2_1 T2_2)).
      * apply IHT2.
      * rewrite Nat.add_succ_r. rewrite <- Nat.add_succ_l. apply Nat.add_le_mono_l.
        apply Nat.le_max_r.
    + cbn. rewrite Nat.add_succ_r. intuition.
  - intuition.
Qed.

Theorem max'_complex :
  forall (A : Type) (T : BinTree A),
    snd (max' A T) <= 1 + height A T.
Proof.
  unfold max'. intros. apply max_t_complex.
Qed.

Lemma removeMax_t_complex :
  forall (A : Type) (T : BinTree A) (t : nat),
    snd (removeMax_t A t T) <= t + height A T.
Proof.
  induction T; intros; cbn.
  - destruct T2.
    + apply Nat.le_trans with (S t + height A (Node A a0 T2_1 T2_2)).
      * unfold snd. fold (snd (removeMax_t A (S t) (Node A a0 T2_1 T2_2))). apply IHT2.
      * rewrite Nat.add_succ_r. rewrite <- Nat.add_succ_l. apply Nat.add_le_mono_l.
        apply Nat.le_max_r.
    + cbn. rewrite Nat.add_succ_r. intuition.
  - intuition.
Qed.

Theorem removeMax'_complex :
  forall (A : Type) (T : BinTree A),
    snd (removeMax' A T) <= 1 + height A T.
Proof.
  unfold removeMax'. intros. apply removeMax_t_complex.
Qed.

Theorem root'_complex :
  forall (A : Type) (T : BinTree A),
    snd (root' A T) = 1.
Proof.
  destruct T; trivial.
Qed.

Theorem remove'_complex :
  forall (A : Type) (T : BinTree A),
    snd (remove' A T) <= 1 + 2 * height A T.
Proof.
  destruct T; cbn.
  - assert (forall (A B : Type) (p : A * B), p = (fst p, snd p)).
    + destruct p. trivial.
    + rewrite H with (Maybe A) nat (max' A T1). destruct (fst (max' A T1)).
      * cbn. apply le_n_S. rewrite <-Nat.add_succ_l. apply Nat.add_le_mono.
        -- apply Nat.le_trans with (1 + height A T1).
          ++ apply max'_complex.
          ++ cbn. apply le_n_S, Nat.le_max_l.
        -- apply Nat.le_trans with (1 + height A T1).
          ++ apply removeMax'_complex.
          ++ cbn. apply le_n_S. rewrite Nat.add_0_r. apply Nat.le_max_l.
      * cbn. apply le_n_S. rewrite <-Nat.add_succ_l. apply le_plus_trans.
        apply le_trans with (1 + height A T1).
        -- apply max'_complex.
        -- apply le_n_S, Nat.le_max_l.
  - trivial.
Qed.

Lemma delete_t_complex :
  forall (A : Type) (ord : A -> A -> bool) (a : A) (T : BinTree A) (t : nat),
    snd (delete_t A t ord a T) <= t + 2 * (1 + height A T).
Proof.
  induction T; intros; cbn.
  - destruct (ord a a0); cbn.
    + destruct (ord a0 a); cbn.
      * rewrite Nat.add_comm. apply le_plus_trans.
        assert (forall (A B : Type) (p : A * B), p = (fst p, snd p)).
        -- destruct p. trivial.
        -- rewrite H with (Maybe A) nat (max' A T1). destruct (fst (max' A T1)).
          ++ cbn. apply le_n_S, le_n_S. rewrite Nat.add_succ_r, <-Nat.add_succ_l.
             apply Nat.add_le_mono.
            ** apply Nat.le_trans with (1 + height A T1).
              --- apply max'_complex.
              --- cbn. apply le_n_S, Nat.le_max_l.
            ** apply Nat.le_trans with (1 + height A T1).
              --- apply removeMax'_complex.
              --- cbn. apply le_n_S. rewrite Nat.add_0_r. apply Nat.le_max_l.
          ++ cbn. apply le_n_S, le_n_S. rewrite Nat.add_succ_r, <-Nat.add_succ_l.
             apply le_plus_trans, Nat.le_trans with (1 + height A T1).
             ** apply max'_complex.
             ** apply le_n_S, Nat.le_max_l.
      * rewrite Nat.add_succ_r, Nat.add_succ_r. apply le_n_S.
        apply Nat.le_trans with (S t + 2 * (1 + height A T1)).
        -- apply IHT1.
        -- cbn. apply le_n_S, Nat.add_le_mono_l.
           rewrite Nat.add_succ_r, Nat.add_succ_r, Nat.add_succ_r. apply le_n_S, le_n_S.
           apply Nat.add_le_mono.
          ++ apply Nat.le_max_l.
          ++ apply Nat.add_le_mono_r, Nat.le_max_l.
    + apply Nat.le_trans with (S t + 2 * (1 + height A T2)).
      * apply IHT2.
      * cbn. rewrite <-Nat.add_succ_r, <-Nat.add_succ_r.
        apply Nat.add_le_mono_l, le_S, le_n_S, Nat.add_le_mono.
        -- apply Nat.le_max_r.
        -- apply le_n_S, le_n_S, Nat.add_le_mono_r, Nat.le_max_r.
  - intuition.
Qed.

Theorem delete'_complex :
  forall (A : Type) (ord : A -> A -> bool) (a : A) (T : BinTree A),
    snd (delete' A ord a T) <= 1 + 2 * (1 + height A T).
Proof.
  unfold delete'. intros. apply delete_t_complex.
Qed.

Fact pow2_positive :
  forall n : nat, 1 <= 2 ^ n.
Proof.
  induction n; cbn.
  - trivial.
  - intuition.
Qed.

Theorem size'_complex :
  forall (A : Type) (T : BinTree A),
    snd (size' A T) <= 2 ^ (1 + height A T) - 1.
Proof.
  induction T; cbn.
  - apply Nat.le_trans with (S (2 ^ (1 + height A T1) + 2 ^ (1 + height A T2) - 2)).
    + apply le_n_S.
      rewrite <-Nat.add_1_l, Nat.sub_add_distr, Nat.add_1_l, <-Nat.add_sub_assoc.
      rewrite Nat.add_sub_swap. apply Nat.add_le_mono; assumption.
      1-2: apply pow2_positive.
    + rewrite <-Nat.sub_succ_l.
      * cbn. apply Nat.sub_le_mono_r. apply Nat.add_le_mono.
        -- apply Nat.add_le_mono.
          ++ apply Nat.pow_le_mono_r.
            ** intro. inversion H.
            ** apply Nat.le_max_l.
          ++ apply Nat.add_le_mono_r, Nat.pow_le_mono_r.
            ** intro. inversion H.
            ** apply Nat.le_max_l.
        -- rewrite Nat.add_0_r, Nat.add_0_r, Nat.add_0_r. apply Nat.add_le_mono.
          ++ apply Nat.pow_le_mono_r.
            ** intro. inversion H.
            ** apply Nat.le_max_r.
          ++ apply Nat.pow_le_mono_r.
            ** intro. inversion H.
            ** apply Nat.le_max_r.
      * rewrite <-Nat.add_1_l.
        apply Nat.add_le_mono; rewrite Nat.add_1_r; apply pow2_positive.
  - trivial.
Qed.
