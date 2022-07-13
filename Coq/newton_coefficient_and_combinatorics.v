(* formulas from Delta 08/2020 *)

Require Import Arith.

Fixpoint Newton_Coefficient' (n k : nat) : nat :=
match n with
  | 0 =>
  match k with
    | 0 => 1
    | S k' => 0
  end
  | S n' =>
  match k with
    | 0 => 1
    | S k' => (Newton_Coefficient' n' k') + (Newton_Coefficient' n' k)
  end
end.

Fixpoint Newton_Coefficient (n k : nat) : nat :=
match k with
  | 0 => 1
  | S k' =>
  match n with
    | 0 => 0
    | S n' => (Newton_Coefficient n' k') + (Newton_Coefficient n' k)
  end
end.

Fact Definitions_Equivalence :
  forall n k : nat, Newton_Coefficient n k = Newton_Coefficient' n k.
Proof.
  induction n.
  - trivial.
  - cbn. destruct k.
    + reflexivity.
    + rewrite IHn. rewrite IHn. reflexivity.
Qed.

Fact Step_NC :
  forall n k : nat,
    Newton_Coefficient (S n) (S k) = Newton_Coefficient n k + Newton_Coefficient n (S k).
Proof.
  trivial.
Qed.

Fixpoint Linear_Sum (n : nat) : nat :=
match n with
  | 0 => 0
  | S n' => n + Linear_Sum n'
end.

Fact LS_Arithmetical_Formula :
  forall n : nat, 2 * Linear_Sum n = n * (S n).
Proof.
  induction n; cbn.
  - reflexivity.
  - rewrite Nat.mul_succ_r, <- IHn. cbn. rewrite <- plus_n_O, <- plus_n_O, Nat.add_comm. cbn.
    rewrite Nat.add_assoc, <- (Nat.add_assoc (Linear_Sum n) (Linear_Sum n) n), Nat.add_assoc.
    rewrite (Nat.add_comm (Linear_Sum n) n), Nat.add_assoc. reflexivity.
Qed.

Fact NC_k0_Arithmetical_Formula :
  forall n : nat, Newton_Coefficient n 0 = 1.
Proof.
  destruct n; trivial.
Qed.

Fact NC_k1_Arithmetical_Formula :
  forall n : nat, Newton_Coefficient n 1 = n.
Proof.
  induction n; cbn.
  - reflexivity.
  - rewrite NC_k0_Arithmetical_Formula. cbn. f_equal. apply IHn.
Qed.

Fact NC_k2_Arithmetical_Formula :
  forall n : nat, 2 * Newton_Coefficient (S n) 2 = n * (S n).
Proof.
  induction n; cbn.
  - reflexivity.
  - rewrite Nat.mul_succ_r, <- IHn. cbn. rewrite NC_k1_Arithmetical_Formula.
    rewrite NC_k0_Arithmetical_Formula. cbn. rewrite <- plus_n_O, <- plus_n_O, Nat.add_assoc.
    rewrite Nat.add_comm. cbn. f_equal. f_equal.
    rewrite (Nat.add_comm (n + Newton_Coefficient n 2 + (n + Newton_Coefficient n 2)) n).
    rewrite Nat.add_assoc, (Nat.add_comm (n + n + Newton_Coefficient n 2) (n + n)).
    rewrite Nat.add_assoc, Nat.add_assoc, Nat.add_assoc, Nat.add_assoc, Nat.add_assoc.
    f_equal. rewrite (Nat.add_comm (n + n + (n + Newton_Coefficient n 2)) n), Nat.add_assoc.
    rewrite Nat.add_assoc. f_equal. f_equal. symmetry. apply Nat.add_assoc.
Qed.

Fact NC_n_lt_k_Arithmetical_Formula :
  forall n k : nat, n < k -> Newton_Coefficient n k = 0.
Proof.
  induction n; destruct k; cbn; intros.
  - inversion H.
  - reflexivity.
  - inversion H.
  - rewrite IHn.
    + rewrite IHn.
      * cbn. reflexivity.
      * apply lt_S, lt_S_n. exact H.
    + apply lt_S_n. exact H.
Qed.

Fact NC_n_eq_k_Arithmetical_Formula :
  forall n : nat, Newton_Coefficient n n = 1.
Proof.
  induction n; cbn.
  - reflexivity.
  - rewrite IHn, NC_n_lt_k_Arithmetical_Formula.
    + reflexivity.
    + apply Nat.lt_succ_diag_r.
Qed.

Lemma NC_symmetric_k :
  forall n k : nat, k <= n -> Newton_Coefficient n k = Newton_Coefficient n (n - k).
Proof.
  induction n; intros.
  - apply le_n_0_eq in H. rewrite H, Nat.sub_diag. rewrite NC_k0_Arithmetical_Formula.
    apply NC_n_eq_k_Arithmetical_Formula.
  - inversion H.
    + rewrite Nat.sub_diag, NC_k0_Arithmetical_Formula. apply NC_n_eq_k_Arithmetical_Formula.
    + rewrite Nat.sub_succ_l.
      * cbn. destruct k.
        -- rewrite Nat.sub_0_r, NC_n_eq_k_Arithmetical_Formula.
           rewrite NC_n_lt_k_Arithmetical_Formula.
           ++ reflexivity.
           ++ apply Nat.lt_succ_diag_r.
        -- rewrite IHn.
           ++ rewrite (IHn (S k)).
             ** rewrite <- Nat.sub_succ_l.
               --- cbn. apply Nat.add_comm.
               --- exact H1.
             ** exact H1.
           ++ apply le_S_n. exact H.
      * exact H1.
Qed.

Theorem NC_k2_eq_LS :
  forall n : nat, Newton_Coefficient (S n) 2 = Linear_Sum n.
Proof.
  induction n; cbn.
  - reflexivity.
  - rewrite <- IHn. cbn. rewrite NC_k1_Arithmetical_Formula, NC_k0_Arithmetical_Formula.
    cbn. reflexivity.
Qed.

Fixpoint Sum_Of_Powers (p n : nat) : nat :=
match n with
  | 0 => p ^ 0
  | S n' => (p ^ n) + Sum_Of_Powers p n'
end.

Theorem SOP_Arithmetical_Formula :
  forall n p : nat, S (p * (Sum_Of_Powers (S p) n)) = (S p) ^ (S n).
Proof.
  induction n.
  - trivial.
  - intros. rewrite Nat.pow_succ_r.
    + rewrite <- IHn. cbn. rewrite (Nat.add_comm (S p ^ n) (p * S p ^ n)), <- Nat.mul_succ_l.
      rewrite <- Nat.pow_succ_r.
      * rewrite IHn, <- Nat.mul_add_distr_l, Nat.add_comm. reflexivity.
      * apply Nat.le_0_l.
    + apply Nat.le_0_l.
Qed.

Fixpoint General_Sum_Of_Newton_Coefficients (n k : nat) : nat :=
match k with
  | 0 => Newton_Coefficient n 0
  | S k' => (Newton_Coefficient n k) + General_Sum_Of_Newton_Coefficients n k'
end.

Definition Sum_Of_Newton_Coefficients (n : nat) : nat :=
  General_Sum_Of_Newton_Coefficients n n.

Fact Step_GNOSC :
  forall n k : nat, General_Sum_Of_Newton_Coefficients n (S k)
    = (Newton_Coefficient n (S k)) + General_Sum_Of_Newton_Coefficients n k.
Proof.
  trivial.
Qed.

Fact Zero_GSONC :
  forall n : nat, General_Sum_Of_Newton_Coefficients n 0 = 1.
Proof.
  destruct n; cbn; reflexivity.
Qed.

Fact Double_GSONC :
  forall k n : nat, General_Sum_Of_Newton_Coefficients (S n) (S k)
    = General_Sum_Of_Newton_Coefficients n (S k) + General_Sum_Of_Newton_Coefficients n k.
Proof.
  induction k; cbn; intros.
  - rewrite NC_k0_Arithmetical_Formula. f_equal. apply Nat.add_comm.
  - rewrite <- (Step_NC n k), <- Step_GNOSC, IHk. cbn.
    rewrite Nat.add_assoc, Nat.add_assoc, Nat.add_assoc. f_equal.
    rewrite
      (Nat.add_comm
        (Newton_Coefficient n (S (S k)) + (Newton_Coefficient n (S k)
          + General_Sum_Of_Newton_Coefficients n k)) (Newton_Coefficient n (S k))).
    rewrite Nat.add_assoc, Nat.add_assoc. reflexivity.
Qed.

Fact Double_SONC :
  forall n : nat, Sum_Of_Newton_Coefficients (S n) = 2 * Sum_Of_Newton_Coefficients n.
Proof.
  intros. unfold Sum_Of_Newton_Coefficients. rewrite Double_GSONC. cbn.
  rewrite <- plus_n_O, NC_n_lt_k_Arithmetical_Formula.
  - trivial.
  - apply Nat.lt_succ_diag_r.
Qed.

Theorem SONC_Arithmetical_Formula :
  forall n : nat, Sum_Of_Newton_Coefficients n = 2 ^ n.
Proof.
  induction n.
  - reflexivity.
  - rewrite Double_SONC. cbn. rewrite IHn. reflexivity.
Qed.

Definition Product_Of_Newton_Coefficient_Power_And_Linear_Coefficient (n k p : nat) : nat :=
k * (p ^ k) * (Newton_Coefficient n k).

Fixpoint General_Sum_Of_PONCPALC (n k p : nat) : nat :=
match k with
  | 0 => Product_Of_Newton_Coefficient_Power_And_Linear_Coefficient n 0 p
  | S k' => (Product_Of_Newton_Coefficient_Power_And_Linear_Coefficient n k p)
                   + General_Sum_Of_PONCPALC n k' p
end.

Definition Sum_Of_PONCPALC (n p : nat) : nat :=
General_Sum_Of_PONCPALC n n p.

Fact Step_GSOPONCPALC :
  forall n k p : nat, General_Sum_Of_PONCPALC n (S k) p
    = (Product_Of_Newton_Coefficient_Power_And_Linear_Coefficient n (S k) p)
         + General_Sum_Of_PONCPALC n k p.
Proof.
  trivial.
Qed.

Definition Product_Of_Newton_Coefficient_And_Power (n k p : nat) : nat :=
(p ^ k) * (Newton_Coefficient n k).

Fixpoint General_Sum_Of_PONCAP (n k p : nat) : nat :=
match k with
  | 0 => Product_Of_Newton_Coefficient_And_Power n 0 p
  | S k' => (Product_Of_Newton_Coefficient_And_Power n k p)
                   + General_Sum_Of_PONCAP n k' p
end.

Definition Sum_Of_PONCAP (n p : nat) : nat :=
General_Sum_Of_PONCAP n n p.

Fact Step_GSOPONCAP :
  forall n k p : nat, General_Sum_Of_PONCAP n (S k) p
    = (Product_Of_Newton_Coefficient_And_Power n (S k) p)
         + General_Sum_Of_PONCAP n k p.
Proof.
  trivial.
Qed.

Fact Zero_GSOPONCAP :
  forall k p : nat, General_Sum_Of_PONCAP 0 k p = 1.
Proof.
  induction k; intros; cbn.
  - reflexivity.
  - rewrite Nat.mul_0_r. cbn. apply IHk.
Qed.

Fact Double_GSOPONCAP :
  forall k n p : nat, General_Sum_Of_PONCAP (S n) (S k) p
    = General_Sum_Of_PONCAP n (S k) p + p * General_Sum_Of_PONCAP n k p.
Proof.
  induction k; intros.
  - cbn. rewrite NC_k0_Arithmetical_Formula, Nat.mul_add_distr_l. cbn.
    rewrite Nat.mul_1_r, (Nat.add_comm (p * 1 * Newton_Coefficient n 1 + 1) (p * 1)).
    symmetry. apply Nat.add_assoc.
  - rewrite Step_GSOPONCAP, (Step_GSOPONCAP n k), (Step_GSOPONCAP n (S k)).
    unfold Product_Of_Newton_Coefficient_And_Power.
    rewrite Nat.mul_add_distr_l, Nat.mul_assoc, Nat.pow_succ_r.
    + rewrite Nat.add_assoc.
      rewrite <-
        (Nat.add_assoc
          (p * p ^ S k * Newton_Coefficient n (S (S k)))
          (General_Sum_Of_PONCAP n (S k) p) (p * p ^ S k * Newton_Coefficient n (S k))).
      rewrite
        (Nat.add_comm
          (General_Sum_Of_PONCAP n (S k) p) (p * p ^ S k * Newton_Coefficient n (S k))).
      rewrite Nat.add_assoc, IHk, Nat.add_assoc. f_equal. f_equal. rewrite Step_NC.
      rewrite (Nat.add_comm (Newton_Coefficient n (S k)) (Newton_Coefficient n (S (S k)))).
      apply Nat.mul_add_distr_l.
    + apply le_0_n.
Qed.

Lemma Step_GSOPONCAP_SOPONCAP :
  forall n p : nat, General_Sum_Of_PONCAP (S n) n p + p ^ (S n)
    = (S p) * Sum_Of_PONCAP n p.
Proof.
  unfold Sum_Of_PONCAP. induction n.
  - reflexivity.
  - intros. rewrite Double_GSOPONCAP, Double_GSOPONCAP, Nat.pow_succ_r.
    + rewrite Nat.mul_succ_l, <- Nat.add_assoc, <- Nat.mul_add_distr_l, IHn, Nat.add_comm.
      f_equal. f_equal. cbn. f_equal. rewrite NC_n_lt_k_Arithmetical_Formula.
      * rewrite Nat.mul_0_r. cbn. reflexivity.
      * apply Nat.lt_succ_diag_r.
    + apply le_0_n.
Qed.

Lemma Step_SOPONCAP :
  forall n p : nat, (Sum_Of_PONCAP (S n) p) + (p ^ (S n))
    = (Product_Of_Newton_Coefficient_And_Power (S n) (S n) p)
         + ((S p) * Sum_Of_PONCAP n p).
Proof.
  intros. rewrite <- Step_GSOPONCAP_SOPONCAP. cbn. symmetry. apply Nat.add_assoc.
Qed.

(* not from Delta *)
Theorem SOPONCAP_Arithmetical_Formula :
  forall n p : nat, Sum_Of_PONCAP n p = (S p) ^ n.
Proof.
  induction n; intros.
  - reflexivity.
  - rewrite Nat.pow_succ_r.
    + rewrite <- IHn.
      apply (plus_reg_l (Sum_Of_PONCAP (S n) p) (S p * Sum_Of_PONCAP n p) (p ^ (S n))).
      rewrite Nat.add_comm, Step_SOPONCAP. f_equal.
      unfold Product_Of_Newton_Coefficient_And_Power.
      rewrite NC_n_eq_k_Arithmetical_Formula. apply Nat.mul_1_r.
    + apply le_0_n.
Qed.

Fact Zero_GSOPONCPALC :
  forall k p : nat, General_Sum_Of_PONCPALC 0 k p = 0.
Proof.
  induction k; intros; cbn.
  - reflexivity.
  - rewrite IHk, Nat.mul_0_r. reflexivity.
Qed.

Fact Double_GSOPONCPALC :
  forall k n p : nat, General_Sum_Of_PONCPALC (S n) (S k) p
    = General_Sum_Of_PONCPALC n (S k) p
        + p * (General_Sum_Of_PONCPALC n k p + General_Sum_Of_PONCAP n k p).
Proof.
  induction k; intros.
  - cbn. rewrite NC_k0_Arithmetical_Formula. cbn.
    rewrite Nat.add_0_r, Nat.add_0_r, Nat.add_0_r. apply Nat.mul_succ_r.
  - rewrite (Step_GSOPONCPALC n k), Step_GSOPONCPALC, IHk, (Step_GSOPONCPALC n (S k)).
    unfold Product_Of_Newton_Coefficient_Power_And_Linear_Coefficient.
    rewrite Step_GSOPONCAP. unfold Product_Of_Newton_Coefficient_And_Power.
    rewrite Nat.add_assoc, Nat.add_assoc.
    rewrite
      (Nat.add_comm
        (S k * p ^ S k * Newton_Coefficient n (S k) + General_Sum_Of_PONCPALC n k p)
        (p ^ S k * Newton_Coefficient n (S k))). rewrite Nat.add_assoc.
    rewrite <- Nat.mul_add_distr_r, (Nat.add_comm (p ^ (S k)) ((S k) * p ^ (S k))).
    rewrite <- Nat.mul_succ_l.
    rewrite <-
      (Nat.add_assoc
        (S (S k) * p ^ S k * Newton_Coefficient n (S k))
        (General_Sum_Of_PONCPALC n k p) (General_Sum_Of_PONCAP n k p)).
    rewrite
      (Nat.mul_add_distr_l p (S (S k) * p ^ S k * Newton_Coefficient n (S k))
        (General_Sum_Of_PONCPALC n k p + General_Sum_Of_PONCAP n k p)).
    rewrite Nat.add_assoc. f_equal.
    rewrite
      (Nat.add_comm
        (S (S k) * p ^ S (S k) * Newton_Coefficient n (S (S k))
         + General_Sum_Of_PONCPALC n (S k) p)
        (p * (S (S k) * p ^ S k * Newton_Coefficient n (S k)))).
    rewrite Nat.add_assoc. f_equal. rewrite Step_NC, Nat.mul_add_distr_l. f_equal.
    rewrite Nat.mul_assoc. f_equal. rewrite Nat.mul_assoc, (Nat.mul_comm p (S (S k))).
    apply Nat.mul_assoc.
Qed.

Lemma Step_GSOPONCPALC_SOPONCPALC :
  forall n p : nat, General_Sum_Of_PONCPALC (S n) n p + (S n) * (p ^ (S n))
    = Sum_Of_PONCPALC n p + p * (Sum_Of_PONCPALC n p + Sum_Of_PONCAP n p).
Proof.
  unfold Sum_Of_PONCPALC, Sum_Of_PONCAP. destruct n; intros.
  - cbn. apply Nat.add_0_r.
  - rewrite Double_GSOPONCPALC, Nat.pow_succ_r.
    + rewrite Nat.mul_assoc, (Nat.mul_comm (S (S n)) p), <- Nat.add_assoc. f_equal.
      rewrite <- Nat.mul_assoc, <- Nat.mul_add_distr_l. f_equal.
      rewrite Step_GSOPONCPALC, Step_GSOPONCAP.
      unfold Product_Of_Newton_Coefficient_Power_And_Linear_Coefficient.
      unfold Product_Of_Newton_Coefficient_And_Power.
      rewrite NC_n_eq_k_Arithmetical_Formula, Nat.mul_1_r, Nat.mul_1_r.
      rewrite (Nat.add_comm (p ^ S n) (General_Sum_Of_PONCAP (S n) n p)).
      rewrite <-
        (Nat.add_assoc
          (S n * p ^ S n) (General_Sum_Of_PONCPALC (S n) n p)
          (General_Sum_Of_PONCAP (S n) n p + p ^ S n)).
      rewrite
        (Nat.add_comm (S n * p ^ S n)
          (General_Sum_Of_PONCPALC (S n) n p + (General_Sum_Of_PONCAP (S n) n p + p ^ S n))).
      rewrite <- Nat.add_assoc, <- Nat.add_assoc, <- Nat.add_assoc. f_equal.
    + apply le_0_n.
Qed.

Lemma Step_SOPONCPALC :
  forall n p : nat, Sum_Of_PONCPALC (S n) p + ((S n) * (p ^ (S n)))
    = Product_Of_Newton_Coefficient_Power_And_Linear_Coefficient (S n) (S n) p
        + (Sum_Of_PONCPALC n p + p * (Sum_Of_PONCPALC n p + Sum_Of_PONCAP n p)).
Proof.
  intros. rewrite <- Step_GSOPONCPALC_SOPONCPALC, Nat.add_assoc, <- Step_GSOPONCPALC.
  unfold Sum_Of_PONCPALC. reflexivity.
Qed.

Theorem SOPONCPALC_Arithmetic_Formula :
  forall n p : nat, Sum_Of_PONCPALC n p = n * p * ((p + 1) ^ (n - 1)).
Proof.
  induction n; intros.
  - trivial.
  - apply (plus_reg_l (Sum_Of_PONCPALC (S n) p)
      (S n * p * (p + 1) ^ (S n - 1)) (S n * p ^ S n)). rewrite Nat.add_comm, Step_SOPONCPALC.
    rewrite IHn, SOPONCAP_Arithmetical_Formula.
    unfold Product_Of_Newton_Coefficient_Power_And_Linear_Coefficient.
    rewrite NC_n_eq_k_Arithmetical_Formula, Nat.mul_1_r. apply f_equal2_plus.
    + reflexivity.
    + rewrite (Nat.add_comm p 1). destruct n; cbn.
      * rewrite Nat.add_0_r. reflexivity.
      * rewrite Nat.sub_0_r, (Nat.add_comm (S p ^ n) (p * S p ^ n)), <- Nat.mul_succ_l.
        rewrite Nat.mul_add_distr_l, Nat.add_assoc.
        rewrite (Nat.add_comm ((p + n * p) * S p ^ n) (p * ((p + n * p) * S p ^ n))).
        rewrite <- Nat.mul_succ_l, Nat.mul_assoc, (Nat.mul_comm (S p) (p + n * p)).
        rewrite <- Nat.mul_assoc, <- Nat.mul_add_distr_r. f_equal. apply Nat.add_comm.
Qed.

Fixpoint Factorial (n : nat) : nat :=
match n with
  | 0 => 1
  | S n' => n * Factorial n'
end.

Fixpoint Limited_Factorial (n k : nat) : nat :=
match k with
  | 0 => 1
  | S k' =>
  match n with
    | 0 => 0
    | S n' => n * Limited_Factorial n' k'
  end
end.

Fact Step_F :
  forall n : nat, Factorial (S n) = (S n) * Factorial n.
Proof.
  trivial.
Qed.

Fact Step_LF :
  forall n k : nat, Limited_Factorial (S n) (S k) = (S n) * Limited_Factorial n k.
Proof.
  trivial.
Qed.

Theorem LF_n_lt_k_Arithmetical_Formula :
  forall n k : nat, n < k -> Limited_Factorial n k = 0.
Proof.
  induction n; destruct k; cbn; intros.
  - destruct (Nat.nlt_0_r 0 H).
  - reflexivity.
  - destruct (Nat.nlt_0_r (S n) H).
  - rewrite IHn.
    + cbn. apply Nat.mul_0_r.
    + apply lt_S_n. exact H.
Qed.

Theorem LF_n_eq_k_Arithmetical_Formula :
  forall n : nat, Limited_Factorial n n = Factorial n.
Proof.
  induction n; cbn.
  - reflexivity.
  - rewrite IHn. reflexivity.
Qed.

Theorem LF_k_le_n_Arithmetical_Formula :
  forall n k : nat, k <= n -> (Limited_Factorial n k) * (Factorial (n - k)) = Factorial n.
Proof.
  induction n; intros.
  - rewrite <- (le_n_0_eq k H). cbn. reflexivity.
  - destruct k; cbn.
    + apply Nat.add_0_r.
    + rewrite Nat.mul_add_distr_r, <- Nat.mul_assoc, IHn.
      * reflexivity.
      * apply le_S_n. exact H.
Qed.

Lemma Step_Diag_NC :
  forall n k : nat, (S k) * Newton_Coefficient (S n) (S k) = (S n) * Newton_Coefficient n k.
Proof.
  induction n; destruct k.
  - trivial.
  - cbn. apply Nat.mul_0_r.
  - cbn. rewrite NC_k0_Arithmetical_Formula, NC_k1_Arithmetical_Formula. cbn. f_equal.
    f_equal. rewrite Nat.mul_1_r. apply Nat.add_0_r.
  - rewrite Step_NC, Nat.mul_add_distr_l, IHn, Nat.mul_succ_l, IHn. rewrite Nat.add_comm.
    rewrite Nat.add_assoc, <- Nat.mul_add_distr_l.
    rewrite (Nat.add_comm (Newton_Coefficient n (S k)) (Newton_Coefficient n k)).
    rewrite <- Step_NC. symmetry. apply Nat.mul_succ_l.
Qed.

Theorem NC_Arithmetical_Formula :
  forall n k : nat, (Newton_Coefficient n k) * (Factorial k) = Limited_Factorial n k.
Proof.
  induction n; destruct k.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite Step_F, Nat.mul_assoc, (Nat.mul_comm (Newton_Coefficient (S n) (S k)) (S k)).
    rewrite Step_Diag_NC, <- Nat.mul_assoc, IHn. cbn. reflexivity.
Qed.

Theorem NC_Limited_Arithmetical_Formula :
  forall n k : nat,
    k <= n -> (Newton_Coefficient n k) * (Factorial k) * (Factorial (n - k)) = Factorial n.
Proof.
  induction n; intros; destruct k.
  - reflexivity.
  - destruct (Nat.nle_succ_0 k H).
  - apply Nat.add_0_r.
  - rewrite Nat.sub_succ, Step_F, Nat.mul_assoc.
    rewrite (Nat.mul_comm (Newton_Coefficient (S n) (S k)) (S k)), Step_Diag_NC.
    rewrite <- Nat.mul_assoc, <- Nat.mul_assoc.
    rewrite (Nat.mul_assoc (Newton_Coefficient n k) (Factorial k) (Factorial (n - k))), IHn.
    + cbn. reflexivity.
    + apply le_S_n. exact H.
Qed.

Fixpoint General_Vertical_Sum_Of_NC (n k : nat) : nat :=
match n with
  | 0 => 0
  | S n' => (Newton_Coefficient (n' + k) k) + (General_Vertical_Sum_Of_NC n' k)
end.

Definition Vertical_Sum_Of_NC (n k : nat) : nat :=
  General_Vertical_Sum_Of_NC ((S n) - k) k.

Theorem GVSONC_Arithmetical_Formula :
  forall n k : nat, General_Vertical_Sum_Of_NC n k = Newton_Coefficient (n + k) (S k).
Proof.
  induction n; intros; cbn.
  - symmetry. apply NC_n_lt_k_Arithmetical_Formula, Nat.lt_succ_diag_r.
  - rewrite IHn. reflexivity.
Qed.

Theorem VSONC_Arithmetical_Formula :
  forall n k : nat, Vertical_Sum_Of_NC n k = Newton_Coefficient (S n) (S k).
Proof.
  intros. unfold Vertical_Sum_Of_NC. rewrite GVSONC_Arithmetical_Formula.
  destruct (Nat.le_gt_cases k (S n)).
  - rewrite Nat.sub_add.
    + reflexivity.
    + exact H.
  - destruct (Nat.sub_0_le (S n) k). rewrite (NC_n_lt_k_Arithmetical_Formula (S n) (S k)).
    + rewrite H1.
      * cbn. apply NC_n_lt_k_Arithmetical_Formula, Nat.lt_succ_diag_r.
      * apply Nat.lt_le_incl, H.
    + apply Nat.lt_lt_succ_r. exact H.
Qed.

Definition NC_N_Plus_I (n i : nat) : nat :=
  Newton_Coefficient (n + i) i.

Fixpoint Sum_Of_NCNPI (n k : nat) : nat :=
match k with
  | 0 => NC_N_Plus_I n 0
  | S k' => (NC_N_Plus_I n k) + (Sum_Of_NCNPI n k')
end.

Theorem SONCNPI_Arithmetical_Formula :
  forall n k : nat, Sum_Of_NCNPI n k = Newton_Coefficient (n + k + 1) k.
Proof.
  induction k.
  - rewrite Nat.add_0_r, Nat.add_1_r. cbn. unfold NC_N_Plus_I. rewrite Nat.add_0_r.
    apply NC_k0_Arithmetical_Formula.
  - rewrite (Nat.add_succ_r n k). cbn. unfold NC_N_Plus_I. rewrite IHk, Nat.add_comm.
    f_equal. rewrite <- (Nat.add_1_r k). f_equal. apply Nat.add_assoc.
Qed.

Definition Product_Of_NC (n m k i : nat) : nat :=
  (Newton_Coefficient n i) * (Newton_Coefficient m (k - i)).

Fixpoint General_Sum_Of_PONC (n m k i : nat) : nat :=
match i with
  | 0 => Product_Of_NC n m k 0
  | S i' => (Product_Of_NC n m k i) + (General_Sum_Of_PONC n m k i')
end.

Definition Sum_Of_PONC (n m k : nat) : nat :=
  General_Sum_Of_PONC n m k k.

Fact Step_GSOPONC :
  forall n m k i : nat, General_Sum_Of_PONC n m k (S i)
    = (Product_Of_NC n m k (S i)) + (General_Sum_Of_PONC n m k i).
Proof.
  trivial.
Qed.

Fact lt_sub_pos :
  forall n m : nat, n < m -> 0 < m - n.
Proof.
  intros. destruct H.
  - rewrite Nat.sub_succ_l.
    + apply Nat.lt_0_succ.
    + apply le_n.
  - rewrite Nat.sub_succ_l.
    + apply Nat.lt_0_succ.
    + apply le_S_n, le_S. exact H.
Qed.

Fact Zero_GSOPONC_i_lt_k :
  forall n k i : nat, i < k -> General_Sum_Of_PONC n 0 k i = 0.
Proof.
  induction i; intros; cbn; unfold Product_Of_NC.
  - rewrite NC_k0_Arithmetical_Formula, Nat.sub_0_r. cbn. destruct H; reflexivity.
  - rewrite IHi.
    + rewrite Nat.add_0_r.
      destruct H; rewrite Nat.sub_succ; rewrite (NC_n_lt_k_Arithmetical_Formula 0).
      * apply Nat.mul_0_r.
      * rewrite Nat.sub_succ_l.
        -- apply Nat.lt_0_succ.
        -- apply le_n.
      * apply Nat.mul_0_r.
      * apply lt_sub_pos. unfold lt. apply le_S_n, le_S. exact H.
    + apply lt_S_n, lt_S. exact H.
Qed.

Fact Zero_GSOPONC_k_eq_i :
  forall n k : nat, General_Sum_Of_PONC n 0 k k = Newton_Coefficient n k.
Proof.
  induction k; cbn; unfold Product_Of_NC; cbn.
  - apply Nat.mul_1_r.
  - rewrite Nat.sub_diag, Zero_GSOPONC_i_lt_k.
    + rewrite Nat.add_0_r. apply Nat.mul_1_r.
    + apply Nat.lt_succ_diag_r.
Qed.

Fact Double_GSOPONC :
  forall n m k i : nat,
    i <= k ->
    (General_Sum_Of_PONC n (S m) (S k) i)
    = (General_Sum_Of_PONC n m k i) + (General_Sum_Of_PONC n m (S k) i).
Proof.
  induction i; intros.
  - cbn. unfold Product_Of_NC. cbn. rewrite Nat.mul_add_distr_l. f_equal. f_equal. f_equal.
symmetry. apply Nat.sub_0_r.
  - cbn. rewrite IHi by intuition. unfold Product_Of_NC. rewrite <- Nat.add_assoc.
    rewrite (
      Nat.add_comm (General_Sum_Of_PONC n m k i)
      (Newton_Coefficient n (S i) * Newton_Coefficient m (S k - S i)
       + General_Sum_Of_PONC n m (S k) i)).
    rewrite (Nat.add_comm (General_Sum_Of_PONC n m k i)).
    rewrite Nat.add_assoc, Nat.add_assoc, Nat.add_assoc. f_equal. f_equal.
    rewrite <- Nat.mul_add_distr_l. f_equal. rewrite Nat.sub_succ_l by assumption. cbn.
    reflexivity.
Qed.

Lemma Step_SOPONC :
  forall n m k : nat,
    (Sum_Of_PONC n (S m) (S k))
    = (Sum_Of_PONC n m k) + (Sum_Of_PONC n m (S k)).
Proof.
  unfold Sum_Of_PONC. cbn. intros. rewrite Double_GSOPONC by intuition.
  rewrite Nat.add_assoc, Nat.add_assoc. f_equal. rewrite Nat.add_comm. f_equal.
  destruct n; cbn; trivial. rewrite Nat.sub_diag. f_equal. symmetry.
  apply NC_k0_Arithmetical_Formula.
Qed.

Theorem SOPONC_Arithmeitcal_Formula :
  forall n m k : nat, Sum_Of_PONC n m k = Newton_Coefficient (n + m) k.
Proof.
  induction m; intros.
  - rewrite Nat.add_0_r. unfold Sum_Of_PONC. apply Zero_GSOPONC_k_eq_i.
  - destruct k.
    + cbn. unfold Product_Of_NC. rewrite NC_k0_Arithmetical_Formula. cbn. symmetry.
      apply NC_k0_Arithmetical_Formula.
    + rewrite Step_SOPONC. rewrite IHm, IHm. rewrite Nat.add_succ_r. cbn. reflexivity.
Qed.

(* END *)