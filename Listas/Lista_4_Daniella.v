(** * Métodos Formais - Lista de Exercícios 4

NOME: Daniella Martins Vasconcellos *)

Require Export Arith.


Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros. induction n. reflexivity. inversion IHn. 
  - apply le_S. reflexivity.
  -inversion IHn.
    + apply le_S. rewrite H0. apply IHn.
    + rewrite H0. apply le_S. apply IHn.
Qed.

Print le_n.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros.  induction H.
  - apply le_n.
  - apply le_S. apply IHle.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros. inversion H. 
  - reflexivity.
  - rewrite <- H1. apply le_S. reflexivity.
Qed. 


Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros. induction H0. 
  - apply H.
  - apply le_S. apply IHle.
Qed.


Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros. apply Sn_le_Sm__n_le_m. induction b.
  -  simpl. rewrite <- plus_n_O. apply le_n.
  - apply le_S. rewrite <- plus_n_Sm. apply IHb.
Qed.

Theorem lt_ge_cases : forall n m,
  n < m \/ n >= m.
Proof.
  intros n m.
  destruct m.
  - right. apply O_le_n.
  - induction n.
  + left. apply n_le_m__Sn_le_Sm. apply O_le_n.
  + destruct IHn.
  * destruct H.
  right. apply le_n.
  left. apply n_le_m__Sn_le_Sm. apply H.
  * right. apply le_S. apply H.
Qed.

Inductive le' : nat -> nat -> Prop :=
  | le_0' m : le' 0 m
  | le_S' n m (H : le' n m) : le' (S n) (S m).

Lemma n_le'_m__Sn_le'_Sm : forall a b, le' a b -> le' (S a) (S b).
Proof.
  intros.
  apply le_S'.
  apply H.
Qed.  

Lemma le'_n_n : forall a, le' a a.
Proof.
  intros.
  induction a.
  apply le_0'.
  apply le_S'.
  apply IHa.
Qed.
  
Lemma le'_n_Sm : forall a b, le' a b -> le' a (S b). 
Proof.
  intros. generalize dependent b. induction a.
  - intros. apply le_0'.
  - intros. induction b.
    + inversion H.
    + apply le_S'. apply IHa. inversion H. apply H2.
Qed.


Theorem le_le' : forall a b, le a b <-> le' a b.
Proof.
  intros a b. split.
  - intros H. induction H as [|b' Hab IH].
  + apply le'_n_n.
  + apply le'_n_Sm in IH. apply IH.
  - intros H. induction H as [ b' | a' b' Hab IH].
  + apply O_le_n.
  + apply n_le_m__Sn_le_Sm. apply IH.
Qed. 

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
  unfold lt.
  intros. split.
  - induction n2.
    + rewrite <- plus_n_O in H. apply H.
    + apply IHn2. apply le_S in H. apply Sn_le_Sm__n_le_m in H.
      rewrite plus_comm in H. simpl in H. rewrite plus_comm in H.
      apply H.
  - induction n1.
    + apply H.
    + apply IHn1. apply le_S in H. apply Sn_le_Sm__n_le_m in H. apply H.
Qed.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  unfold lt. intros. apply le_S in H. apply H.
Qed.
