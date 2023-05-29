(** * Métodos Formais - Lista de Exercícios 3 
 Não importar nenhum outro módulo.

NOME: Daniella Martins Vasconcellos *)

Require Import PeanoNat.
Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint app {X : Type} (l1 l2 : list X)
             : (list X) :=
  match l1 with
  | nil      => l2
  | cons h t => cons h (app t l2)
  end.


Fixpoint map {X Y: Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.


Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | (h :: t) => P h /\ All P t 
  end.

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.


Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
  Proof.
  intros P Q R.
  split.
  - intros H. destruct H.
    + split. left. apply H. left. apply H.
    + inversion H. split.
      * right. apply H0.
      * right. apply H1.
  - intros H. inversion H as [[HP1 | HQ] [HP2 | HR]].
    left. apply HP1.
    left. apply HP1.
    left. apply HP2.
    right. split. apply HQ. apply HR.
Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
    - (* left *) apply HQ.
    - (* right *) apply HP.
Qed.

Theorem dist_exists_and : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x /\ Q x) -> (exists x, P x) /\ (exists x, Q x).
Proof.
  split.
  - intros. destruct H. exists x. apply proj1 in H. apply H.
  -  destruct H. exists x. apply and_commut in H. apply proj1 in H. apply H.
Qed.

Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
    Proof with intuition.
    intros A B f l y.
    induction l as [|y' l' IHl].
    - simpl. split.
      + intro H. inversion H.
      + intro H. inversion H as [Hm Hn]. apply Hn.
    - simpl. split.
      + intro H. destruct H.
        * exists y'. split. apply H. left. reflexivity.
        * inversion IHl. 
          destruct (H0 H). exists x. split. 
          destruct H2. apply H2. destruct H2. right. apply H3.
      + intro H. destruct H.
        * inversion IHl. inversion H. rewrite IHl. destruct H3.
          left. rewrite H3. apply H2.
          right. exists x. split. apply H2. apply H3.
  Qed.

Lemma In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros. split.
 - intro. induction l.
   + right. apply H.
   + simpl. simpl in H. destruct H.
     * left. left. apply H.
     * apply or_assoc. right. apply IHl. apply H.
 -  intro. induction l.
   + destruct H. induction l'.
     * simpl. destruct H.
     * simpl. simpl in IHl'. right. apply IHl'.
     * simpl. apply H.
   + destruct H. simpl. simpl in H. destruct H.
     * left. apply H.
     * right. apply IHl. left. apply H.
     * simpl. right. apply IHl. right. apply H.
Qed.


Lemma All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
    intros. split. intros.
    - induction l as [| x y].
      + simpl. reflexivity.
      + simpl. split.
        * apply H. simpl. left. reflexivity.
        * apply IHy. intros. apply H. simpl. right. apply H0.
    - induction l as [|x y]. intros.
      + inversion H0. 
      + intros. simpl in H0. simpl in H. destruct H0 as [h' | a']. destruct H as [ah' ha']. 
          rewrite <- h'. apply ah'.
* apply IHy. destruct H as [dan vasco]. apply dan. apply a'. 
  Qed.
