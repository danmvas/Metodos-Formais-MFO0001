(* Lista de Exercícios 5 - Expressões Regulares 

NOME: Daniella Martins Vasconcellos *)

Require Export Coq.Init.Logic.
Require Export Coq.Bool.Bool.
Require Export Coq.Lists.List.
Import ListNotations.

Inductive reg_exp {T : Type} : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp)
  | Union (r1 r2 : reg_exp)
  | Star (r : reg_exp).

Inductive exp_match {T} : list T -> reg_exp -> Prop :=
  | MEmpty : exp_match [] EmptyStr
  | MChar x : exp_match [x] (Char x)
  | MApp s1 re1 s2 re2
             (H1 : exp_match s1 re1)
             (H2 : exp_match s2 re2) :
             exp_match (s1 ++ s2) (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : exp_match s1 re1) :
                exp_match s1 (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : exp_match s2 re2) :
                exp_match s2 (Union re1 re2)
  | MStar0 re : exp_match [] (Star re)
  | MStarApp s1 s2 re
                 (H1 : exp_match s1 re)
                 (H2 : exp_match s2 (Star re)) :
                 exp_match (s1 ++ s2) (Star re).

Notation "s =~ re" := (exp_match s re) (at level 80).

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.


(* Exercício 1*)
(* Dica pode ser necessário o uso da tática [generalize dependent]. *)

Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
  intros. generalize dependent s1. induction s2.
  - split.
    + simpl. intros. inversion H. reflexivity.
    + intros. simpl. rewrite H. apply MEmpty.
  - split.
    + intros. simpl in H. inversion H. inversion H3. simpl. rewrite (IHs2 s3) in H4.
      rewrite H4. reflexivity.
    + intros. simpl. rewrite H.
    assert ( A : forall S (xx:S) y, [xx]++y = xx::y).
      {  intros S xx y. simpl. reflexivity.  }
    rewrite <- A. apply MApp.
      * apply MChar.
      * apply IHs2. reflexivity.
Qed.

Fixpoint re_not_empty {T : Type} (re : @reg_exp T) : bool :=
  match re with
    | EmptySet => false
    | EmptyStr => true
    | Char _ => true
    | App re1 re2 => andb (re_not_empty re1) (re_not_empty re2)
    | Union re1 re2 => orb (re_not_empty re1) (re_not_empty re2)
    | Star re1 => true
end.

(* Exercício 2*)
Lemma re_not_empty_correct : forall T (re : @reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  intros T re. split.
  - intro H. induction re.
    + inversion H. simpl. inversion H0.
    + reflexivity.
    + reflexivity.
    + simpl. apply andb_true_intro. split.
      * apply IHre1. inversion H. inversion H0. exists s1.
        apply H4.
      * apply IHre2. inversion H. inversion H0. exists s2.
        apply H5.
    + simpl. apply Bool.orb_true_intro. inversion H. inversion H0.
      * left. apply IHre1. exists x. apply H3.
      * right. apply IHre2. exists x. apply H3.
    + reflexivity.
  - intro H. induction re.
    + simpl. inversion H.
    + exists []. apply MEmpty.
    + exists [t]. apply MChar.
    + simpl in H. apply andb_true_iff in H. inversion H.
      apply IHre1 in H0. inversion H0.
      apply IHre2 in H1. inversion H1.
      exists (x ++ x0). apply (MApp x _ x0).
      * apply H2.
      * apply H3.
    + simpl in H. apply orb_true_iff in H. inversion H.
      * apply IHre1 in H0. inversion H0.
        exists x. apply MUnionL. apply H1.
      * apply IHre2 in H0. inversion H0.
        exists x. apply MUnionR. apply H1.
    + exists []. apply MStar0.
Qed.


(* Exercício 3*)
Lemma MStar'' : forall T (s : list T) (re : reg_exp),
  s =~ Star re ->
  exists ss : list (list T),
    s = fold_right (@app T) [] ss
    /\ forall s', In s' ss -> s' =~ re.
Proof.
  intros T s re H. remember (Star re) as re' eqn:eqre.
  induction H as [|x'
                  |s1 re1 s2 re2 Hr1 IH1 Hr2 IH2
                  |s1 re1 re2 Hr IH
                  |re1 s2 re2 Hr IH
                  |re1
                  |s1 s2 re1 Hr1 IH1 Hr2 IH2].
  - inversion eqre.
  - inversion eqre.
  - inversion eqre.
  - inversion eqre.
  - inversion eqre.
  - exists []. split.
    + reflexivity. 
    + intros s' H. inversion H.
  - destruct (IH2 eqre) as [ss' [L R]].
    exists (s1::ss'). split.
    + simpl. rewrite <- L. reflexivity.
    + intros s' H. destruct H.
      * rewrite <- H. inversion eqre. rewrite H1 in Hr1. apply Hr1.
      * apply R. apply H.
Qed.