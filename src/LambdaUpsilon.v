(* Author : Maciej Bendkowski <maciej.bendkowski@tcs.uj.edu.pl> *)
Section LambdaUpsilon.

Require Import Arith.
Require Import Omega.

(* binary trees *)
Inductive btree : Set :=
| Leaf
| Left  : btree -> btree
| Right : btree -> btree
| BNode : btree -> btree -> btree.

Hint Constructors btree.

(* natural size of btrees *)
Fixpoint btree_size (bt : btree) : nat :=
  match bt with
    | Leaf         => 1
    | Left t       => S (btree_size t)
    | Right t      => S (btree_size t)
    | BNode lt rt  => S (btree_size lt + btree_size rt)
  end.

(* de Bruijn indices *)
Inductive index : Set :=
| Z
| Succ : index -> index.

Hint Constructors index.

(* appropriate index <-> nat conversions *)
Fixpoint index_to_nat (idx : index) : nat :=
  match idx with
    | Z      => 0
    | Succ n => 1 + index_to_nat n
  end.

Fixpoint nat_to_index (n : nat) : index :=
  match n with
    | 0 => Z
    | S n' => Succ (nat_to_index n')
  end.

Lemma nat_index_inv : forall (n : nat),
  index_to_nat (nat_to_index n) = n.
Proof.
induction n.
- trivial.
- simpl; auto.
Qed.

(* natural size of indices *)
Fixpoint index_size (idx : index) : nat :=
  match idx with
    | Z      => 1
    | Succ n => S (index_size n)
  end.

(* The size of index n is n + 1 *)
Lemma index_size_conv : forall (n : nat),
  index_size (nat_to_index n) = S n.
Proof.
induction n.
- trivial.
- simpl; auto.
Qed.

(* lambda upsilon terms *)
Inductive term : Set :=
| Abs     : term -> term
| Index   : index -> term
| App     : term -> term -> term
| Closure : term -> subs -> term

with

(* explicit substitutions *)
subs : Set :=
| Lift   : subs -> subs
| Slash  : term -> subs
| Shift.

Hint Constructors term.
Hint Constructors subs.

(* natural size of terms *)
Fixpoint term_size (t : term) : nat :=
  match t with
    | Index idx   => index_size idx
    | Abs t'      => S (term_size t')
    | App lt rt   => S (term_size lt + term_size rt)
    | Closure t s => S (term_size t + subs_size s)
  end

with

(* natural size of substitutions *)
subs_size (s : subs) : nat :=
  match s with
    | Lift s' => S (subs_size s')
    | Slash t => S (term_size t)
    | Shift   => 1
  end.

(* auxiliary lifts helper *)
Fixpoint lifts (n : nat) (s : subs) : subs :=
  match n with
    | 0    => s
    | S n' => Lift (lifts n' s)
  end.

(* auxiliary lifts lemmas *)
Lemma lifts_size : forall (n : nat) (s : subs),
  subs_size (lifts n s) = n + subs_size s.
Proof.
induction n, s.
(* base cases *)
- simpl; trivial.
- simpl; trivial.
- simpl; trivial.
(* successor cases *)
- simpl; rewrite IHn; auto.
- simpl; rewrite IHn; auto.
- simpl; rewrite IHn; auto.
Qed.

Lemma lifts_ind : forall (n : nat) (s : subs),
  lifts (S n) s = lifts n (Lift s).
Proof.
induction n.
- intros. simpl. trivial.
- intros. simpl lifts. f_equal.
  rewrite <- IHn. simpl. trivial.
Qed.

Hint Resolve lifts_ind.

Lemma lifts_diff : forall (n : nat) (s : subs) (t : term),
  Lift (lifts n s) <> lifts n (Slash t).
Proof.
induction n.
- intros. simpl. discriminate.
- intros. simpl. injection; intros.
  specialize (IHn s t). injection H; intro.
  contradiction.
Qed.

(* lifts is injective *)
Lemma lifts_inj : forall (n : nat) (s s' : subs),
  lifts n s = lifts n s' -> s = s'.
Proof.
induction n.
- intros. simpl lifts in H. auto.
- intros. simpl lifts in H. injection H; intros.
  specialize (IHn s s'). auto.
Qed.

(* translation from btrees to terms *)
Fixpoint btree_to_term (bt : btree) : term :=
  match bt with
    | Leaf         => Index Z
    | Left t       => btree_to_term' 1 t
    | Right t      => Abs (btree_to_term t)
    | BNode lt rt  => App (btree_to_term lt) (btree_to_term rt)
  end

with

btree_to_term' (n : nat) (bt : btree) : term :=
  match bt with
    | Leaf         => Index (nat_to_index n)
    | Left t       => btree_to_term' (S n) t
    | Right t      => Closure (btree_to_term t) (lifts (n-1) Shift)
    | BNode lt rt  => Closure (btree_to_term rt) (lifts (n-1) (Slash (btree_to_term lt)))
  end.

(* translation preserves the structure size *)
Theorem size_prop : forall (bt : btree) (n : nat),
  term_size (btree_to_term bt) = btree_size bt /\
  term_size (btree_to_term' (S n) bt) = (S n) + btree_size bt.
Proof.
induction bt, n.
(* Leaf cases *)
- auto.
- split. auto.
  simpl. rewrite index_size_conv. omega.
(* Left cases *)
- simpl. split.
  apply IHbt. apply IHbt.
- simpl. split.
  apply IHbt.
  specialize (IHbt (S (S n))). omega.
(* Right cases *)
- simpl. specialize (IHbt 0).
  split. omega. omega.
- simpl. split. specialize (IHbt 0). omega.
  rewrite lifts_size. simpl. specialize (IHbt (n+1)). omega.
(* BNode cases *)
- simpl. split.
  specialize (IHbt1 0). specialize (IHbt2 0). omega.
  specialize (IHbt1 0). specialize (IHbt2 0). omega.
- simpl. split.
  specialize (IHbt1 0). specialize (IHbt2 0). omega.
  specialize (IHbt1 0). specialize (IHbt2 0).
  rewrite lifts_size. simpl. omega.
Qed.

(* structural invariant of btree_to_term' *)
Lemma btree_to_term'_inv : forall (bt : btree),
  (forall (n : nat),
    btree_to_term' (S n) bt = Index (nat_to_index (n + btree_size bt))) \/
  (forall (n : nat),
    exists t s, btree_to_term' (S n) bt = Closure t (lifts n s)).
Proof.
induction bt.
- left. intro. simpl.
  induction n.
    * auto.
    * simpl. injection IHn.
      intro. rewrite H. auto.
- destruct IHbt.
  * left. intro. simpl. rewrite H.
    f_equal. auto with zarith.
  * right. intro. simpl btree_to_term'.
    specialize (H (S n)).
    do 2 destruct H.
    exists x. exists (Lift x0).
    rewrite H. f_equal. eauto.
- repeat (destruct IHbt;
    right; intro; simpl;
    exists (btree_to_term bt);
    exists Shift;
    replace (n - 0) with n;
    trivial; omega).
- repeat (destruct IHbt1; destruct IHbt2;
    right; intro; simpl;
    exists (btree_to_term bt2);
    exists (Slash (btree_to_term bt1));
    replace (n - 0) with n;
    trivial; omega).
Qed.

(* auxiliary size lemmas *)
Lemma contrapositive: forall (P Q : Prop),
  (P -> Q) -> (~ Q -> ~ P).
Proof.
tauto.
Qed.

(* auxiliary proof arguments *)
Lemma diff_term_size : forall (t t' : term),
  term_size t <> term_size t' -> t <> t'.
Proof.
intros t t'.
apply contrapositive.
intro. rewrite H. trivial.
Qed.

Hint Resolve diff_term_size.

Lemma diff_subs_size : forall (s s' : subs),
  subs_size s <> subs_size s' -> s <> s'.
Proof.
intros s s'.
apply contrapositive.
intro. rewrite H. trivial.
Qed.

Hint Resolve diff_subs_size.

(* positive size lemmas *)
Lemma positive_btree_size : forall (bt : btree),
  btree_size bt > 0.
Proof.
repeat (induction bt;
        simpl; omega).
Qed.

Hint Resolve positive_btree_size.

Lemma positive_index_size : forall (i : index),
  index_size i > 0.
Proof.
intros.
repeat (destruct i;
        simpl; omega).
Qed.

Hint Resolve positive_index_size.

Lemma positive_term_size : forall (t : term),
  term_size t > 0.
Proof.
repeat (induction t;
        simpl; auto with arith).
Qed.

Hint Resolve positive_term_size.

(* additional structural invariants of btree_to_term' *)
Lemma btree_to_term'_abs : forall (bt bt' : btree) (n : nat),
  btree_to_term' (S n) bt <> Abs (btree_to_term bt').
Proof.
intros.
destruct (btree_to_term'_inv bt).
intuition. rewrite H in H0. discriminate H0.
intuition. specialize (H n). do 2 destruct H.
rewrite H in H0. discriminate H0.
Qed.

Lemma btree_to_term'_app : forall (bt bt' bt'' : btree) (n : nat),
  btree_to_term' (S n) bt <> App (btree_to_term bt') (btree_to_term bt'').
Proof.
intros.
destruct (btree_to_term'_inv bt).
intuition. rewrite H in H0. discriminate H0.
intuition. specialize (H n). do 2 destruct H.
rewrite H in H0. discriminate H0.
Qed.

Lemma btree_to_term'_left_right : forall (n : nat) (bt bt' : btree),
  btree_to_term' (S n) (Left bt) <> btree_to_term' (S n) (Right bt').
Proof.
intros. simpl.
destruct (btree_to_term'_inv bt).
rewrite (H (S n)). discriminate.
specialize (H (S n)). do 2 destruct H.
rewrite H. injection; intros.
destruct x0.
- apply (f_equal subs_size) in H1.
  simpl subs_size in H1.
  do 2 (rewrite lifts_size in H1).
  simpl subs_size in H1.
  omega.
- apply (f_equal subs_size) in H1.
  simpl subs_size in H1.
  do 2 (rewrite lifts_size in H1).
  simpl subs_size in H1.
  omega.
- injection H0; intros.
  apply (f_equal subs_size) in H3.
  simpl subs_size in H3.
  do 2 (rewrite lifts_size in H3).
  simpl subs_size in H3.
  omega.
Qed.

Lemma btree_to_term'_left_bnode : forall (n : nat) (bt bt'1 bt'2 : btree),
  btree_to_term' (S n) (Left bt) <> btree_to_term' (S n) (BNode bt'1 bt'2).
Proof.
intros. simpl.
destruct (btree_to_term'_inv bt).
rewrite (H (S n)). discriminate.
specialize (H (S n)). do 2 destruct H.
rewrite H. injection; intros.
contradict H1. replace (n-0) with n.
apply lifts_diff. omega.
Qed.

Lemma btree_to_term'_right_bnode : forall (n : nat) (bt bt'1 bt'2 : btree),
  btree_to_term' (S n) (Right bt) <> btree_to_term' (S n) (BNode bt'1 bt'2).
Proof.
intros. simpl.
injection; intros.
contradict H0. replace (n-0) with n.
apply diff_subs_size.
rewrite lifts_size. simpl.
rewrite lifts_size. simpl.
pose proof (positive_term_size (btree_to_term bt'1)).
omega. omega.
Qed.

(* main proof: translation is injective *)
Theorem injection_prop : forall (bt bt' : btree),
  (btree_to_term bt = btree_to_term bt' -> bt = bt') /\
  (forall (n : nat),
    btree_to_term' (S n) bt = btree_to_term' (S n) bt' -> bt = bt').
Proof.
induction bt.
(* Leaf cases *)
- intros. destruct bt'.
  * split. trivial.
    intro. trivial.
  * split.
      intro. contradict H. apply diff_term_size.
      simpl. pose proof (size_prop bt' 0) as H. destruct H.
      rewrite H0. pose proof (positive_btree_size bt'). omega.

      intros. contradict H. apply diff_term_size.
      simpl. rewrite index_size_conv.
      pose proof (size_prop bt' (S n)) as H. destruct H.
      rewrite H0. pose proof (positive_btree_size bt'). omega.
  * split.
      intro. contradict H. apply diff_term_size.
      simpl. pose proof (size_prop bt' 0) as H. destruct H.
      rewrite H. pose proof (positive_btree_size bt'). omega.

      intros. contradict H. apply diff_term_size.
      simpl. rewrite index_size_conv. rewrite lifts_size. simpl.
      pose proof (size_prop bt' 0) as H. destruct H.
      rewrite H. pose proof (positive_btree_size bt'). omega.
  * split.
      intro. contradict H. apply diff_term_size. simpl.
      pose proof (size_prop bt'1 0) as H1. destruct H1. rewrite H.
      pose proof (size_prop bt'2 0) as H2. destruct H2. rewrite H1.
      pose proof (positive_btree_size bt'1).
      pose proof (positive_btree_size bt'2).
      omega.

      intros. contradict H. apply diff_term_size.
      simpl. rewrite index_size_conv. rewrite lifts_size. simpl.
      pose proof (size_prop bt'1 0) as H1. destruct H1. rewrite H.
      pose proof (size_prop bt'2 0) as H2. destruct H2. rewrite H1.
      pose proof (positive_btree_size bt'1).
      pose proof (positive_btree_size bt'2).
      omega.
(* Left cases *)
- intros. destruct bt'.
  * split.
    intro. contradict H. apply diff_term_size. simpl.
    pose proof (size_prop bt 0) as H. destruct H.
    rewrite H0. pose proof (positive_btree_size bt). omega.

    intros. simpl btree_to_term' in H at 1.
    apply (f_equal term_size) in H.
    pose proof (size_prop bt (S n)) as P. destruct P.
    rewrite H in H1.
    simpl btree_to_term' in H1.
    simpl term_size in H1.
    rewrite index_size_conv in H1.
    contradict H1. pose proof (positive_btree_size bt).
    omega.
  * split.  (* both are Left *)
    intros. simpl btree_to_term in H.
    specialize (IHbt bt'). destruct IHbt.
    specialize (H1 0). cut (bt = bt').
    intros. apply (f_equal Left) in H2. auto. auto.

    intros. simpl btree_to_term' in H.
    specialize (IHbt bt'). destruct IHbt.
    specialize (H1 (S n)). cut (bt = bt').
    intros. apply (f_equal Left) in H2. auto. auto.
  * split.
    intros. simpl btree_to_term in H.
    contradict H. apply btree_to_term'_abs.

    intros.
    pose proof (btree_to_term'_left_right n bt bt').
    contradiction.
  * split.
    intros. simpl btree_to_term in H.
    contradict H. apply btree_to_term'_app.

    intros.
    pose proof (btree_to_term'_left_bnode n bt bt'1 bt'2).
    contradiction.
(* Right cases *)
- intros. destruct bt'.
  * split.
    intro. contradict H. apply diff_term_size. simpl.
    pose proof (size_prop bt 0) as H. destruct H.
    rewrite H. pose proof (positive_btree_size bt). omega.

    intros. simpl btree_to_term' in H.
    discriminate H.
  * split.
    intros. symmetry in H. simpl btree_to_term in H.
    contradict H. apply btree_to_term'_abs.

    intros.
    pose proof (btree_to_term'_left_right n bt' bt).
    symmetry in H. contradiction.
  * split. (* both are Right *)
    intros. simpl btree_to_term in H.
    specialize (IHbt bt'). destruct IHbt. cut (bt = bt').
    intros. apply (f_equal Right) in H2. auto. injection H. auto.

    intros. simpl btree_to_term' in H.
    specialize (IHbt bt'). destruct IHbt.
    specialize (H1 (S n)). cut (bt = bt').
    intros. apply (f_equal Right) in H2. auto.
    injection H. auto.
  * split.
    intros. simpl btree_to_term in H.
    discriminate H.

    intros.
    pose proof (btree_to_term'_right_bnode n bt bt'1 bt'2).
    contradiction.
(* BNode cases *)
- intros. split.
  * intros. simpl btree_to_term in H. destruct bt'.
    + simpl btree_to_term in H. discriminate H.
    + simpl btree_to_term in H.
      pose proof (btree_to_term'_app bt' bt1 bt2 0).
      symmetry in H. contradiction.
    + simpl btree_to_term in H. discriminate H.
    + simpl btree_to_term in H. injection H. intros.
      specialize (IHbt1 bt'1). destruct IHbt1.
      specialize (IHbt2 bt'2). destruct IHbt2.
      assert (bt1 = bt'1). auto.
      assert (bt2 = bt'2). auto.
      f_equal. auto. auto.
  * intros. destruct bt'.
    + simpl btree_to_term' in H. discriminate H.
    + symmetry in H.
      pose proof (btree_to_term'_left_bnode n bt' bt1 bt2).
      contradiction.
    + symmetry in H.
      pose proof (btree_to_term'_right_bnode n bt' bt1 bt2).
      contradiction.
    + simpl btree_to_term' in H. (* both are BNode *)
      injection H; intros.
      specialize (IHbt2 bt'2). destruct IHbt2.
      replace (n-0) with n in H0.
      apply lifts_inj in H0.
      injection H0; intros.
      specialize (IHbt1 bt'1). destruct IHbt1.
      f_equal. auto. auto.
      omega.
Qed.

End LambdaUpsilon.

Extraction Language Haskell.
Extraction "LambdaUpsilonCert.hs" btree_to_term.