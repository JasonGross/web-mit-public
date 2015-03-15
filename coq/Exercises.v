Require Import Setoid.

(** username: espuser
    password: #Spark2015 *)

(** Run Coq by opening terminal and typing

     add esp
     coqide &

    If that doesn't work, you can install Coq by typing

     sudo apt-get install coq proofgeneral-coq coqide
     coqide &

    Find this file at http://web.mit.edu/jgross/Public/coq/Exercises.v
    (capitalization matters) or type

     mkdir ~/Documents/<your first name>
     cd ~/Documents/<your first name>
     wget http://web.mit.edu/jgross/Public/coq/Exercises.v
*)

(** Useful tactics to try (roughly in order of usefulness):

   - intro <name>
   - revert <existing hypothesis name> (the inverse of intro <name>)
   - induction <hypothesis name> (perform induction on the named hypothesis)
   - split (use it to split a conjunction (a /\ b))
   - left (to choose to prove a in a \/ b)
   - right (to choose to prove b in a \/ b)
   - exact <hypothesis name> (if you have the goal as a hypothesis)
   - assumption (if any hypothesis solves the goal exactly, use it)
   - destruct <hypothesis name> (to split apart a conjunction (a /\ b), disjunction (a \/ b), or proof of False or Empty_set)
   - constructor (to solve a goal like True or unit or to split apart a conjunction (a /\ b))
   - apply <hypothesis name> (to make use of a hypothesis of the form (a -> b))
   - eapply <hypothesis name> (to make use of a hypothesis of the form (forall x, ...), if you don't know what to choose for x)
   - compute in <hypothesis name>, compute in *, compute (to fully reduce a hypothesis, everything, or the goal)
   - simpl in <hypothesis name>, simpl in *, simpl (to simplify a hypothesis, everything, or the goal; use if compute does too much)
   - reflexivity (to prove a goal of the form x = x)
   - symmetry (to turn x = y into y = x)
   - transitivity y (to turn x = z into two goals, x = y and y = z)
   - rewrite -> <hypothesis name> (make use of an equality x = y, replacing x with y in the goal)
   - rewrite <- <hypothesis name> (make use of an equality x = y, replacing y with x in the goal)
   - inversion <hypothesis name> (turn a hypothesis like S x = S y into x = y)
   - clear <hypothesis name> (get rid of a hypothesis)
  *)

(** Logic *)

Definition id
: forall A, A -> A.
Proof.
  admit.
Defined.

Print id.

Definition function_from_empty_set
: forall T, Empty_set -> T.
Proof.
  admit.
Defined.

Definition function_from_False
: forall P, False -> P.
Proof.
  admit.
Defined.

Definition function_to_unit
: forall T, T -> unit.
Proof.
  admit.
Defined.

Definition function_to_true
: forall P, P -> True.
Proof.
  admit.
Defined.

Definition a_implies_b_implies_a
: forall A B, A -> (B -> A).
Proof.
  admit.
Defined.

Print a_implies_b_implies_a.

Definition b_implies_a_implies_a
: forall A B, B -> A -> A.
Proof.
  admit.
Defined.

Lemma triple_negation_elimination (P : Prop)
: not (not (not P)) <-> not P.
Proof.
  admit.
Qed.

Lemma not_disjunct
: forall P Q,
    not (P \/ Q) <-> (not P) /\ (not Q).
Proof.
  admit.
Qed.

Lemma not_disjunct_iso_1
: forall P Q,
    (sum P Q -> Empty_set)
    -> prod (P -> Empty_set) (Q -> Empty_set).
Proof.
  admit.
Defined.

Lemma not_disjunct_iso_2
: forall P Q,
    prod (P -> Empty_set) (Q -> Empty_set)
    -> (sum P Q -> Empty_set).
Proof.
  admit.
Defined.

Lemma pierces_law_implies_lem
: (forall P Q, ((P -> Q) -> P) -> P)
  -> (forall P, P \/ not P).
Proof.
  admit.
Qed.

Lemma lem_implies_pierces_law
: (forall P, P \/ not P)
  -> (forall P Q : Prop, ((P -> Q) -> P) -> P).
Proof.
  admit.
Qed.

(** See http://en.wikipedia.org/wiki/Intuitionistic_logic#Non-interdefinability_of_operators for more things to prove *)

(** Arithmetic *)

Lemma n_plus_zero
: forall n, n + 0 = n.
Proof.
  admit.
Qed.

Lemma zero_plus_n
: forall n, 0 + n = n.
Proof.
  admit.
Qed.

Lemma plus_commut
: forall n m, n + m = m + n.
Proof.
  admit.
Qed.

Lemma plus_assoc
: forall a b c, (a + b) + c = a + (b + c).
Proof.
  admit.
Qed.

Lemma n_mult_zero
: forall n, n * 0 = 0.
Proof.
  admit.
Qed.

Lemma zero_mult_n
: forall n, 0 * n = 0.
Proof.
  admit.
Qed.

Lemma n_mult_one
: forall n, n * 1 = n.
Proof.
  admit.
Qed.

Lemma one_mult_n
: forall n, 1 * n = n.
Proof.
  admit.
Qed.

Lemma mult_commut
: forall n m, n * m = m * n.
Proof.
  admit.
Qed.

Lemma mult_distribute_plus_left
: forall a b c, a * (b + c) = a * b + a * c.
Proof.
  admit.
Qed.

Lemma mult_distribute_plus_right
: forall a b c, (b + c) * a = b * a + c * a.
Proof.
  admit.
Qed.

Lemma mult_assoc
: forall a b c, (a * b) * c = a * (b * c).
Proof.
  admit.
Qed.

(** you can write down and prove some
    properties of exponents here *)
Fixpoint factorial (n : nat) : nat :=
  match n with
    (* 0! = 1 *)
    | 0 => 1
    (* (n' + 1)! = (n' + 1) * n'! *)
    | S n' => (S n') * factorial n'
  end.

Eval compute in factorial 0.
Eval compute in factorial 1.
Eval compute in factorial 5.

Lemma factorial_correct : factorial 0 = 1
                          /\ forall n : nat,
                               n > 0
                               -> factorial n = n * factorial (n - 1).
Proof.
  admit.
Qed.

Print plus.
Print nat.

Fixpoint expt (b e : nat) : nat :=
  match e with
    | 0 => 1 (* we say that 0 ^ 0 = 1 *)
    | S e' => b * expt b e' (* b ^ (e' + 1) = b * b ^ e' *)
  end.

Eval compute in expt 0 1.
Eval compute in expt 1 0.
Eval compute in expt 3 3.
Eval compute in expt 0 0.


Fixpoint sum_to_n (n : nat) : nat :=
  match n with
    | 0 => 0
    | S n' => S n' + sum_to_n n'
  end.

Lemma sum_to_n_prop : forall n, 2 * sum_to_n n = n * (n + 1).
Proof.
  admit.
Qed.

Fixpoint sum_to_two_to_the_n (n : nat) : nat :=
  match n with
    | 0 => 1
    | S n' => expt 2 (S n') + sum_to_two_to_the_n n'
  end.

Lemma sum_to_two_to_the_n_property
: forall n,
    sum_to_two_to_the_n n = expt 2 (1 + n) - 1.
Proof.
  admit.
Qed.

Definition PowerSet S := S -> bool.

Definition function_is_surjective A B
           (f : A -> B)
  := forall b : B,
     exists a : A,
       f a = b.

(** No function from a set to its power set is surjective *)
Lemma CantorsDiagonalArgument S
: forall f : S -> PowerSet S,
    not (function_is_surjective _ _ f).
Proof.
  admit.
Qed.
