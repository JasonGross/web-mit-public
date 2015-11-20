(** username: espuser
    password: 20Splash15 *)

(** Run Coq by opening terminal and typing

     add esp
     coqide &

    If that doesn't work, you can install Coq by typing

     sudo apt-get install coq proofgeneral-coq coqide
     coqide &

    Find this file at http://web.mit.edu/jgross/Public/coq/Exercises2015.v
    (capitalization matters) or type

     mkdir ~/Documents/<your first name>
     cd ~/Documents/<your first name>
     wget http://web.mit.edu/jgross/Public/coq/Exercises2015.v

    On your own computer, you can download Coq from https://coq.inria.fr.

    N.B. There are many theorem provers out there, e.g., Agda, Idris, NuPRL, Otter, Twelf, Isabelle/HOL, Mizar, Metamath
*)

(** Logic *)

(** The following are placeholders; [admit] indicates that something should be filled in later. *)
Axiom admit : forall {T}, T.

(** Remove this to get ASCII (->) rather than unicode (→). *)
Require Import Utf8.

(** ** Tautologies *)

(** We'll fill in these first few together.  Any ideas for how to to prove something like this? *)

Definition id : forall A, A -> A.
Proof.
  refine admit.
Defined.

(** We can also write the colon on a line of its own; I set up this file in this way so that I can use a large font in my presentation. *)

Definition modus_ponens
: forall P Q, (P -> Q) -> P -> Q.
Proof.
  refine admit.
Defined.

(** N.B. [A -> (B -> C)] and [A -> B -> C] are the same; [->] associates to the right. *)

Definition first_argument
: forall A B, A -> (B -> A).
Proof.
  refine admit.
Defined.

Definition compose
: forall A B C,
    (A -> B) -> (B -> C) -> (A -> C).
Proof.
  refine admit.
Defined.

Definition function_from_False
: forall P, False -> P.
Proof.
  refine admit.
Defined.

Definition not_False
: ~False.
Proof.
  refine admit.
Defined.

Definition function_to_True
: forall P, P -> True.
Proof.
  refine admit.
Defined.

Definition disjunction
: forall P, True \/ P.
Proof.
  refine admit.
Defined.

Definition conjunction
: forall P : Prop,
    P -> True /\ P.
Proof.
  refine admit.
Defined.

Definition use_conjunction
: forall P : Prop,
    True /\ P -> P.
Proof.
  refine admit.
Defined.

Definition use_disjunction
: forall P : Prop,
    False \/ P -> P.
Proof.
  refine admit.
Defined.

(** These two are exercises to do individually or with the people sitting next to you. *)

Definition introduce_intermediate
: forall A B C,
    (A -> (B -> C))
    -> ((A -> B) -> (A -> C)).
Proof.
  refine admit.
Defined.

Definition swap_args
: forall A B C,
    (A -> B -> C) -> (B -> A -> C).
Proof.
  refine admit.
Defined.

Definition second_argument
: forall A B, A -> B -> B.
Proof.
  refine admit.
Defined.

Definition id_either
: forall A, A -> A -> A.
Proof.
  refine admit.
Defined.

Definition third_argument
: forall A B C, A -> B -> C -> C.
Proof.
  refine admit.
Defined.

(** This one is a bit different; one of the arguments has a [forall] *)
Definition explode
: forall A B F,
    (forall C, F -> C)
    -> (A -> F)
    -> (A -> B).
Proof.
  refine admit.
Defined.

Lemma triple_negation_elimination
: forall P : Prop,
    not (not (not P)) <-> not P.
Proof.
  unfold not, iff.
  refine admit.
Qed.

Lemma not_disjunct
: forall P Q,
    not (P \/ Q) <-> (not P) /\ (not Q).
Proof.
  unfold not, iff.
  admit.
Qed.

(** Prove that the Law of Excluded Middle implies Double Negation Elimination *)

Definition LEM_implies_DNE
: (forall P, P \/ ~P)
  -> (forall P, ~~P -> P).
Proof.
  unfold not.
  refine admit.
Defined.

(** Prove that Double Negation Elimination implies Peirce's Law *)

Definition DNE_implies_Peirce
: (forall P, ~~P -> P)
  -> (forall P Q : Prop,
        ((P -> Q) -> P) -> P).
Proof.
  unfold not.
  refine admit.
Defined.

(** Prove that Peirce's Law implies the Law of Excluded Middle *)

Definition Peirce_implies_LEM
: (forall P Q : Prop,
     ((P -> Q) -> P) -> P)
  -> (forall P, P \/ ~P).
Proof.
  unfold not.
  refine admit.
Defined.
