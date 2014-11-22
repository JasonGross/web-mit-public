(** * Preliminaries *)
(** Instructor's Name: Jason
    Username: espuser
    Password: !Splash2014

    How to install Coq: Open up a terminal, and type

<<
    tellme root
    sudo apt-get install coq coqide emacs proofgeneral-coq
>>

    At home, you can download it from https://coq.inria.fr/.

    You can download this file from:
    http://web.mit.edu/jgross/Public/2014-splash/equality/exercises.v
 *)

(** * Warmup - Getting used to Coq *)
(** Let's see how to prove some things. *)
(** You may find http://andrej.com/coq/cheatsheet.pdf helpful.

    Here's a partial list:
    - [simpl] simplifies things
    - [compute] shows you the normal form
    - [intro x]
    - [destruct x], [case x], [induction x] do case analysis on [x]
    - [reflexivity] proves a goal of the form [x = x]
    - [apply H] makes use of a hypothesis [H]
    - [rewrite H] replaces [x] with [y] when [H] is of type [x = y]
    - [rewrite <- H] replaces [y] with [x] when [H] is of type [x = y]
    - [split] is used to prove [_ /\ _] (conjunction)
    - [left] and [right] are used to prove [_ \/ _] (disjunction) *)
Section WarmUp.
  (** We use a cheating axiom as a placeholder.  Your code should not
      end with any [admit]s.  We use curly braces to not have to give
      [T] explicitly. *)
  Axiom admit : forall {T}, T.

  Lemma id' : forall A, A -> A.
  Proof.
    admit.
  Defined.

  Print id'.

  Definition id : forall A, A -> A
    := admit.

  Lemma compose' : forall A B C, (A -> B) -> (B -> C) -> (A -> C).
  Proof.
    admit.
  Defined.

  Print compose'.

  Definition compose {A B C} (g : B -> C) (f : A -> B) : A -> C
    := admit.

  Goal 1 + 1 = 2.
  Proof.
    admit.
  Defined.

  Lemma and_ex : 1 = 1 /\ 2 = 2.
  Proof.
    admit.
  Defined.

  Lemma or_ex : 1 = 1 \/ 1 = 2.
  Proof.
    admit.
  Defined.

  Lemma or_l : forall A B : Prop, A -> A \/ B.
  Proof.
    admit.
  Defined.

  Lemma or_r : forall A B : Prop, B -> A \/ B.
  Proof.
    admit.
  Defined.

End WarmUp.

(** We begin by defining equality: *)
Inductive eq {A : Type} (x : A) : A -> Type
  := refl : x = x where "x = y" := (@eq _ x y) : type_scope.
Arguments refl {A} x, {A x}.
Notation "x <> y" := (x = y -> False) : type_scope.
(** This says the following:

    - To ask the question, "is [x] equal to [y]?", [x] and [y] must
      both have the same type [A].

    - The only way to construct a proof of equality is by reflexivity,
      which proves, for all [x], that [x = x].

    - The way to make use of an equality [e : x = y] is to replace [y]
      with [x] and [e] with [refl].  This is formalized in [eq_rect]:
      *)

Check eq_rect.
(**
<<
 eq_rect
     : forall (A : Type) (x : A) (P : forall a : A, x = a -> Type),
       P x refl -> forall (y : A) (e : x = y), P y e
>>

     This says that if you are trying to prove [P y e] for any [y : A]
     and [e : x = y], it sufficies to prove [P x refl], i.e., it
     sufficies to replace [y] with [x] and [e] with [refl] and prove
     the resulting statement.

     Using the tactic [destruct e] or [induction e] will perform this
     step in a proof.

     Furthermore, there is a computation rule, which says that when
     [y] is already [x] and [e] is already [refl], the [eq_rect]
     disappears from your proof, and the resulting term of type [P y
     e] *is* the same as the term of type [P x refl].  *)

(** Let's see that this obeys our intuitions. *)
Section WarmUpEq.
  (** You'll want to use [case] or [destruct] here, to do case
      analysis on the "proof of False".  (Hint: There are no proofs of
      [False].  So if you have one, you can do trivial case analysis,
      and there are no cases.) *)
  Lemma absurd : forall A, False -> A.
  Proof.
    admit.
  Defined.

  Lemma all_absurd' : (forall B, B) -> False.
  Proof.
    admit.
  Defined.

  Lemma all_absurd : (forall A B, A -> B) -> False.
  Proof.
    admit.
  Defined.

  Lemma all_1p1_eq_2 x (H : 1 = x) : x + x = 2.
  Proof.
    admit.
  Defined.

  Lemma eq_x_true_any A B (x : bool) (H : x = true)
  : A -> if x then A else B.
  Proof.
    admit.
  Defined.

  Lemma eq_false_x_any A B (x : bool) (H : false = x)
  : (if x then A else B) -> B.
  Proof.
    admit.
  Defined.

  Lemma eq_false_true_any' (H : false = true)
  : forall A B, A -> B.
  Proof.
    admit.
  Defined.

  Lemma neq_false_true : false <> true.
  Proof.
    admit.
  Defined.
End WarmUpEq.

(** Let's prove some simple lemmas. *)
Definition sym {A} {x y : A} (e : x = y) : y = x.
Proof.
  admit.
Defined.
Print sym.

(** We make a notation, so that [sym e] can be written [e^] or [e⁻¹].
    Switch the order of these if you want it to display as [e^]. *)
Notation "e ^" := (sym e) (at level 10, format "e '^'").
Notation "e ⁻¹" := (sym e) (at level 10, format "e '⁻¹'").

Definition trans {A} {x y z : A} (p : x = y) (q : y = z) : x = z.
Proof.
  admit.
Defined.

(** We make another notation for [trans], which can be thought of as
    concatenating or composing equality proofs. *)
Notation "p @ q" := (trans p q) (at level 20, left associativity).
Notation "p • q" := (trans p q) (at level 20, left associativity).

(** When are two proofs of equality themselves equal? *)
(** Since [refl] proves [x = x], we have that any proof of equality is
    equal to itself. *)

Definition eq_refl_refl : forall A (x : A), refl x = refl x
  := admit.

(** Our computation rules also give us that [refl⁻¹ = refl] and [refl
    • refl = refl]. *)
Definition sym_refl {A} (x : A) : (refl x)^ = refl x.
Proof.
  (** unfold [sym] *)
  cbv delta [sym].
  (** plug arguments into functions *)
  cbv beta.
  (** compute pattern matches *)
  cbv iota.
  admit.
Defined.

Definition trans_refl {A} (x : A) : refl x @ refl x = refl x.
Proof.
  admit.
Defined.

Definition ap {A B} (f : A -> B) {x y : A} : x = y -> f x = f y.
Proof.
  admit.
Defined.

(** We can prove the following in two different ways: By doing case
    analysis on [b1] then [b2], or by doing case analysis on [b2] then
    [b1].

    N.B. There are more ways to prove this theorem, which might not
    all be equal. *)
Definition bool_case_1 : forall b1 b2 : bool, b1 = b2 \/ b1 = true \/ b2 = true.
Proof.
  intros b1 b2.
  case b1, b2.
  { admit. }
  { admit. }
  { admit. }
  { admit. }
Defined.

Definition bool_case_2 : forall b1 b2 : bool, b1 = b2 \/ b1 = true \/ b2 = true.
Proof.
  intros b1 b2.
  case b2, b1.
  { admit. }
  { admit. }
  { admit. }
  { admit. }
Defined.

(** We can prove that these two proofs are equal, by case analysis on
    [b1] and [b2]. *)
Definition bool_case_eq : forall b1 b2, bool_case_1 b1 b2 = bool_case_2 b1 b2.
Proof.
  intros b1 b2.
  unfold bool_case_1, bool_case_2.
  case b1, b2.
  { admit. }
  { admit. }
  { admit. }
  { admit. }
Defined.

(** We can, in fact, prove this in another way, too. *)
Definition bool_case_eq' : forall b1 b2, bool_case_1 b1 b2 = bool_case_2 b1 b2.
Proof.
  intros b1 b2.
  unfold bool_case_1, bool_case_2.
  case b2, b1.
  { admit. }
  { admit. }
  { admit. }
  { admit. }
Defined.

(** And we can prove that these two ways are equal... *)
Definition bool_case_eq_eq : forall b1 b2, bool_case_eq b1 b2 = bool_case_eq' b1 b2.
Proof.
  intros b1 b2.
  unfold bool_case_eq, bool_case_eq'.
  case b1, b2.
  { admit. }
  { admit. }
  { admit. }
  { admit. }
Defined.

(** What other properties can we prove? *)
Definition sym_sym {A} (x y : A) (e : x = y) : (e^)^ = e.
Proof.
  admit.
Defined.

Definition trans_1p {A} {x y : A} (e : x = y) : refl @ e = e.
Proof.
  admit.
Defined.

Definition trans_p1 {A} {x y : A} (e : x = y) : e @ refl = e.
Proof.
  admit.
Defined.

Definition trans_assoc {A} {x y z w : A} (p : x = y) (q : y = z) (r : z = w)
: (p @ q) @ r = p @ (q @ r).
Proof.
  admit.
Defined.

Definition trans_pV {A} (x y : A) (p : x = y) : p @ p^ = refl.
Proof.
  admit.
Defined.

Definition trans_Vp {A} (x y : A) (p : x = y) : p^ @ p = refl.
Proof.
  admit.
Defined.

Definition trans_sym {A} (x y z : A) (p : x = y) (q : y = z)
: (p @ q)^ = q^ @ p^.
Proof.
  admit.
Defined.

(** There are also rules for how [ap] plays with [trans] and [sym].
    Try to state and prove them. *)
Definition ap_sym {A B} (f : A -> B) {a b : A} (p : a = b)
: admit.
Proof.
  admit.
Defined.

Definition ap_trans {A B} (f : A -> B) {a b c : A} (p : a = b) (q : b = c)
: admit.
Proof.
  admit.
Defined.

(** Now back to the rules not involving [ap]. *)

Definition whisker_l {A} {x y z : A} (r : x = y) {p q : y = z} (w : p = q)
: r @ p = r @ q.
Proof.
  admit.
Defined.

Definition whisker_r {A} {x y z : A} {p q : x = y} (w : p = q) (r : y = z)
: p @ r = q @ r.
Proof.
  admit.
Defined.

Notation "r @L w" := (whisker_l r w) (at level 20).
Notation "r •ˡ w" := (whisker_l r w) (at level 20).
Notation "w @R r" := (whisker_r w r) (at level 20).
Notation "w •ʳ r" := (whisker_r w r) (at level 20).

(** We can relate [trans_1p], [trans_p1], and [trans_assoc] in a
    commutative triangle:
<<
    (p • refl) • q == p • (refl • q)
           \\          //
             \\      //
               \\  //
                p • q
>> *)
Definition triangle_leg_1 {A} {x y z : A} (p : x = y) (q : y = z)
: (p @ refl) @ q = p @ (refl @ q)
  := trans_assoc _ _ _.
Definition triangle_leg_2 {A} {x y z : A} (p : x = y) (q : y = z)
: p @ (refl @ q) = p @ q
  := p @L trans_1p q.
Definition triangle_leg_3 {A} {x y z : A} (p : x = y) (q : y = z)
: (p @ refl) @ q = p @ q
  := trans_p1 p @R q.
Definition triangle {A} {x y z : A} (p : x = y) (q : y = z)
: triangle_leg_1 p q @ triangle_leg_2 p q = triangle_leg_3 p q.
Proof.
  unfold triangle_leg_1, triangle_leg_2, triangle_leg_3.
  admit.
Defined.

(** There is a similar pentagon relating the two different ways of
    proving that [p @ (q @ (r @ s)) = ((p @ q) @ r) @ s] using chains
    of [trans_assoc].

    Write down the five legs of this pentagon, and prove that the two
    paths are equal. *)
(**
<<
  ((p @ q) @ r) @ s ======= (p @ (q @ r)) @ s
          ||                    ||
          ||                    ||
          ||                    ||
   (p @ q) @ (r @ s)         p @ ((q @ r) @ s)
          \\                   //
            \\               //
              \\           //
                \\       //
             p @ (q @ (r @ s))
>> *)
Definition pentagon {A} {a b c d e : A} (p : a = b) (q : b = c) (r : c = d) (s : d = e)
: admit.
Proof.
  admit.
Defined.

(** There are higher dimensional rules, too, that relate the triangle
    and the pentagon.  They are known as Stasheff polyhedra or
    associahedra. *)


(** Let's look at more complicated things. *)

(** We can proof that all proofs of [False] are equal

    Hint 1: There are no such proofs.

    Hint 2: You can use [exfalso] to say "it sufficies to prove
            [False]". *)
Lemma all_eq_False : forall x y : False, x = y.
Proof.
  admit.
Defined.

Lemma all_eq_eq_False : forall (x y : False) (p q : x = y), p = q.
Proof.
  admit.
Defined.

(** We can prove that all proofs of [false = true] are equal. *)

Lemma all_eq_false_true : forall p q : false = true, p = q.
Proof.
  admit.
Defined.

(** We can proof that all proofs of equality of things of type [unit]
    are equal, but we need to prove something more general. *)
Print unit.
(** It sufficies to prove that all [x : unit] are equal to [tt].  To
    do this, we need to construct a canonical proof of [tt = x] for
    all [x]. *)
Lemma unit_canonical_proof : forall x : unit, tt = x.
Proof.
  admit.
Defined.

Lemma eq_unit_tt {x : unit} (p : tt = x) : p = unit_canonical_proof x.
Proof.
  admit.
Defined.

(** Note: to see the result of applying a theorem to an argument, you
    can use [pose proof (thm args) as H]. *)
Lemma UIP_tt : forall p : tt = tt, p = refl.
Proof.
  admit.
Defined.

Lemma UIP_unit {x : unit} : forall p : x = x, p = refl.
Proof.
  admit.
Defined.

(** It is possible to prove that all proofs of [true = true] are
    equal, but we have to prove a more general theorem.  Namely, we
    need to prove a fact for all [b : bool] and [p : true = b] at
    once.  In the case that [b] is [true], we prove that [p = refl].
    In the case that [b] is [false], we prove absurdity ([False]). *)
Definition eq_true_canonical_proof {b : bool} (p : true = b)
: match b as b' return true = b' -> Prop with
    | true => fun p' => p' = refl
    | false => fun _ => False
  end p.
Proof.
  admit.
Defined.

(** UIP stands for "uniqueness of identity proofs". *)
Definition UIP_true_true (p : true = true) : p = refl.
Proof.
  admit.
Defined.

(** More generally, we can prove uniqueness of identity proofs for
    booleans. *)
Definition eq_bool_canonical_proof {b1 b2 : bool} (p : b1 = b2)
: match b1 as b1', b2 as b2' return b1' = b2' -> Prop with
    | true, true => fun p' => p' = refl
    | false, false => fun p' => p' = refl
    | true, false => fun _ => False
    | false, true => fun _ => False
  end p.
Proof.
  admit.
Defined.

Definition UIP_bool {b1 b2 : bool} : forall p q : b1 = b2, p = q.
Proof.
  admit.
Defined.

(** It is possible to prove that UIP goes up levels. *)
Lemma UIP_bump_helper {A} {x y : A}
      (UIP_A : forall (p q : x = y), p = q)
      (UIP_A_comp : forall (p : x = y), UIP_A p p = refl)
: forall (p q : x = y) (T U : p = q), T = U.
Proof.
  admit.
Defined.

Definition UIP_adjust {A} {x y : A} (H : forall (p q : x = y), p = q)
           (p q : x = y)
: p = q.
Proof.
  admit.
Defined.

Lemma UIP_bump {A} {x y : A}
      (UIP_A : forall (p q : x = y), p = q)
: forall (p q : x = y) (T U : p = q), T = U.
Proof.
  admit.
Defined.

(** Can you prove this in general? *)
(** We can try to ask: "Are all proofs of equality equal to
    reflexivity?"  But this question does not typecheck.  There are
    subtle reasons for this, and it ends up being important. *)
Fail Check forall A (x y : A) (p : x = y), p = refl.

(** We can instead try to prove that any proof of [x = x] is
    [refl]. *)
Lemma UIP : forall {A} {x : A} (p : x = x), p = refl.
Proof.
  admit.
Defined.
