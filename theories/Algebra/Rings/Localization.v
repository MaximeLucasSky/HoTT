Require Import Basics Types.
Require Import Rings.CRing.

(** In this file we develop the localization of rings at a multiplicative subset. *)

(** A multiplicative subset of a ring [R] is: *)
Record MultiplicativeSubset (R : CRing) := {
  (** A type *)
  mss_type : Type;
  (** Which is a set *)
  mss_ishset : IsHSet mss_type;
  (** With a multiplication *)
  mss_mult : Mult mss_type;
  (** And unit *)
  mss_unit : One mss_type;
  (** And an inclusion map *)
  mss_incl : mss_type -> R;
  (** Which is injective *)
  mss_incl_inj : IsInjective mss_incl;
  (** And preserves the multiplication and unit *)
  mss_incl_ismonoidpreserving
    : @IsMonoidPreserving mss_type R mult mult one one mss_incl;
}.

Coercion mss_type : MultiplicativeSubset >-> Sortclass.
Global Existing Instances
  mss_ishset mss_mult mss_unit mss_incl_inj mss_incl_ismonoidpreserving.


Local Open Scope mc_scope.

(** TODO: move to CRing *)
(** An element [r] of a ring [R] is a unit if it has an inverse. *)
Class IsUnit (R : CRing) (r : R) := {
  isunit_inverse : R;
  isunit_left_inverse   : isunit_inverse * r = 1;
  isunit_right_inverse  : r * isunit_inverse = 1;
}.

(** Classically a localization (at S) is a map R -> R_S which maps elements of S to units in R_S, such that given any other map R -> T which maps S to units, there exists a unique map R_S -> T such that the appropriate triangle commutes.

In HoTT, we can typically phrase universal properties like this as a certain precomposition being an equivalence. However to do that we need to bundle up ring homomorphisms which invert a particular subset S. This seems counterproductive so we keep the definition close the the classical one.

*)

Class IsLocalization (R : CRing) (S : MultiplicativeSubset R) (R_S : CRing)
  (l : CRingHomomorphism R R_S) :=
{
  (** For such an [f] to be a localization it must invert the elements of S *)
  isrnglocal_unit : forall s, IsUnit R_S (l (mss_incl R S s));
  (** Now for the "universal property", given any other morphism R -> T which inverts elements of S, there exists a unique map R_S -> T such the triangle commutes. *)
  isrnglocal_up
    (T : CRing) (** Given any other ring T *) 
    (f : CRingHomomorphism R T) (** And a map f from R to T *)
    {H : forall s, IsUnit T (f (mss_incl R S s))} (** Such that it inverts elements of S *)
    : Contr (** uniquely *)
        { g : CRingHomomorphism R_S T (** There exists a ring homo g : R_S -> R *)
        & f == g o l}; (** such that f factors through l *) 
}.

(** TODO: Now we wish to show that localizations exist. *)
	





