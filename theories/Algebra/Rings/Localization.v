Require Import Basics Types.
Require Import Rings.CRing.
Require Import Truncations.
Require Import Colimits.Quotient.

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
Arguments mss_incl {R _}.
Global Existing Instances
  mss_ishset mss_mult mss_unit mss_incl_inj mss_incl_ismonoidpreserving.

Section MultSubsetLaws.
  Context {R : CRing} {S : MultiplicativeSubset R} (x y : S).

  Definition mss_incl_mult : @mss_incl R S (x * y) = mss_incl x * mss_incl y
    := preserves_sg_op x y.

  Definition mss_incl_one : @mss_incl R S 1 = 1
    := monmor_unitmor.
End MultSubsetLaws.

(** Common multiplicative subsets *)

(** The multiplicative subset generated by a single element *)
Definition mss_single_element (R : CRing) (a : R) : MultiplicativeSubset R.
Proof.
  snrapply Build_MultiplicativeSubset.
  (** We define it to be the sigma type of elements merely equal to a power of a *)
  1: exact {x : R & hexists (fun n => x = rng_pow n a)}.
  1: exact _. (** Our definition allows this to be found. *)
  (** Multiplication *)
  { intros [x p] [y q].
    exists (x * y).
    strip_truncations.
    destruct p as [n p], q as [m q].
    apply tr.
    exists (Peano.plus n m).
    rewrite rng_pow_mult.
    f_ap. }
  (** One *)
  { exists 1.
    apply tr.
    by exists 0%nat. }
  (** Inclusion map *)
  1: apply pr1.
  (** Injectivity of inclusion *)
  { intros x y p.
    by apply path_sigma_hprop. }
  (** Inclusion is monoid preserving. *)
  split.
  { intros [x p] [y q].
    reflexivity. }
  reflexivity.
Defined.

Local Open Scope mc_scope.

(** TODO: move to CRing *)
(** An element [r] of a ring [R] is a unit if it has an inverse. *)
Class IsUnit (R : CRing) (r : R) := {
  isunit_inverse : R;
  isunit_left_inverse   : isunit_inverse * r = 1;
  isunit_right_inverse  : r * isunit_inverse = 1;
}.

Arguments isunit_inverse {_ _} _.

(** Classically a localization (at S) is a map R -> R_S which maps elements of S to units in R_S, such that given any other map R -> T which maps S to units, there exists a unique map R_S -> T such that the appropriate triangle commutes.

In HoTT, we can typically phrase universal properties like this as a certain precomposition being an equivalence. However to do that we need to bundle up ring homomorphisms which invert a particular subset S. This seems counterproductive so we keep the definition close the the classical one.

*)

Class IsLocalization (R : CRing) (S : MultiplicativeSubset R) (R_S : CRing)
  (l : CRingHomomorphism R R_S) :=
{
  (** For such an [f] to be a localization it must invert the elements of S *)
  isrnglocal_unit : forall (s : S), IsUnit R_S (l (mss_incl s));
  (** Now for the "universal property", given any other morphism R -> T which inverts elements of S, there exists a unique map R_S -> T such the triangle commutes. *)
  isrnglocal_up
    (T : CRing) (** Given any other ring T *) 
    (f : CRingHomomorphism R T) (** And a map f from R to T *)
    {H : forall (s:S), IsUnit T (f (mss_incl s))} (** Such that it inverts elements of S *)
    : Contr (** uniquely *)
        { g : CRingHomomorphism R_S T (** There exists a ring homo g : R_S -> R *)
        & f == g o l}; (** such that f factors through l *) 
}.

(** TODO: Now we wish to show that localizations exist. *)

Section Localization.

  (** In this section we will define the localization of a ring as the field of fractions. This construction can be quite involved since we have to define the rings structure on it from scratch. *)

  Context (R : CRing) (S : MultiplicativeSubset R).

  (** We need to define a relation on R * S *)
  Definition eq_fraction : Relation (prod R S).
  Proof.
    intros [r d] [s e].
    exact (exists (x : S),
      mss_incl x * (mss_incl e * r - mss_incl d * s) = 0).
  Defined.

  (** Now we will define the addition and multiplication operations on this quotient. In order to do this, we need to prove some quick lemmas that come up when checking that our operations resepect the equivalence relation. *)

  (** The first lemma is about addition resepcting the relation. *)
  Lemma lem1 (a c e : R) (b d f s : S)
    (p : mss_incl s * (mss_incl f * a - mss_incl b * e) = 0)
    : mss_incl s *
      (mss_incl (f * d) * (a * mss_incl d + mss_incl b * c) -
       mss_incl (b * d) * (e * mss_incl d + mss_incl f * c)) = 0.
  Proof.
    rewrite ?rng_dist_l.
    rewrite rng_mult_negate_r.
    rewrite ?rng_dist_l.
    rewrite ?simple_associativity.
    rewrite <- ? mss_incl_mult.
    set (A := mss_incl (s * (f * d)) * a * mss_incl d).
    set (B := mss_incl (s * (f * d) * b) * c).
    set (C := mss_incl (s * (b * d)) * e * mss_incl d).
    set (D := mss_incl (s * (b * d) * f) * c).
    rewrite (commutativity C D).
    rewrite rng_negate_plus.
    rewrite simple_associativity.
    rewrite <- (simple_associativity A).
    assert (r : B - D = 0).
    { unfold B, D; clear A B C D p.
      rewrite ? mss_incl_mult.
      rewrite <- ? simple_associativity.
      rewrite (commutativity (mss_incl d)).
      rewrite <- ? simple_associativity.
      rewrite (commutativity _ (mss_incl d)).
      rewrite (simple_associativity (mss_incl f)).
      rewrite (commutativity (mss_incl f)).
      rewrite <- simple_associativity.
      rewrite (simple_associativity (mss_incl f)).
      rewrite (commutativity (mss_incl f)).
      rewrite <- simple_associativity.
      apply right_inverse. }
    rewrite r.
    rewrite (right_identity A).
    unfold A, C; clear r B D A C.
    rewrite ?mss_incl_mult.
    rewrite (commutativity (mss_incl f)).
    rewrite <- rng_mult_negate_l.
    rewrite <- (rng_dist_r _ _ (mss_incl d)).
    refine (_ @ rng_mult_zero_l (mss_incl d)).
    f_ap.
    rewrite <- (simple_associativity _ _ e).
    rewrite <- (simple_associativity _ _ a).
    rewrite <- rng_mult_negate_r.
    rewrite <- (rng_dist_l (mss_incl s)).
    rewrite (commutativity (mss_incl b)).
    rewrite <- (simple_associativity _ _ e).
    rewrite <- (simple_associativity _ _ a).
    rewrite <- rng_mult_negate_r.
    rewrite <- (rng_dist_l (mss_incl d)).
    rewrite simple_associativity.
    rewrite (commutativity (mss_incl s)).
    rewrite <- simple_associativity.
    refine (ap _ p @ rng_mult_zero_r _).
  Qed.

  (** The second is about multiplication resepecting the relation. *)
  Lemma lem3 (a c e : R) (b d f s : S)
    (p : mss_incl s * (mss_incl f * a - mss_incl b * e) = 0)
    : mss_incl s * (mss_incl (f * d) * (a * c) - mss_incl (b * d) * (e * c)) = 0.
  Proof.
  Admitted.

  (** We can now define our operations *)

  (** Fraction addition *)
  Instance plus_quotient_eq_fraction : Plus (Quotient eq_fraction).
  Proof.
    intros x.
    srapply Quotient_rec; intros [c d]; revert x.
    { srapply Quotient_rec; intros [a b].
      { apply class_of.
        exact (a * mss_incl d + mss_incl b * c , b * d). }
      intros [e f] [s p].
      apply qglue.
      exists s.
      apply lem1.
      assumption. }
    intros x [e f] [s p]; revert x.
    srapply Quotient_ind_hprop.
    intros [a b].
    apply qglue.
    exists s.
    rewrite 2 mss_incl_mult.
    rewrite 2 (commutativity (mss_incl b) (mss_incl _)).
    rewrite <- 2 mss_incl_mult.
    rewrite 2 (commutativity (a * _)).
    rewrite 2 (commutativity (mss_incl b)).
    rewrite 2 (commutativity a).
    apply lem1.
    assumption.
  Defined.

  (** Fraction multiplication *)
  Instance mult_quotient_eq_fraction : Mult (Quotient eq_fraction).
  Proof.
    intros x.
    srapply Quotient_rec; intros [c d]; revert x.
    { srapply Quotient_rec.
      { intros [a b].
        apply class_of.
        exact (a * c, b * d). }
      intros [a b] [e f] [s p].
      apply qglue.
      exists s.
      apply lem3.
      assumption. }
    intros x [a b] [s p]; revert x.
    srapply Quotient_ind_hprop; intros [e f].
    apply qglue.
    exists s.
    rewrite 2 (commutativity e).
    rewrite 2 mss_incl_mult.
    rewrite 2 (commutativity (mss_incl f)).
    rewrite <- 2 mss_incl_mult.
    apply lem3.
    assumption.
  Defined.

  (** Zero *)
  Instance zero_quotient_eq_fraction : Zero (Quotient eq_fraction)
    := class_of _ (0, 1).

  (** One *)
  Instance one_quotient_eq_fraction : One (Quotient eq_fraction)
    := class_of _ (1, 1).

  (** Negation *)
  Instance negate_quotient_eq_fraction : Negate (Quotient eq_fraction).
  Proof.
    snrapply Quotient_rec; [ exact _ | |].
    { intros [a b].
      exact (class_of _ (- a, b)). }
    intros [a b] [c d] [s p].
    apply qglue.
    exists s.
    rewrite ? rng_mult_negate_r.
    rewrite <- rng_negate_plus.
    rewrite ? rng_mult_negate_r.
    rewrite p.
    apply negate_0.
  Defined.

  (** Addition is associative *)
  Instance associative_plus_quotient_eq_fraction
    : Associative plus_quotient_eq_fraction.
  Proof.
    intros x y.
    srapply Quotient_ind_hprop; intros [e f]; revert y.
    srapply Quotient_ind_hprop; intros [c d]; revert x.
    srapply Quotient_ind_hprop; intros [a b].
    apply qglue.
    exists f.
    rewrite ? mss_incl_mult.
    rewrite ? rng_dist_l.
    rewrite ? simple_associativity.
    rewrite rng_mult_negate_r.
    rewrite ? rng_dist_l.
    rewrite ? rng_dist_r.
    rewrite ? simple_associativity.
    rewrite ? rng_dist_l.
    rewrite ? simple_associativity.
    apply right_inverse.
  Qed.

  (** 0 + x = x *)
  Instance left_identity_plus_quotient_eq_fraction
    : LeftIdentity plus zero.
  Proof.
  Admitted.

  (** x + 0 = x *)
  Instance right_identity_plus_quotient_eq_fraction
    : RightIdentity plus zero.
  Proof.
  Admitted.

  (** - x + x = 0 *)
  Instance left_inverse_plus_quotient_eq_fraction
    : LeftInverse plus negate zero.
  Proof.
  Admitted.

  (** x + - x = 0 *)
  Instance right_inverse_plus_quotient_eq_fraction
    : RightInverse plus negate zero.
  Proof.
  Admitted.

  (** Commutativity of addition *)
  Instance commutative_plus_quotient_eq_fraction
    : Commutative plus.
  Proof.
  Admitted.

  (** Associativity of multiplication *)
  Instance associative_mult_quotient_eq_fraction
    : Associative mult.
  Proof.
  Admitted.

  (** 1 * x = x *)
  Instance left_identity_mult_quotient_eq_fraction
    : LeftIdentity mult one.
  Proof.
  Admitted.

  (** x * 1 = x *)
  Instance right_identity_mult_quotient_eq_fraction
    : RightIdentity mult one.
  Proof.
  Admitted.

  (** Commutativity of multiplication *)
  Instance commutative_mult_quotient_eq_fraction
    : Commutative mult.
  Proof.
  Admitted.

  (** Left distributivity of multiplication over addition *)
  Instance leftdistribute_quotient_eq_fraction
    : LeftDistribute mult plus.
  Proof.
  Admitted.

  (** The quotient is a commutative ring *)
  Instance isring_quotient_eq_fraction
    : IsRing (Quotient eq_fraction).
  Proof.
    repeat split; exact _.
  Qed.

  (** Hence we define [rng_localization] typically denoted [S^-1 R] in classical mathematics as the quotient of R * S by this equivalence relation. *)
  Definition rng_localization : CRing.
  Proof.
    snrapply Build_CRing.
    (** We define the localization of a ring as a quotient of R * S *)
    1: exact (Quotient eq_fraction).
    all: exact _.
  Defined.

  (** This is the universal map [R $-> rng_localization R S] *)
  Definition rng_localization_map : CRingHomomorphism R rng_localization.
  Proof.
    snrapply Build_CRingHomomorphism.
    1: exact (fun x => class_of _ (x, 1)).
    (** There should be 4 cases but 2 can be solved by reflexivity *)
    repeat split.
    { intros x y.
      apply qglue.
      exists 1.
      rewrite ? mss_incl_mult.
      rewrite ? mss_incl_one.
      rewrite ? rng_mult_one_l, ? rng_mult_one_r.
      apply plus_negate_r. }
    intros x y.
    apply qglue.
    exists 1.
    rewrite ? mss_incl_mult.
    rewrite ? mss_incl_one.
    rewrite ? rng_mult_one_l.
    apply plus_negate_r.
  Defined.

  Section LocRec.

    Context (T : CRing) (f : CRingHomomorphism R T)
      (u : forall s : S, IsUnit T (f (mss_incl s))).

    Lemma rng_localization_rec'_well_defined
      : forall x y : R * S, eq_fraction x y
        -> f (fst x) * isunit_inverse (u (snd x))
         = f (fst y) * isunit_inverse (u (snd y)).
    Proof.
      intros [r1 s1] [r2 s2] [x p].
      apply (ap f) in p.
      rewrite rng_homo_zero in p.
      rewrite rng_homo_mult in p.
      rewrite rng_homo_plus in p.
      apply (ap (mult (isunit_inverse (u x)))) in p.
      rewrite simple_associativity in p.
      rewrite isunit_left_inverse in p.
      rewrite rng_mult_one_l in p.
      rewrite rng_mult_zero_r in p.
      rewrite rng_homo_negate in p.
      rewrite <- rng_mult_one_r; symmetry.
      rewrite <- (@isunit_right_inverse _ _ (u s1)).
      rewrite simple_associativity.
      f_ap.
      rewrite <- simple_associativity.
      rewrite (rng_mult_comm _ (f _)).
      rewrite <- rng_mult_one_r; symmetry.
      rewrite <- (@isunit_right_inverse _ _ (u s2)).
      rewrite ? simple_associativity.
      f_ap.
      apply equal_by_zero_sum.
      rewrite <- ?rng_homo_mult.
      rewrite ? (rng_mult_comm _ (mss_incl _)).
      apply p.
    Qed.

    (** We wish to show that this is a ring homomorphism. *)
    Definition rng_localization_rec' : rng_localization -> T.
    Proof.
      snrapply Quotient_rec.
      1: exact _.
      { intros [r s].
        exact (f r * isunit_inverse (u s)). }
      apply rng_localization_rec'_well_defined.
    Defined.

    Instance issemigrouppreserving_plus_rng_localization_rec'
      : @IsSemiGroupPreserving _ _ plus plus rng_localization_rec'.
    Proof.
      intros x.
      snrapply Quotient_ind_hprop; [exact _ | intros [r1 s1]; revert x].
      snrapply Quotient_ind_hprop; [exact _ | intros [r2 s2]].
      simpl.
      assert (p : isunit_inverse (u (s2 * s1))
        = isunit_inverse (u s2) * isunit_inverse (u s1)).
      { rewrite <- rng_mult_one_r.
        rewrite <- (@isunit_right_inverse _ _ (u (s2 * s1))).
        refine ((rng_mult_one_l _)^ @ _).
        rewrite simple_associativity.
        f_ap.
        rewrite mss_incl_mult.
        rewrite rng_homo_mult.
        rewrite (rng_mult_comm (f _)).
        rewrite <- simple_associativity.
        rewrite (simple_associativity _ (f _)).
        rewrite isunit_left_inverse.
        rewrite rng_mult_one_l.
        rewrite isunit_left_inverse.
        reflexivity. }
      rewrite p.
      rewrite rng_homo_plus.
      rewrite ?rng_homo_mult.
      rewrite rng_dist_r.
      rewrite (rng_mult_comm (isunit_inverse _)).
      rewrite rng_mult_assoc.
      rewrite <- (rng_mult_assoc (f r2)).
      rewrite isunit_right_inverse.
      rewrite rng_mult_one_r.
      rewrite (rng_mult_comm (isunit_inverse _)).
      rewrite (rng_mult_comm (f _) (f _)).
      rewrite rng_mult_assoc.
      rewrite <- (rng_mult_assoc (f r1)).
      rewrite isunit_right_inverse.
      rewrite rng_mult_one_r.
      reflexivity.
    Qed.

    Instance issemigrouppreserving_mult_rng_localization_rec'
      : @IsSemiGroupPreserving _ _ mult mult rng_localization_rec'.
    Proof.
    Admitted.

    Instance isunitpreserving_zero_rng_localization_rec'
      : @IsUnitPreserving _ _ zero zero rng_localization_rec'.
    Proof.
    Admitted.

    Instance isunitpreserving_one_rng_localization_rec'
      : @IsUnitPreserving _ _ one one rng_localization_rec'.
    Proof.
    Admitted.

    Definition rng_localization_rec : CRingHomomorphism rng_localization T.
    Proof.
      snrapply Build_CRingHomomorphism.
      1: rapply rng_localization_rec'.
      repeat split; exact _.
    Defined.

  End LocRec.

End Localization.

(** Now we will show that this construction of localization is in fact a ring localization. *)

Global Instance islocalization_rng_localization `{Funext}
  {R : CRing} {S : MultiplicativeSubset R}
  : IsLocalization R S _ (rng_localization_map R S).
Proof.
  split.
  { intro s.
    snrapply Build_IsUnit.
    1: exact (class_of _ (1, s)).
    1,2: apply qglue.
    1,2: exists 1.
    1,2: rewrite ? mss_incl_mult, ? mss_incl_one.
    1,2: rewrite ? rng_mult_one_l, ? rng_mult_one_r.
    1,2: apply plus_negate_r. }
  intros T f p.
  snrapply Build_Contr.
  { exists (rng_localization_rec R S T f p).
    intro. simpl.
    refine ((rng_mult_one_r _)^ @ ap _ _).
    refine (_ @ rng_mult_one_r _).
    refine (_ @ ap _ (rng_homo_one f)).
    refine (_^ @ ap _ (ap _ mss_incl_one)).
    apply isunit_left_inverse. }
  intros [g q].
  rapply path_sigma_hprop.
  rapply equiv_path_cringhomomorphism.
  rapply Quotient_ind_hprop.
  intros [r s].
  simpl.
  transitivity (g ((rng_localization_map R S r) * class_of _ (1, s))).
  { rewrite rng_homo_mult.
    simpl.
    rewrite <- q.
    f_ap.
    rewrite <- rng_mult_one_r.
    rewrite <- (@isunit_right_inverse _ _ (p s)).
    refine ((rng_mult_one_l _)^ @ _).
    rewrite rng_mult_assoc.
    f_ap.
    rewrite q.
    rewrite <- rng_homo_mult.
    symmetry.
    refine (_ @ rng_homo_one g).
    f_ap.
    apply qglue.
    exists 1.
    rewrite ?mss_incl_mult, ?mss_incl_one.
    rewrite ?rng_mult_one_l, ?rng_mult_one_r.
    apply plus_negate_r. }
  apply ap.
  apply qglue.
  exists 1.
  rewrite ?mss_incl_mult, ?mss_incl_one.
  rewrite ?rng_mult_one_l, ?rng_mult_one_r.
  apply plus_negate_r.
Qed.



