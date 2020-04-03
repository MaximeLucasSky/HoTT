Require Import Basics Types WildCat.
Require Import Geometry.Site Geometry.Presheaf Geometry.Sheaf.
Require Import Algebra.Rings.
Require Import Spaces.Finite.

Local Open Scope mc_scope.

Definition ZariskiCoverage `{Funext} : Coverage CRing^op.
Proof.
  snrapply Build_Coverage.
  (** We define what it means for a family of morphisms (a sink) to be a Zariski covering. *)
  { (** Given a ring R and a family of morphisms from (since op) this ring *)
    intros R f.
    (** We require the indexing set of the family to be explicitly finite in order to define ring operations with it. *)
    refine (exists (e : exists n, sink_index f <~> Fin n), _).
    (** This family is a Zariski coverage if there exists a family [a] of elements in [R] *)
    refine (exists (a : sink_index f -> R), _).
    (** And two conditions hold *)
    refine (prod _ _).
    (** Firstly each map in the family is a ring localization at the specified element [a] *)
    1: exact (forall i, IsLocalization R (mss_single_element R (a i)) _ (sink_map f i)).
    (** And secondly there exists a family elements [b] in [R] *)
    refine (exists (b : Fin e.1 -> R), _).
    unfold op in R.
    (** Such the sum of their products is 1 *)
    exact (rng_indexed_sum (fun x => a (e.2^-1 x) * b x) = 1). }
  
  intros R f [[n e] [a c]].
  intros V g.
Admitted.

Section AssumeFunext.
Context `{Funext}.

Definition ZariskiSite : Site.
Proof.
  snrapply (Build_Site CRing^op).
  1-4: exact _.
  { intros x y; simpl.
    apply ishset_cringhomomorphism. }
  exact ZariskiCoverage.
Defined.

End AssumeFunext.