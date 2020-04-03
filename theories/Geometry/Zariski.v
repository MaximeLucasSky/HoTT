Require Import Basics Types WildCat.
Require Import Geometry.Site Geometry.Presheaf Geometry.Sheaf.
Require Import Algebra.Rings.
Require Import Spaces.Finite.

Local Open Scope mc_scope.

Section AssumeFunext.
Context `{Funext}.

(** For a cover to be a Zariski cover, we require the following: *)
Record IsZariskiCover {SpecR : CRing^op} (f : Sink SpecR) := {
  (** The indexing set is finite *)
  iszar_finite : Finite (sink_index f);
  (** A family of elements of SpecR which we will later localize at *)
  iszar_a : sink_index f -> SpecR;
  (** Each map of the cover is a localization at a_i *)
  iszar_islocal (i : sink_index f)
    : IsLocalization _ (mss_single_element _ (iszar_a i)) _ (sink_map f i);
  (** Another family of elements of SpecR *)
  iszar_b : sink_index f -> SpecR;
  (** Such that their "inner product" is 1 *)
  (** TODO: better name *)
  iszar_eq : rng_indexed_sum
    (fun i => cring_mult (iszar_a i) (iszar_b i)) = cring_one;
}.

Definition ZariskiCoverage `{Funext} : Coverage CRing^op.
Proof.
  snrapply Build_Coverage.
  1: intros SpecR f; exact (IsZariskiCover f).
  hnf; intros U f iszar_g.
  intros V g.
  snrefine (_;_).
  { snrapply Build_Sink.
    1: exact (sink_index f).
    1: exact _.
    { intro i.
      
      
Admitted.



Definition ZariskiSite : Site.
Proof.
  snrapply (Build_Site CRing^op).
  1-4: exact _.
  { intros x y; simpl.
    apply ishset_cringhomomorphism. }
  exact ZariskiCoverage.
Defined.

End AssumeFunext.