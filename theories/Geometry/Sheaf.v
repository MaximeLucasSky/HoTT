Require Import Basics Types WildCat.
Require Import Geometry.Site.
Require Import Geometry.Presheaf.
Require Import Limits.Pullback.

(** In this file we define shaves on a site *)

(** Firstly, we have to define the sieve of a cover *)
Section Sieve.

  Context
    {C : Site}    (** Let C be a site *)
    {U : C}       (** Let U be an object of C *)
    (f : Sink U)  (** And let f be a covering of U *)
    `{IsCover C U f}.

  (** The sieve associated to a cover *)
  Definition presheaf_sieve : PSh C.
  Proof.
    (** We define the sieve as a coequalizer of the following presheaves *)
    snrapply PreSheafCoeq.
    { snrapply PreSheafCoproduct.
      1: exact (BuildhSet (sink_index f * sink_index f)).
      intros [i j].
      nrapply PreSheafPullback.
      1: exact (fmap hset_yon (sink_map f i)).
      exact (fmap hset_yon (sink_map f j)). }
    { snrapply PreSheafCoproduct.
      1: exact (sink_index f).
      intros i.
      exact (hset_yon (sink_domain f i)). }
    (** Here we define the two maps between them *)
    { snrapply functor_presheafcoproduct.
      1: exact fst.
      intros [i j].
      snrapply Build_NatTrans.
      { intro X.
        exact pr1. }
      snrapply Build_Is1Natural.
      intros X Y g.
      reflexivity. }
    snrapply functor_presheafcoproduct.
    1: exact snd.
    intros [i j].
    snrapply Build_NatTrans.
    { intro x.
      exact pullback_pr2. }
    snrapply Build_Is1Natural.
    intros X Y g.
    reflexivity.
  Defined.

  (** TODO: this can be slow, but not slow if done all at once. *)
  (** Now there is a "canonical" map from the sieve to the presheaf represented by U *)
  Definition sieve_map : presheaf_sieve $-> hset_yon U.
  Proof.
    snrapply PreSheafCoeq_rec.
    { snrapply PreSheafCoproduct_rec.
      intro i.
      exact (fmap hset_yon (sink_map f i)). }
    intros X [[i j] [x [y p]]].
    exact p.
  Defined.

End Sieve.

(** Now sheaves are preciesly those presheaves that are local with respect to the sieve map for all covers. *)

Section Sheaf.
  Context {C : Site}.

  Definition presheaf_precomp {a b} := @cat_precomp (PSh C) _ _ a b.

  (** A presheaf on a site C is a sheaf if precomposition with the sieve map is an equivalence. *)
  Class IsSheaf (X : PSh C)
    := isequiv0gpd_issheaf (U : C) (f : Sink U) `{IsCover C U f}
      : IsEquiv0Gpd (presheaf_precomp X (sieve_map f)).
  Global Existing Instance isequiv0gpd_issheaf.
End Sheaf.

(** We define sheaves on a site C to be presheaves which satisfy the sheaf condition. *)
Record Sh (C : Site) := {
  sheaf_presheaf : PSh C;
  sheaf_issheaf : IsSheaf sheaf_presheaf;
}.

Coercion sheaf_presheaf : Sh >-> PSh.
Global Existing Instance sheaf_issheaf.

(** Sheaves form a wild category induced by the wild category structure on presheaves *)
Global Instance isgraph_sh {C} : IsGraph (Sh C) := induced_graph (sheaf_presheaf C).
Global Instance is01cat_sh {C} : Is01Cat (Sh C) := induced_01cat (sheaf_presheaf C).
Global Instance is1cat_sh  {C} : Is1Cat  (Sh C) := induced_1cat  (sheaf_presheaf C).
Global Instance hasequivs_sh {C} : HasEquivs (Sh C) := induced_hasequivs (sheaf_presheaf C).


