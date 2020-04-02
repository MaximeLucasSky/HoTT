Require Import Basics Types WildCat.

Definition Sink {A : Type} `{IsGraph A} (U : A)
  := exists (I : hSet) (V : I -> A), forall i, V i $-> U.

(** Here are some convenient names for sinks *)
Section SinkFields.
  Context {A : Type} `{IsGraph A} {U : A} (f : Sink U).
  Definition sink_index := f.1.
  Definition sink_domain := f.2.1.
  Definition sink_map := f.2.2.
End SinkFields.

(** A coverage is a family deciding which sinks are coverings and equipped with a proof that coverings have a closure property. *)
Record Coverage (C : Type) `{Is1Cat C} := {
  (** We have a type family deciding if a sink is a cover *)
  coverage_iscover {U : C} : Sink U -> Type;
  (** TODO: maybe make that a hprop? *)
  coverage_closed (U : C) (f : Sink U) (f_iscover : coverage_iscover f)
    (V : C) (g : V $-> U)
      : exists (h : Sink V) (h_iscover : coverage_iscover h),
          forall (j : sink_index h),
            exists (i : sink_index f) (k : sink_domain h j $-> sink_domain f i),
              g $o sink_map h j $== sink_map f i $o k;
}.

(** A site consists of a category C and a coverge on C. *)
(** We want a site to be a coherent 1-category as later we will be doing presheaf constructions over this site. These constructions typically require homs to be hsets. *)
Record Site := {
  (** A wild cat with equivalences *)
  site_type : Type;
  site_isgraph : IsGraph site_type;
  site_is01cat : Is01Cat site_type;
  site_is1cat  : Is1Cat  site_type;
  site_hasmoreext : HasMorExt site_type;
  site_istrunc_hom : forall x y, IsHSet (x $-> y);
  site_coverage : Coverage site_type;
}.

Coercion site_type : Site >-> Sortclass.
Global Existing Instances site_isgraph site_is01cat
  site_is1cat site_hasmoreext site_istrunc_hom.

Definition IsCover (C : Site) (U : C) (f : Sink U)
  := coverage_iscover C (site_coverage C) f.
