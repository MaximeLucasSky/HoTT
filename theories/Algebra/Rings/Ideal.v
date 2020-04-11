Require Import Basics Types.
Require Import Algebra.Rings.CRing.
Require Import Algebra.AbGroups.
Require Import BiInv.

Local Open Scope mc_scope.

(** In this file we define Ideals *)

(** TODO: In the future it might be useful to define ideals as submodules *)

(** An additive subgroup I of a ring R is an ideal when: *)
Class IsIdeal {R : CRing} (I : Subgroup R) := {
  (** Forall r : R and x : I, there exists an a : I, such that a = r * x inside R *)
  isideal : forall r x, exists a, issubgroup_incl a = r * issubgroup_incl x;
}.

Record Ideal (R : CRing) := {
  ideal_subgroup : Subgroup R;
  ideal_isideal : IsIdeal ideal_subgroup;
}.

Coercion ideal_subgroup : Ideal >-> Subgroup.
Global Existing Instances ideal_isideal.

Definition plus_ideal {R : CRing} {I : Ideal R} : Plus I := sg_op.
Global Existing Instances plus_ideal.

Definition zero_ideal {R : CRing} {I : Ideal R} : Zero I := mon_unit.
Global Existing Instances zero_ideal.

Definition ideal_incl {R : CRing} {I : Ideal R}
  : GroupHomomorphism I R.
Proof.
  exact (Build_GroupHomomorphism issubgroup_incl).
Defined.

Global Instance issubgroup_trivial {G : Group} : IsSubgroup TrivialAbGroup G.
Proof.
  snrapply Build_IsSubgroup.
  { snrapply (Build_GroupHomomorphism (fun _ => group_unit)).
    intros ??; symmetry; apply left_identity. }
  cbn; intros ???.
  apply path_unit.
Defined.

Global Instance isinj_idmap A : @IsInjective A A idmap
  := fun x y => idmap.

Global Instance issubgroup_group {G : Group} : IsSubgroup G G
  := Build_IsSubgroup _ _ grp_homo_id _.

Definition trivial_subgroup {G} : Subgroup G
  := Build_Subgroup G TrivialAbGroup _.

Definition trivial_subgroup' {G} : Subgroup G
  := Build_Subgroup G G _.

Section Examples.

  Context (R : CRing).

  (** The zero ideal is an ideal *)
  Global Instance isideal_trivial_subgroup
    : IsIdeal (R:=R) trivial_subgroup.
  Proof.
    split.
    intros r [].
    exists tt.
    refine (_ @ _^ @ ap _ _^).
    1,3: rapply grp_homo_unit.
    apply rng_mult_zero_r.
  Defined.

  (** Zero ideal *)
  Definition ideal_zero : Ideal R
    := Build_Ideal R _ isideal_trivial_subgroup.

  (** The unit ideal is an ideal *)
  Global Instance isideal_trivial_subgroup'
    : IsIdeal (R:=R) trivial_subgroup'.
  Proof.
    split.
    cbn; intros r r'.
    exists (r * r').
    reflexivity.
  Defined.

  (** Unit ideal *)
  Definition ideal_unit : Ideal R
    := Build_Ideal R _ isideal_trivial_subgroup'.

  (** TODO: Intersection of ideals *)


  (* Lemma eq_hprop {P : hProp} (x y : P) : x = y. *)
  (* Proof. *)
  (*   destruct (istrunc_trunctype_type P x y). *)
  (*   exact center. *)
  (* Defined. *)

  (* Lemma eq_hprop_1 {P : hProp} (x : P) : eq_hprop x x = 1%path. *)
  (* Proof. *)
  (*   apply eq_hprop. *)
  (* Defined. *)
  
End Examples.

(** * Something about subsets and infinite intersections ****)

Section Subsets.
  
  Class IsSubset (E F : Type) `{IsHSet F} :=
    {
      issubset_incl : E -> F;
      issubset_ishset : IsHSet E;
      isinj_issubset_incl : IsInjective issubset_incl;
    }.

  Global Existing Instance isinj_issubset_incl.
  Global Existing Instance issubset_ishset.

  Generalizable Variable E F.
  Context `{IsHSet E} `{IsHSet F}.
  
(* Subset inclusion is an embedding. *)
  Global Instance isembedding_issubset_incl `{!IsSubset E F}
    : IsEmbedding (@issubset_incl E F _ _).
  Proof. 
    apply HSet.isembedding_isinj_hset.
    apply isinj_issubset_incl.
  Defined.
  
  Definition issig_issubset G H GhSet : _ <~> IsSubset G H
    := ltac:(issig).
  
(** A subset of a set E is a set F which is a subset of E. *) 
  Record Subset (E : Type) `{IsHSet E} :=
    {
      subset_set :> Type;
      subset_issubset : IsSubset subset_set E;
    }.
  
  Global Existing Instance subset_issubset.

End Subsets.

Section Subset_HProp.
  Context (E : Type) `{IsHSet E} (ϕ : E -> Type) `{forall x, IsHProp (ϕ x)}.
  
  Global Instance hset_subset_hprop : IsHSet { e : E | ϕ e }.
  Proof. 
    intros x y. eapply trunc_equiv'.
    1: exact (equiv_path_sigma_hprop x y).
    exact (IsHSet0 x.1 y.1).
  Defined.

  Global Instance issubset_subset_hprop : IsSubset { e : E | ϕ e } E.
  Proof.
    snrapply Build_IsSubset.
    - exact (fun x => x.1).
    - exact hset_subset_hprop.
    - intros ???.
      apply equiv_path_sigma_hprop.
      assumption.
  Defined.

  Definition subset_subset_hprop : Subset E.
  Proof.
    snrapply Build_Subset.
    1: exact { e : E | ϕ e }.
    exact _.
  Defined.
End Subset_HProp.

Section Inter_Subset.

  Context (E : Type) `{IsHSet E}.
  Context {J : Type} (f : J -> Type) `{forall (j : J), IsSubset (f j) E}.

  Definition type_setinter : Type :=
    {x : E | forall j : J, exists a : f j, issubset_incl a = x}.
  
  Global Instance issubset_setinter `{Funext} : IsSubset type_setinter E.
  Proof.
    apply issubset_subset_hprop.
    intro x.
    apply trunc_forall.
  Defined.

  Definition subset_setinter `{Funext} : Subset E.
  Proof.
    snrapply Build_Subset.
    1: exact type_setinter.
    exact _.
    Defined.

End Inter_Subset.

Section InterSubgroup.
  
  Local Open Scope mc_mult_scope.


  Global Instance subset_subgroup (G : Group) (H : Subgroup G) : IsSubset H G.
  Proof.
    snrapply Build_IsSubset.
    - exact issubgroup_incl.
    - exact _.
    - exact _.
  Defined.
  
  Context {G : Group} {J : Type} (f : J -> Subgroup G) `{Funext}.
  

  
  Definition type_groupinter : Type :=
    type_setinter G f.

  Global Instance sgop_groupinter : SgOp type_groupinter. 
  Proof.
     intros [x Hx] [y Hy].
     exists (x * y).
     intro j. specialize (Hx j). specialize (Hy j).
     exists (Hx.1 * Hy.1).
     cbn. rewrite (preserves_sg_op (pr1 Hx) (pr1 Hy)).
     cbn in Hx. rewrite (pr2 Hx).
     cbn in Hy. rewrite (pr2 Hy).
     reflexivity.
  Defined.

  Global Instance monunit_groupinter : MonUnit type_groupinter.
  Proof.
    exists mon_unit.
    intro j.
    exists mon_unit.
    exact preserves_mon_unit.
  Defined.

  Global Instance negate_groupinter : Negate type_groupinter.
  Proof.
    intros [x Hx].
    exists (-x).
    intro j. specialize (Hx j).
    exists  (- Hx.1). cbn in *.
    rewrite (grp_homo_inv _ (pr1 Hx)).
    rewrite (pr2 Hx).
    reflexivity.
  Defined.

  Global Instance isgroup_groupinter: IsGroup type_groupinter.
  Proof.
    snrapply Build_IsGroup.
    - snrapply Build_IsMonoid.
      + snrapply Build_IsSemiGroup.
        *  exact _. 
        * intros [x Hx] [y Hy] [z Hz].
          apply equiv_path_sigma_hprop. cbn.
          rewrite sg_ass.
          1: reflexivity.
          exact _.
      + intros [x Hx].
        apply equiv_path_sigma_hprop. cbn.
        rewrite  monoid_left_id.
        1: reflexivity.
        exact _.
      + intros [x Hx].
        apply equiv_path_sigma_hprop. cbn.
        rewrite  monoid_right_id.
        1: reflexivity.
        exact _.
    - intros [x Hx].
      apply equiv_path_sigma_hprop. cbn.
      rewrite (negate_l _). reflexivity.
    - intros [x Hx].
      apply equiv_path_sigma_hprop. cbn.
      rewrite (negate_r _). reflexivity.
  Defined.
  
  Definition groupinter : Group.
  Proof.
    exact (Build_Group type_groupinter _ _ _ _).
  Defined.

  Definition grouphomo_groupinter :
    GroupHomomorphism groupinter G.
  Proof.
    snrapply Build_GroupHomomorphism.
    1: exact (fun x => x.1).
    intros x y.
    reflexivity.
  Defined.

  Global Instance issubgroup_groupinter  :
    IsSubgroup groupinter G.
  Proof.
    snrapply Build_IsSubgroup.
    1: exact grouphomo_groupinter.
    exact (@isinj_issubset_incl _ _ _ (issubset_setinter _ f)).
  Defined.

  Global Instance subgroup_groupinter :
    Subgroup G.
  Proof.
    exact (Build_Subgroup _ groupinter _).
  Defined.

End InterSubgroup.

Section InterIdeal.
  
  Definition ideal_idealinter `{Funext} {R : CRing} {J : Type} (f : J -> Subgroup R) `{forall j : J, IsIdeal (f j)}: Ideal R.
  Proof.
    snrapply Build_Ideal.
    - exact (subgroup_groupinter f).
    - snrapply Build_IsIdeal.
      intros r [x Hx].
      unshelve econstructor.
      + unshelve econstructor.
        1: exact (r * x).
        intro j. specialize (Hx j). specialize (H0 j).
        unshelve econstructor.
        1: exact (isideal r (Hx.1)).1.
        cbn. rewrite (isideal r Hx.1).2.
        cbn in Hx. rewrite Hx.2.
        reflexivity.
      + reflexivity.
  Defined.
        
End InterIdeal.

                
          
  
(** TODO: Sum of ideals *)

(** TODO: Product of ideals *)


Definition ideal_kernel {R S : CRing} (f : CRingHomomorphism R S) : Ideal R.
Proof.
  snrapply Build_Ideal.
  1: exact (grp_kernel f).
  snrapply Build_IsIdeal.
  intros r x.
  simpl in x.
  unfold hfiber in x.
  srefine (_;_).
  { exists (r * x.1).
    refine (rng_homo_mult f _ _ @ _).
    refine (ap _ _ @ rng_mult_zero_r (f r)).
    exact x.2. }
  reflexivity.
Defined.

(** This instance helps typeclass search by selecting a proof of normality, so that quotient rings, which are defined as quotient groups, are not confused. *)
Global Instance isnormal_ideal_kernel {R S} (f : CRingHomomorphism R S)
  : IsNormalSubgroup (ideal_kernel f).
Proof.
  apply isnormal_ab_subgroup.
Defined.

(** Properties of ideals *)

(** TODO: Maximal ideals *)
(** TODO: Principal ideal *)
(** TODO: Prime ideals *)

Class IsPrime (R : CRing) (I : Ideal R) :=
  {
    isprime_proper : ~ (exists x : I, ideal_incl x = 1);
    isprime_prime : forall (a b : R), (exists (x : I) , (ideal_incl x : R) = a * b) -> ((exists (y : I), ideal_incl y = a) + (exists (z : I), ideal_incl z = b))
    }.

(** TODO: Radical ideals *)

(** TODO: Minimal ideals *)

(** TODO: Primary ideals *)

