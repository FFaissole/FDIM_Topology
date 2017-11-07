
Require Export Coquelicot.Coquelicot.
Require Export Reals.
Require Export mathcomp.ssreflect.ssreflect.
Require Export FunctionalExtensionality.
Require Export hilbert.
Require Import Decidable.
Require Export lax_milgram.


(** * Finite spaces : canonical structure approach *)

Module FiniteDim.

Record mixin_of (E : ModuleSpace R_Ring) := Mixin {
  dim : nat ;
  B : nat -> E ;
  BO : B 0 = zero ;
  ax : forall u : E, exists L : nat -> R,
           u = sum_n (fun n => scal (L n) (B n)) dim
}.

Section ClassDef.

Record class_of (T : Type) := Class {
  base : ModuleSpace.class_of R_Ring T ;
  mixin : mixin_of (ModuleSpace.Pack R_Ring T base T)
}.
Local Coercion base : class_of >-> ModuleSpace.class_of.

Structure type := Pack { sort; _ : class_of sort ; _ : Type }.
Local Coercion sort : type >-> Sortclass.

Variable cT : type.

Definition class := let: Pack _ c _ := cT return class_of cT in c.

Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition AbelianGroup := AbelianGroup.Pack cT xclass xT.
Definition ModuleSpace := ModuleSpace.Pack _ cT xclass xT.

End ClassDef.

Module Exports.

Coercion base : class_of >-> ModuleSpace.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion AbelianGroup : type >-> AbelianGroup.type.
Canonical AbelianGroup.
Coercion ModuleSpace : type >-> ModuleSpace.type.
Canonical ModuleSpace.

Notation FiniteDim := type.

End Exports.

End FiniteDim.

Export FiniteDim.Exports.

Section AboutFiniteDim.

Context {E : FiniteDim}.

Definition dim : nat := FiniteDim.dim _ (FiniteDim.class E).

Definition B : nat -> E := FiniteDim.B _ (FiniteDim.class E).

End AboutFiniteDim.

Section FiniteSpaces.

Definition BR := (fun n : nat => match (le_gt_dec n 0) with
                     | left _ => (@zero R_Ring)
                     | right _ => (@one R_Ring)
                 end).

(** R is finite *)
Lemma R_one_c : forall u : Ring_ModuleSpace R_Ring,exists L : nat -> R,
         u = sum_n (fun n => scal (L n) (BR n)) 1.
Proof.
intros u.
exists (fun n => match n with |O => (@zero R_Ring) | _ => u end).
rewrite sum_Sn.
rewrite sum_O.
rewrite scal_zero_l.
rewrite plus_zero_l.
intuition.
Qed.

Lemma BR0 : BR 0 = zero.
Proof.
intuition.
Qed.

Definition R_FiniteDim_mixin :=
   FiniteDim.Mixin _ 1%nat (fun n => BR n) BR0 R_one_c.

Canonical R_FiniteDim :=
  FiniteDim.Pack R (FiniteDim.Class _ _ R_FiniteDim_mixin) R.

Definition dimE (E : FiniteDim) := FiniteDim.dim _ (FiniteDim.class E).
Definition Base (E : FiniteDim) := FiniteDim.B _ (FiniteDim.class E).

Lemma Dim0 (E : FiniteDim) : dimE E = O -> forall u : E, u = zero.
Proof.
intros.
assert (H0 : exists L : nat -> R,
           u = sum_n (fun n => scal (L n) ((Base E) n)) (dimE E)).
apply FiniteDim.ax.
rewrite H in H0.
destruct H0 as (L,H0).
rewrite sum_O in H0.
assert (H1 : Base E O = zero).
apply FiniteDim.BO.
rewrite H1 in H0.
rewrite H0.
rewrite scal_zero_r.
reflexivity.
Qed.

(** Cartesian product of finite space is finite *)

Definition BProd (E1 : FiniteDim) (E2 : FiniteDim) (B1 : nat -> E1) (B2 : nat -> E2) :=
   (fun n => match le_gt_dec n 0 with
               | left _ => zero
               | right _ => (match (le_gt_dec n (dimE E1)) with
                    | left _  => (B1 n,(@zero E2))
                    | right _ => (match (le_gt_dec n
                                 (dimE E1 + dimE E2)%nat) with
                        | left _ => ((@zero E1),B2 (n - (dimE E1))%nat)
                        | right _ => zero
                        end)
                    end)
               end).

Lemma BPR0 (E1 E2 : FiniteDim) (B1 : nat-> E1) (B2 : nat -> E2) :
            BProd E1 E2 B1 B2 O = zero.
Proof.
unfold BProd.
destruct (le_gt_dec 0 0).
reflexivity.
exfalso; intuition.
Qed.

Definition LProd (E1 E2 : FiniteDim) (L1 L2 : nat -> R) :=
  (fun n => match le_gt_dec n (dimE E1) with
             | left _ => L1 n
             | right _ => L2 ((n - dimE E1)%nat)
        end).

Lemma sum_n_fst (E1 E2 : ModuleSpace R_Ring) : forall (n : nat) (L : nat -> (E1*E2)),
        fst (sum_n (fun n => L n) n) = sum_n (fun n => fst (L n)) n.
Proof.
intros.
induction n.
simpl.
rewrite sum_O.
rewrite plus_zero_r.
reflexivity.
symmetry.
rewrite sum_Sn.
rewrite sum_Sn.
simpl.
f_equal.
unfold sum_n.
unfold sum_n_m.
unfold Iter.iter_nat.
simpl.
simpl in IHn.
unfold sum_n in IHn.
unfold sum_n_m, Iter.iter_nat in IHn.
simpl in IHn.
symmetry.
trivial.
Qed.

Lemma sum_n_snd (E1 E2 : ModuleSpace R_Ring) : forall (n : nat) (L : nat -> (E1*E2)),
        snd (sum_n (fun n => L n) n) = sum_n (fun n => snd (L n)) n.
Proof.
intros.
induction n.
simpl.
rewrite sum_O.
rewrite plus_zero_r.
reflexivity.
symmetry.
rewrite sum_Sn.
rewrite sum_Sn.
simpl.
f_equal.
unfold sum_n.
unfold sum_n_m.
unfold Iter.iter_nat.
simpl.
simpl in IHn.
unfold sum_n in IHn.
unfold sum_n_m, Iter.iter_nat in IHn.
simpl in IHn.
symmetry.
trivial.
Qed.

Lemma sum_n_m_decal (E : ModuleSpace R_Ring) : forall (n m d: nat) (L : nat -> E),
        sum_n_m (fun n => L n) m n = sum_n_m (fun n => L ((n - d)%nat)) (m + d)%nat (n + d)%nat.
Proof.
intros n m d L.
induction d.
assert ((fun n0 : nat => L (n0 - 0)%nat)
         =
        (fun n0 : nat => L n0)).
apply functional_extensionality.
intros x.
replace (x-0)%nat with x by intuition.
reflexivity.
rewrite H.
replace (m + 0)%nat with m by intuition.
replace (n + 0)%nat with n by intuition.
reflexivity.
rewrite IHd.
replace (m + S d)%nat with (S ((m + d)%nat)) by auto.
replace (n + S d)%nat with (S ((n + d)%nat)) by auto.
rewrite <- sum_n_m_S.
assert (Hss :(fun n0 : nat => L (n0 - d)%nat)
       =
       (fun n0 : nat => L (S n0 - S d)%nat)).
apply functional_extensionality.
intros n0.
replace (S n0 - S d)%nat with (n0 - d)%nat by auto.
reflexivity.
rewrite Hss.
reflexivity.
Qed.

Lemma Product_c (E1 E2 : FiniteDim) : forall (u : E1*E2), exists L : nat -> R,
    u = sum_n (fun n => scal (L n) ((BProd E1 E2 (Base E1) (Base E2) n))) ((dimE E1) + (dimE E2)).
Proof.
intros (u1,u2).
assert (H1 : forall (u1 : E1), exists L : nat -> R,
    u1 = sum_n (fun n => scal (L n) ((Base E1) n)) (dimE E1)).
apply FiniteDim.ax.
specialize (H1 u1).
destruct H1 as (L1,H1).
assert (H2 : forall (u2 : E2), exists L : nat -> R,
u2 = sum_n (fun n => scal (L n) ((Base E2) n)) (dimE E2)).
apply FiniteDim.ax.
specialize (H2 u2).
destruct H2 as (L2,H2).
exists (LProd E1 E2 L1 L2).
rewrite H1 H2.
apply injective_projections.
(* projection 1 *)
rewrite (sum_n_fst E1 E2).
simpl.
unfold BProd.
unfold sum_n.
rewrite (sum_n_m_Chasles _ 0 (dimE E1) (dimE E1 + dimE E2) ).
replace (sum_n_m (fun n : nat => scal (L1 n) (Base E1 n)) 0 (dimE E1))
      with (plus (sum_n_m (fun n : nat => scal (L1 n) (Base E1 n)) 0 (dimE E1))
           (sum_n_m (fun n : nat => (@zero E1))  (S (dimE E1)) (dimE E1 + dimE E2))).
f_equal.
apply sum_n_m_ext_loc.
intros k Hk.
destruct (le_gt_dec k 0).
assert (Hk0 : k = O).
intuition.
rewrite Hk0.
assert (Base E1 0 = zero).
apply FiniteDim.BO.
rewrite H.
intuition.
destruct (le_gt_dec k (dimE E1)).
simpl.
unfold LProd.
destruct (le_gt_dec k (dimE E1)).
reflexivity.
exfalso; intuition.
exfalso; intuition.
apply sum_n_m_ext_loc.
intros k Hk.
destruct (le_gt_dec k 0).
assert (Hk0 : k = O).
intuition.
rewrite Hk0.
simpl.
rewrite scal_zero_r.
reflexivity.
destruct (le_gt_dec k (dimE E1)).
exfalso; intuition.
destruct (le_gt_dec k (dimE E1 + dimE E2)).
simpl.
rewrite scal_zero_r.
reflexivity.
simpl.
rewrite scal_zero_r.
reflexivity.
rewrite sum_n_m_const_zero.
rewrite plus_zero_r.
reflexivity.
intuition.
intuition.
(* projection 2 *)
rewrite (sum_n_snd E1 E2).
simpl.
unfold sum_n.
rewrite (sum_n_m_Chasles _ 0 (dimE E1) (dimE E1 + dimE E2)).
replace (sum_n_m (fun n : nat => scal (L2 n) (Base E2 n)) 0 (dimE E2))
        with
        (plus
           (sum_n_m (fun n : nat => (@zero E2)) 0 (dimE E1))
           (sum_n_m (fun n : nat => scal (L2 n) (Base E2 n)) 0 (dimE E2))
        ).
f_equal.
apply sum_n_m_ext_loc.
intros k Hk.
unfold BProd.
destruct (le_gt_dec k 0).
simpl.
rewrite scal_zero_r.
reflexivity.
destruct (le_gt_dec k (dimE E1)).
simpl.
rewrite scal_zero_r.
reflexivity.
exfalso; intuition.
rewrite (sum_n_m_decal E2 (dimE E2) 0 (dimE E1)
        (fun n : nat => scal (L2 n) (Base E2 n))).
replace (dimE E1 + dimE E2)%nat with (dimE E2 + dimE E1)%nat
        by intuition.
assert (sum_n_m (fun n : nat => scal (L2 (n - dimE E1)%nat)
                        (Base E2 (n - dimE E1)))
             (0 + dimE E1) (dimE E2 + dimE E1) =
        sum_n_m (fun n : nat => scal (L2 (n - dimE E1)%nat)
                        (Base E2 (n - dimE E1)))
             (S (dimE E1)) (dimE E2 + dimE E1)).
simpl.
rewrite sum_Sn_m.
replace (dimE E1 - dimE E1)%nat with O by intuition.
replace (Base E2 0) with (@zero E2).
rewrite scal_zero_r.
rewrite plus_zero_l.
reflexivity.
symmetry.
apply FiniteDim.BO.
intuition.
rewrite H.
apply sum_n_m_ext_loc.
intros k Hk.
unfold BProd.
simpl.
destruct (le_gt_dec k 0).
assert (HO : (k = O)%nat).
intuition.
rewrite HO.
replace (0 - dimE E1)%nat with O by intuition.
replace (Base E2 0) with (@zero E2).
simpl.
repeat (rewrite scal_zero_r); reflexivity.
symmetry.
apply FiniteDim.BO.
destruct (le_gt_dec k (dimE E1)).
exfalso; intuition.
destruct (le_gt_dec k (dimE E1 + dimE E2)).
simpl.
replace (k-0)%nat with k by intuition.
unfold LProd.
destruct (le_gt_dec k (dimE E1)).
unfold LProd.
destruct (dimE E1).
exfalso; intuition.
exfalso; intuition.
reflexivity.
unfold LProd.
destruct (le_gt_dec k (dimE E1)).
exfalso; intuition.
exfalso; intuition.
rewrite sum_n_m_const_zero.
rewrite plus_zero_l.
reflexivity.
intuition.
intuition.
Qed.

Context {E1 E2 : FiniteDim}.

Definition E1xE2_FiniteDim_mixin :=
    FiniteDim.Mixin _ (dimE E1 + dimE E2) (BProd E1 E2 (Base E1) (Base E2))
                          (BPR0 E1 E2 (Base E1) (Base E2)) (Product_c E1 E2).

Canonical E1xE2_FiniteDim :=
  FiniteDim.Pack (E1*E2) (FiniteDim.Class _ _ E1xE2_FiniteDim_mixin) (E1*E2).

End FiniteSpaces.
