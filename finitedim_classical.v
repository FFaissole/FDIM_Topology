
Require Export Coquelicot.Coquelicot.
Require Export Reals.
Require Export mathcomp.ssreflect.ssreflect.
Require Export FunctionalExtensionality.
Require Export hilbert.
Require Import Decidable.
Require Export lax_milgram.
Require Import Classical.

(** * Finite dimensional subspaces *)


(** Lemma about distributivity of inner product on sums *)
Lemma inner_sum_n {E : Hilbert} : forall m f (x : E),
    inner (sum_n (fun n => f n) m) x
      = sum_n (fun n => inner (f n) x) m.
Proof.
intros m f x.
induction m.
now rewrite 2!sum_O.
rewrite 2!sum_Sn.
rewrite inner_plus_l.
rewrite IHm.
reflexivity.
Qed.


Section FDIM_span.

(** * Finite dimensional subspaces *) 
Context{E : Hilbert}.
Definition phi_FDIM (p : E -> Prop) (dim : nat) (B : nat -> E)
          := match (eq_nat_dec dim 0) with
              | left _ => forall u, p u <-> u = zero
              | right _ => forall u, p u <-> exists L : nat -> R,
           u = sum_n (fun n => scal (L n) (B n)) (dim - 1)
         end.

(** * Linear span *)

Definition span (u : E) := fun x:E => (exists (l : R), x = scal l u).

(** clean_scal transformer *)
Definition clean_scal (u : E) (F : (E -> Prop) -> Prop):
                       (R -> Prop) -> Prop
     := fun A : (R -> Prop) => exists V : E -> Prop,
           F V /\ (forall l,  V (scal l u) -> A l).

Lemma proper_scal' (u : E) (F : (E -> Prop) -> Prop) :
  ProperFilter F -> (forall V : E -> Prop, F V -> exists x : E,
                            V x /\ span u x)
                    ->  ProperFilter' (clean_scal u F).
Proof.
intros (FF1,FF2).
intros Hsp.
constructor.
intro Hkk.
unfold clean_scal in Hkk.
destruct Hkk as (V,(H1,H2)).
specialize (Hsp V H1).
destruct Hsp as (k,(Hk,(l,Hkl))).
apply (H2 l).
now rewrite Hkl in Hk.
constructor.
unfold clean_scal.
exists (fun _ : E => True).
split.
apply FF2.
now intros.
intros P Q HP HQ.
unfold clean_scal in *.
destruct FF2.
destruct HP as (V,(P1,P2)).
destruct HQ as (V',(Q1,Q2)).
exists (fun x : E => V x /\ V' x).
split.
now apply filter_and.
intros l (HL1,HL2).
split.
now apply P2.
now apply Q2.
intros P Q HImp (V,(HP1,HP2)).
unfold clean_scal in *.
exists V.
split; try assumption.
intros l Hvl.
apply HImp.
now apply HP2.
Qed.

Lemma proper_scal (u : E) (F : (E -> Prop) -> Prop) :
  ProperFilter F -> (forall V : E -> Prop, F V ->  exists x : E,
                            V x /\ span u x)
                    ->  ProperFilter (clean_scal u F).
Proof.
intros (FF1,FF2).
intros Hsp.
constructor.
unfold clean_scal.
intros P (V,(HV1,HV2)).
destruct (FF1 V HV1) as (f,Hf).
specialize (Hsp V HV1).
destruct Hsp as (x,(Hx1,(l,Hx2))).
exists l.
apply HV2.
now rewrite <- Hx2.
constructor.
unfold clean_scal.
exists (fun _ : E => True).
split.
apply FF2.
now intros.
intros P Q HP HQ.
unfold clean_scal in *.
destruct FF2.
destruct HP as (V,(P1,P2)).
destruct HQ as (V',(Q1,Q2)).
exists (fun x : E => V x /\ V' x).
split.
now apply filter_and.
intros l (HL1,HL2).
split.
now apply P2.
now apply Q2.
intros P Q HImp (V,(HP1,HP2)).
unfold clean_scal in *.
exists V.
split; try assumption.
intros l Hvl.
apply HImp.
now apply HP2.
Qed.

Lemma cauchy_scal (u : E) (F : (E -> Prop) -> Prop) :
  u <> zero -> ProperFilter F -> cauchy F -> (forall V : E -> Prop, F V -> exists x : E,
                            V x /\ span u x)
                    ->  cauchy (clean_scal u F).
Proof.
intros Ho PF C HV.
unfold cauchy.
intros e.
unfold clean_scal.
unfold cauchy in C.
assert (hp : 0 < (e * norm u) / 2).
apply Rmult_lt_0_compat.
apply Rmult_lt_0_compat.
apply e.
now apply norm_gt_0.
intuition.
pose (eu := mkposreal ((e * norm u)/2) hp).
specialize (C eu).
simpl in C.
destruct C as (x,C).
unfold Hierarchy.ball in C; simpl in C; unfold ball in C; simpl in C.
specialize (HV (fun y : E => Hnorm (minus x y) < ((e * norm u) / 2)) C).
destruct HV as (z,(HV1,(l,HV2))).
exists l.
exists (fun y : E => Hnorm (minus z y) < e * norm u).
split.
apply filter_imp with (fun y : E => Hnorm (minus x y) < (e * norm u)/2).
intros s Hs.
generalize (norm_triangle (minus z x) (minus x s)) => Hnt.
assert (Ha : plus (minus z x) (minus x s) = minus z s).
unfold minus.
rewrite (Hierarchy.plus_comm x (opp s)).
rewrite plus_assoc_gen.
rewrite plus_opp_l.
now rewrite plus_zero_r.
rewrite Ha in Hnt.
apply Rle_lt_trans with
      (Hnorm (minus z x) + Hnorm (minus x s)).
trivial.
replace (e * norm u) with ((e * norm u / 2)+(e * norm u / 2)) by field.
apply Rplus_lt_le_compat.
replace (Hnorm (minus z x)) with (Hnorm (minus x z)).
trivial.
unfold Hnorm.
f_equal.
unfold minus.
rewrite inner_plus_l.
rewrite inner_plus_l.
rewrite inner_opp_l.
rewrite inner_opp_l.
rewrite Rplus_comm.
f_equal.
replace (plus z (opp x)) with
           (opp (plus x (opp z))).
now rewrite inner_opp_r.
rewrite opp_plus.
rewrite opp_opp.
now rewrite Hierarchy.plus_comm.
replace (plus x (opp z)) with
           (opp (plus z (opp x))).
now rewrite inner_opp_r.
rewrite opp_plus.
rewrite opp_opp.
now rewrite Hierarchy.plus_comm.
intuition.
trivial.
intros l0 Hl0.
unfold Hierarchy.ball; simpl.
unfold AbsRing_ball; simpl.
rewrite HV2 in HV1.
rewrite HV2 in Hl0.
assert (Hl0' : Hnorm (scal (minus l l0) u) < e * norm u).
unfold minus.
rewrite scal_distr_r.
rewrite scal_opp_l.
now unfold minus in Hl0.
rewrite norm_scal in Hl0'.
unfold abs.
simpl.
simpl in Hl0'.
apply Rmult_lt_reg_r in Hl0'.
rewrite Rabs_minus_sym.
trivial.
unfold Hnorm.
now apply norm_gt_0.
Qed.

(*

Hypothesis Hdec3 : forall (u : E) (V : E -> Prop),
             decidable (exists x : E, V x /\ span u x).

Hypothesis Hdec4 : forall u:E, forall x:E, decidable (span u x).*)

Lemma my_complete_classical_def (u : E) : my_complete (span u) ->
         (forall F : (E -> Prop) -> Prop,
             ProperFilter F -> cauchy F ->
             (forall P : E -> Prop, F P ->
             (exists x : E, P x /\ span u x)) -> span u (lim F)).
Proof.
intros Hmc F PF cF HFF.
assert (Hdsnn : forall x:E, span u x <-> ~~ span u x).
intros x.
split. 
intros S Hf; apply Hf; trivial.
apply NNPP.
apply Hmc; trivial.
intros P HP.
specialize (HFF P HP).
intros S; apply S; trivial.
Qed.

(** closedness of the linear span *)
Lemma span_closed (u : E) : my_complete (span u).
Proof.
destruct (is_zero_dec u).
assert (Hdsnn : forall x:E, span u x <-> ~~ span u x).
intros x.
split. 
intros S Hf; apply Hf; trivial.
apply NNPP.
assert (Hds2 : my_complete (span u) <->
               my_complete (fun x:E => ~~ span u x)).
split.
intro Hh.
generalize my_complete_classical_def => MCDD.
unfold my_complete.
intros F PF cF HFF.
apply Hdsnn.
apply Hh; try assumption.
intros P HP.
specialize (HFF P HP).
intros Hj.
apply HFF.
intros (l,Hl).
apply Hj.
exists l.
split; try easy.
destruct Hl as (Hl1,Hl2).
now apply Hdsnn in Hl2.
intros HH F PF cF HF.
unfold my_complete in HH.
apply Hdsnn.
apply HH; try assumption.
intros P HP.
specialize (HF P HP).
intro Hj.
apply HF.
intros (l,Hl).
destruct Hl as (Hl1,Hl2).
apply Hj.
exists l.
split; try easy.
rewrite Hds2.
apply closed_my_complete.
unfold closed; unfold open; simpl.
intros x Hx.
unfold locally.
unfold Hierarchy.ball; simpl.
unfold ball; simpl.
assert (0 < 1).
intuition.
pose (e := mkposreal 1 H0).
destruct (is_zero_dec x).
exists e.
intros y Hh.
unfold span in Hx.
exfalso.
apply Hx.
exists e.
rewrite H1.
rewrite H.
rewrite scal_zero_r.
reflexivity.
assert (Hnx : 0 < norm x).
apply norm_gt_0.
trivial.
exists (mkposreal (norm x) Hnx).
intros y Hk.
simpl in Hk.
intro.
unfold span in H2.
destruct H2 as (l,H2).
rewrite H in H2.
rewrite scal_zero_r in H2.
rewrite H2 in Hk.
unfold minus in Hk.
rewrite opp_zero in Hk.
rewrite plus_zero_r in Hk.
unfold Hnorm in Hk.
unfold norm in Hk.
simpl in Hk.
unfold Hnorm in Hk.
absurd (sqrt (inner x x) < sqrt (inner x x)).
apply Rlt_irrefl.
trivial.
assert (HO := H); clear H.
assert (Ho' : norm u <> 0).
generalize (norm_gt_0 u HO) => NG.
apply Rlt_dichotomy_converse.
right.
intuition.
assert (Ho'' : 0 < norm u).
now apply norm_gt_0.
intros F PF CF H.
pose (ff := clean_scal u F).
exists (lim ff).
assert (Hk : forall P : Hilbert_CompleteSpace -> Prop,
    F P -> (exists x : Hilbert_CompleteSpace, P x /\ span u x)).
intros P HP.
apply NNPP.
now apply H. 
clear H.
generalize (proper_scal u F PF Hk) => ffP.
generalize (cauchy_scal u F HO PF CF Hk) => ffC.
fold ff in ffP, ffC.
apply ball_eq.
intros eu.
unfold cauchy in ffC, CF.
simpl in ffC, CF.
generalize (@complete_cauchy _ ff ffP ffC) => Hff.
simpl in Hk.
unfold ff in Hff at 1.
unfold clean_scal in Hff.
assert (Hep : 0 < (eu / norm u) /2).
apply Rmult_lt_0_compat.
apply Rmult_lt_0_compat.
apply eu.
generalize (norm_gt_0 u HO) => NG.
assert (/ norm u <> 0).
apply Rinv_neq_0_compat.
apply Rlt_dichotomy_converse.
right.
intuition.
intuition.
intuition.
pose (e := mkposreal ((eu / norm u)/2) Hep).
specialize (Hff (mkposreal e Hep)).
destruct Hff as (V,(Hv1,Hv2)).
generalize Hk => Hk0.
generalize (@complete_cauchy _ F PF CF) => HC.
assert (P2 : 0 < eu/2).
apply Rmult_lt_0_compat.
apply eu.
intuition.
specialize (HC (mkposreal (eu/2) P2)).
assert (H : F (fun x:E => (V x) /\
          (Hierarchy.ball (Hierarchy.lim F) (eu/2)) x)).
now apply filter_and.
specialize (Hk0 _ H).
destruct Hk0 as (x0,((Hx01,Hx02),(lx,Hx1))).
rewrite Hx1 in Hx02.
rewrite Hx1 in Hx01.
specialize (Hv2 lx Hx01).
simpl in Hv2.
unfold Hierarchy.ball; simpl.
unfold ball; simpl.
unfold Hierarchy.ball in Hx02, Hv2.
simpl in Hx02, Hv2.
unfold ball in Hx02; simpl in Hx02.
unfold AbsRing_ball in Hv2; simpl in Hv2.
clear Hx01 H HC P2 Hx1 Hv1.
clear PF CF Hk ffP ffC.
assert (HX2 : Hnorm (minus (scal lx u) (scal (lim ff) u)) < eu / 2).
replace (minus (scal lx u) (scal (lim ff) u))
   with (scal (minus lx (lim ff)) u).
rewrite norm_scal.
apply Rmult_lt_reg_r with (/ norm u).
generalize (norm_gt_0 u HO) => NG.
assert (/ norm u <> 0).
apply Rinv_neq_0_compat.
apply Rlt_dichotomy_converse.
right.
intuition.
intuition.
field_simplify.
unfold norm.
simpl.
field_simplify.
replace (Rabs (minus lx (lim ff)) / 1)
        with (abs (minus lx (lim ff))).
replace (eu / (2 * Hnorm u)) with (eu / norm u / 2).
trivial.
field_simplify.
reflexivity.
generalize (norm_gt_0 u HO) => NG.
apply Rlt_dichotomy_converse.
right; intuition.
generalize (norm_gt_0 u HO) => NG.
apply Rlt_dichotomy_converse.
right; intuition.
field_simplify.
reflexivity.
trivial.
trivial.
trivial.
trivial.
unfold minus.
rewrite scal_distr_r.
now rewrite scal_opp_l.
assert (Hy : minus (lim F) (scal (lim ff) u) =
        (plus (minus (lim F) (scal lx u))
        (minus (scal lx u) (scal (lim ff) u)))).
unfold minus.
rewrite (Hierarchy.plus_comm
         (scal lx u) (opp (scal (lim ff) u))).
rewrite plus_assoc_gen.
rewrite plus_opp_l.
rewrite plus_zero_r.
reflexivity.
generalize (norm_triangle (minus (lim F) (scal lx u))
        (minus (scal lx u) (scal (lim ff) u))) => Hnt.
rewrite Hy.
apply Rle_lt_trans with (Hnorm (minus (lim F) (scal lx u)) +
      Hnorm (minus (scal lx u) (scal (lim ff) u))).
trivial.
assert (H2p : 0  < eu / 2).
apply Rmult_lt_0_compat.
apply eu.
intuition.
destruct eu as (eu,Heu).
simpl.
replace eu with (plus (eu/2) (eu/2)).
simpl in Hx02.
simpl in HX2.
now apply Rplus_lt_compat.
unfold plus.
simpl.
field.
Qed.

End FDIM_span.

(** * Orthogonal projection *)

Section FDIM_sum.

Context {E : Hilbert}.

Definition proj (V : E -> Prop) :=
          fun u : E => iota (fun v : E => V v /\ norm (minus u v)
        = Glb_Rbar (fun r => exists w:E, V w /\ r = norm (minus u w))).

Definition proj' (V : E -> Prop) := fun u : E => minus u (proj V u).

Variable G : E -> Prop.

Hypothesis HcG : my_complete G.

Hypothesis HcM : compatible_m G.

Lemma my_complete_complete : complete_subset G.
Proof.
unfold my_complete in HcG.
unfold complete_subset.
exists lim.
intros F PF cF HF.
split.
apply HcG; try assumption.
intros e.
generalize (@complete_cauchy _ F PF cF) => HC.
apply HC.
Qed.

Lemma projG : forall x, G (proj G x).
Proof.
intros x.
unfold proj.
assert (exists! v : E, G v /\ norm (minus x v)
        = Glb_Rbar (fun r => exists w:E, G w /\ r = norm (minus x w))).
apply: ortho_projection_subspace; try assumption.
apply my_complete_complete.
trivial.
intros eps.
apply classic.
destruct H as (c,H).
assert (H' := H).
apply iota_elim in H'.
rewrite H'.
apply H.
Qed.

(** clean_proj and clean_proj' transformers *)
Definition clean_proj (u : E) (F : (E -> Prop) -> Prop) :
                   (E -> Prop) -> Prop
        := filtermap (proj G) F.

Definition clean_proj' (u : E) (F : (E -> Prop) -> Prop) :
                   (E -> Prop) -> Prop
        := filtermap (proj' G) F.

Lemma norm_minus_sym : forall x y : E, Hnorm (minus x y) = Hnorm (minus y x).
Proof.
intros x y.
unfold Hnorm.
assert (Hin : inner (minus x y) (minus x y)
            = inner (minus y x) (minus y x)).
replace (minus y x) with (opp (minus x y)) at 1.
rewrite inner_opp_l.
replace (minus y x) with (opp (minus x y)).
rewrite inner_opp_r.
ring_simplify.
reflexivity.
unfold minus.
rewrite opp_plus.
rewrite opp_opp.
rewrite Hierarchy.plus_comm.
reflexivity.
unfold minus.
rewrite opp_plus.
rewrite opp_opp.
rewrite Hierarchy.plus_comm.
reflexivity.
rewrite Hin.
reflexivity.
Qed.

Lemma PFsum : forall x, plus (proj G x) (proj' G x) = x.
Proof.
intros x.
unfold proj'.
unfold minus.
rewrite Hierarchy.plus_comm.
rewrite <- Hierarchy.plus_assoc.
rewrite plus_opp_l.
rewrite plus_zero_r.
reflexivity.
Qed.

Lemma PGuisu : forall x, G x -> (proj G x = x).
Proof.
intros x Gx.
generalize (my_complete_complete) => Hcc.
generalize (@direct_sum_with_orth_compl_charac1
             E G HcM Hcc x (proj G x)) => Ds1.
generalize (projG x) => GP.
specialize (Ds1 GP).
assert (Hu : exists! v:E,
          G v /\ norm (minus x v)
        = Glb_Rbar (fun r => exists w:E, G w /\ r = norm (minus x w))).
apply: ortho_projection_subspace; try easy.
intros eps; apply classic.
destruct Hu as (k,Hk).
assert (Hk2 := Hk).
apply iota_elim in Hk.
assert (iota (fun v : E =>
        G v /\
        norm (minus x v) =
        Glb_Rbar (fun r : R => exists w : E, G w /\ r = norm (minus x w)))
        = proj G x).
unfold proj.
reflexivity.
rewrite H in Hk.
rewrite <- Hk in Hk2.
assert (Ha : norm (minus x (proj G x)) =
      Glb_Rbar (fun r : R => exists w : E, G w /\ r = norm (minus x w))).
apply Hk2.
clear Hk2 Hk H.
specialize (Ds1 Ha).
clear Ha.
now apply Ds1.
Qed.

Lemma PGorth_compl : forall x, orth_compl G x -> (proj G x = zero).
Proof.
intros x Gx.
generalize (my_complete_complete) => Hcc.
generalize (@direct_sum_with_orth_compl_charac2
             E G HcM Hcc x (proj G x)) => Ds2.
generalize (projG x) => GP.
specialize (Ds2 GP).
assert (Hu : exists! v:E,
          G v /\ norm (minus x v)
        = Glb_Rbar (fun r => exists w:E, G w /\ r = norm (minus x w))).
apply: ortho_projection_subspace; try easy.
intros eps; apply classic.
destruct Hu as (k,Hk).
assert (Hk2 := Hk).
apply iota_elim in Hk.
assert (iota (fun v : E =>
        G v /\
        norm (minus x v) =
        Glb_Rbar (fun r : R => exists w : E, G w /\ r = norm (minus x w)))
        = proj G x).
unfold proj.
reflexivity.
rewrite H in Hk.
rewrite <- Hk in Hk2.
assert (Ha : norm (minus x (proj G x)) =
      Glb_Rbar (fun r : R => exists w : E, G w /\ r = norm (minus x w))).
apply Hk2.
clear Hk2 Hk H.
specialize (Ds2 Ha).
clear Ha.
now apply Ds2.
Qed.

(** linearity of proj *)
Lemma lin_proj : is_linear_mapping (proj G).
Proof.
split.
intros x y.
assert (H : exists! v:E,
          G v /\ norm (minus (plus x y) v)
        = Glb_Rbar (fun r => exists w:E, G w /\ r = norm (minus (plus x y) w))).
apply: ortho_projection_subspace; try easy.
apply my_complete_complete.
intros eps; apply classic.
destruct H as (zxy,Hxy).
assert (H : exists! v:E,
          G v /\ norm (minus x v)
        = Glb_Rbar (fun r => exists w:E, G w /\ r = norm (minus x w))).
apply: ortho_projection_subspace; try easy.
apply my_complete_complete.
intros eps; apply classic.
destruct H as (zx,Hx).
assert (H : exists! v:E,
          G v /\ norm (minus y v)
        = Glb_Rbar (fun r => exists w:E, G w /\ r = norm (minus y w))).
apply: ortho_projection_subspace; try easy.
apply my_complete_complete.
intros eps; apply classic.
destruct H as (zy,Hy).
assert (H : unique (fun v : E =>
         G v /\
         norm (minus (plus x y) v) =
         Glb_Rbar
           (fun r : R => exists w : E, G w /\ r = norm (minus (plus x y) w)))
        (plus zx zy)).
split.
split.
destruct HcM as ((HcM1,HcM2),HcM3).
replace zy with (opp (opp zy)).
apply HcM1.
apply Hx.
replace (opp zy) with (scal (opp one) zy).
apply HcM3.
apply Hy.
rewrite scal_opp_one; reflexivity.
rewrite opp_opp; reflexivity.
generalize (@charac_ortho_projection_subspace2
             E G HcM (plus x y) (plus zx zy)) => CC.
assert (Hgs : G (plus zx zy)).
destruct HcM as ((HcM1,HcM2),HcM3).
replace zy with (opp (opp zy)).
apply HcM1.
apply Hx.
replace (opp zy) with (scal (opp one) zy).
apply HcM3.
apply Hy.
rewrite scal_opp_one.
reflexivity.
rewrite opp_opp.
reflexivity.
specialize (CC Hgs).
clear Hgs.
apply CC.
intros w Hw.
rewrite inner_plus_l.
rewrite inner_plus_l.
f_equal.
revert Hw.
apply charac_ortho_projection_subspace2.
trivial.
apply Hx.
apply Hx.
revert Hw.
apply charac_ortho_projection_subspace2.
trivial.
apply Hy.
apply Hy.
intros xs (Hg,H).
assert (Hu : unique (fun t => G t /\ norm (minus (plus x y) t) =
     Glb_Rbar
       (fun r0 : R => exists w : E, G w /\ r0 = norm (minus (plus x y) w))) xs).
split.
split; trivial.
assert (Hn : exists! t:E, G t /\ norm (minus (plus x y) t) =
     Glb_Rbar
       (fun r0 : R => exists w : E, G w /\ r0 = norm (minus (plus x y) w))).
apply: ortho_projection_subspace.
trivial.
apply my_complete_complete.
intros eps; apply classic.
trivial.
destruct Hn as (p,Hn).
assert (Hn' := Hn).
assert (Hn'' := Hn).
apply iota_elim in Hn'.
intros x' Hx'.
destruct Hn as (Hn1,Hn2).
specialize (Hn2 x' Hx').
rewrite <- Hn2.
destruct Hn'' as (Hn''1,Hn''2).
specialize (Hn''2 xs).
symmetry.
apply Hn''2.
split; trivial.
assert (Hu2 : G (plus zx zy) /\  norm (minus (plus x y) (plus zx zy)) =
       Glb_Rbar
       (fun r0 : R => exists w : E, G w /\ r0 = norm (minus (plus x y) w))).
split.
destruct HcM as ((HcM1,Ho),HcM2).
replace zy with (opp (opp zy)).
apply HcM1.
apply Hx.
replace (opp zy) with (scal (opp one) zy).
apply HcM2.
apply Hy.
rewrite scal_opp_one.
reflexivity.
rewrite opp_opp.
reflexivity.
generalize (@charac_ortho_projection_subspace2
             E G HcM (plus x y) (plus zx zy)) => CC.
assert (Hgi : G (plus zx zy)).
destruct HcM as ((HcM1,Ho),HcM2).
replace zy with (opp (opp zy)).
apply HcM1.
apply Hx.
replace (opp zy) with (scal (opp one) zy).
apply HcM2.
apply Hy.
rewrite scal_opp_one.
reflexivity.
rewrite opp_opp.
reflexivity.
specialize (CC Hgi).
apply CC.
intros w Hw.
rewrite inner_plus_l.
rewrite inner_plus_l.
f_equal.
revert Hw.
apply charac_ortho_projection_subspace2.
trivial.
apply Hx.
apply Hx.
revert Hw.
apply charac_ortho_projection_subspace2.
trivial.
apply Hy.
apply Hy.
unfold unique in Hu.
destruct Hu as (Hu,Hu').
symmetry.
apply Hu'.
trivial.
apply iota_elim in H.
apply iota_elim in Hxy.
apply iota_elim in Hx.
apply iota_elim in Hy.
rewrite <- Hx in H.
rewrite <- Hy in H.
now unfold proj.
(* scal *)
intros x l.
assert (H : exists! v:E,
          G v /\ norm (minus (scal l x) v)
        = Glb_Rbar (fun r => exists w:E, G w /\ r = norm (minus (scal l x) w))).
apply: ortho_projection_subspace; try easy.
apply my_complete_complete.
intros eps; apply classic.
destruct H as (z,Hz).
assert (H : exists! v:E,
          G v /\ norm (minus x v)
        = Glb_Rbar (fun r => exists w:E, G w /\ r = norm (minus x w))).
apply: ortho_projection_subspace; try easy.
apply my_complete_complete.
intros eps; apply classic.
destruct H as (s,H0).
assert (H : unique (fun v : E =>
         G v /\
         norm (minus (scal l x) v) =
         Glb_Rbar
           (fun r : R => exists w : E, G w /\ r = norm (minus (scal l x) w)))
        (scal l s)).
split.
split.
destruct HcM as ((HcM1,HcM2),HcM3).
apply HcM3.
apply H0.
generalize (@charac_ortho_projection_subspace2
             E G HcM (scal l x) (scal l s)) => CC.
assert (Hgs : G (scal l s)).
destruct HcM as ((HcM1,HcM2),HcM3).
apply HcM3.
apply H0.
specialize (CC Hgs).
clear Hgs.
apply CC.
intros w Hw.
rewrite inner_scal_l.
rewrite inner_scal_l.
apply Rmult_eq_compat_l.
revert Hw.
apply charac_ortho_projection_subspace2.
trivial.
apply H0.
apply H0.
intros r (H1,H2).
assert (Hu : unique (fun t => G t /\ norm (minus (scal l x) t) =
     Glb_Rbar
       (fun r0 : R => exists w : E, G w /\ r0 = norm (minus (scal l x) w))) r).
split.
split; trivial.
assert (Hn : exists! t:E, G t /\ norm (minus (scal l x) t) =
     Glb_Rbar
       (fun r0 : R => exists w : E, G w /\ r0 = norm (minus (scal l x) w))).
apply: ortho_projection_subspace.
trivial.
apply my_complete_complete.
intros eps; apply classic.
trivial.
destruct Hn as (p,Hn).
assert (Hn' := Hn).
assert (Hn'' := Hn).
apply iota_elim in Hn'.
intros x' Hx'.
destruct Hn as (Hn1,Hn2).
specialize (Hn2 x' Hx').
rewrite <- Hn2.
destruct Hn'' as (Hn''1,Hn''2).
specialize (Hn''2 r).
symmetry.
apply Hn''2.
split; trivial.
assert (Hu2 : G (scal l s) /\  norm (minus (scal l x) (scal l s)) =
       Glb_Rbar
       (fun r0 : R => exists w : E, G w /\ r0 = norm (minus (scal l x) w))).
split.
destruct HcM as (HcM1,HcM2).
apply HcM2; apply H0.
replace (minus (scal l x) (scal l s)) with (scal l (minus x s)).
unfold norm.
simpl.
rewrite norm_scal.
unfold Glb_Rbar.
destruct (ex_glb_Rbar
    (fun r0 : R => exists w : E, G w /\ r0
     = Hnorm (minus (scal l x) w))).
simpl.
unfold is_glb_Rbar in i.
destruct i as (I1,I2).
unfold is_lb_Rbar in I1.
unfold is_lb_Rbar in I2.
assert (J1 : Rbar_le x0 (Rabs l * Hnorm (minus x s))).
apply I1.
exists (scal l s).
split.
apply (proj2 HcM).
apply H0.
rewrite <- norm_scal.
unfold minus.
rewrite scal_distr_l.
rewrite scal_opp_r.
reflexivity.
assert (J2 : Rbar_le (Rabs l * Hnorm (minus x s)) x0).
apply I2.
intros x1 Hx1.
destruct Hx1 as (w,(Hw1,Hw2)).
rewrite Hw2.
destruct (is_zero_dec l).
rewrite H.
rewrite Rabs_R0.
simpl.
ring_simplify.
apply norm_ge_0.
assert (Hq : exists y:E, G y /\ (y = scal (1 / l) w)).
exists (scal (1/l) w).
split.
apply (proj2 HcM).
trivial.
reflexivity.
destruct Hq as (y,(Hy1,Hy2)).
assert (Hc : w = scal l y).
rewrite Hy2.
rewrite scal_assoc.
unfold mult.
simpl.
replace (l * (1 / l)) with 1.
rewrite scal_one.
reflexivity.
now field.
rewrite Hc.
rewrite <- norm_scal.
unfold minus.
rewrite <- scal_opp_r.
rewrite <- scal_distr_l.
assert (Rap : 0 < Rabs l).
now apply Rabs_pos_lt.
rewrite norm_scal.
rewrite norm_scal.
pose (L := mkposreal (Rabs l) Rap).
generalize (Rbar_mult_pos_le (Hnorm (minus x s))
                             (Hnorm (minus x y))
                              L) => RMP.
simpl in RMP.
assert (RMP' : Hnorm (minus x s) <= Hnorm (minus x y) <->
       Rabs l * Hnorm (minus x s)<= Rabs l * Hnorm (minus x y)).
rewrite RMP.
rewrite Rmult_comm.
rewrite (Rmult_comm (Hnorm (minus x y)) (Rabs l)).
reflexivity.
clear RMP.
unfold Rbar_le.
rewrite <- RMP'.
assert (HG: norm (minus x s) =
        Glb_Rbar (fun r : R => exists w : E, G w /\ r = norm (minus x w))).
apply H0.
unfold Glb_Rbar in HG.
destruct ((ex_glb_Rbar
          (fun r0 : R => exists w0 : E, G w0 /\ r0 = norm (minus x w0)))).
simpl in HG.
unfold is_glb_Rbar in i.
unfold is_lb_Rbar in i.
destruct i as (S1,S2).
destruct x2.
unfold real in HG.
rewrite <- HG in S1.
unfold norm in HG.
simpl in HG.
specialize (S1 (Hnorm (minus x y))).
simpl in S1.
apply S1.
exists y.
split.
trivial.
reflexivity.
simpl in S1.
specialize (S1 (norm (minus x w))).
exfalso.
apply S1.
exists w.
split.
trivial.
reflexivity.
simpl in HG.
unfold norm in HG; simpl in HG.
rewrite HG.
apply norm_ge_0.
generalize (Rbar_le_antisym (Rabs l * Hnorm (minus x s)) x0) => RL.
specialize (RL J2 J1).
destruct x0.
intuition.
simpl in J1.
now exfalso.
simpl in J2.
now exfalso.
rewrite scal_distr_l.
unfold minus.
rewrite scal_opp_r.
reflexivity.
unfold unique in Hu.
destruct Hu as (Hu,Hu').
symmetry.
apply Hu'.
trivial.
apply iota_elim in H.
apply iota_elim in H0.
rewrite <- H0 in H.
now unfold proj.
Qed.

(** metric properties of proj  *)
Lemma proj_min : forall x:E, norm (proj G x) <= norm x.
Proof.
intros x.
destruct (is_zero_dec x).
assert (GO : G zero).
destruct HcM as ((HcM1,Ho),HcM2).
destruct Ho as (z,Ho).
specialize (HcM2 z 0%R).
rewrite scal_zero_l in HcM2.
now apply HcM2.
rewrite H.
generalize (@PGuisu zero GO) => Gz.
rewrite Gz.
apply Rle_refl.
destruct (is_zero_dec (proj G x)).
rewrite H0.
unfold norm. simpl.
rewrite norm_zero.
apply norm_ge_0.
apply Rmult_le_reg_r with (norm (proj G x)).
apply norm_gt_0.
trivial.
rewrite squared_norm.
generalize (@charac_ortho_projection_subspace2
             E G HcM x (proj G x) (projG x)) => CC.
assert (Hh : inner (proj G x) (proj G x) = inner x (proj G x)).
apply CC.
assert (He : exists! v:E,
          G v /\ norm (minus x v)
        = Glb_Rbar (fun r => exists w:E, G w /\ r = norm (minus x w))).
apply: ortho_projection_subspace; try easy.
apply my_complete_complete.
intros eps; apply classic.
destruct He as (c,He).
assert (He' := He).
apply iota_elim in He.
assert (He2 : iota
       (fun v : E =>
        G v /\
        norm (minus x v) =
        Glb_Rbar
          (fun r : R => exists w : E, G w /\ r = norm (minus x w)))
       = proj G x).
unfold proj; reflexivity.
rewrite He in He2.
rewrite He2 in He'.
apply He'.
apply projG.
rewrite Hh.
apply Rle_trans with (Rabs (inner x (proj G x))).
unfold Rabs.
destruct (Rcase_abs (inner x (proj G x))).
apply Rle_trans with 0.
intuition.
intuition.
apply Rle_refl.
apply Cauchy_Schwartz_with_norm.
Qed.

Lemma proj_dist (e : posreal) :  forall x y: E,
                  Hierarchy.ball x e y -> (Hierarchy.ball (proj G x) e
                                                          (proj G y)).
Proof.
intros x y Hxy.
unfold Hierarchy.ball in *; simpl in *.
unfold ball in *; simpl in *.
assert (HL : minus (proj G x) (proj G y) = (proj G (minus x y))).
generalize lin_proj => LL.
destruct LL as (LL1,LL2).
unfold minus at 1.
assert (Ho : opp (proj G y) = scal (opp one) (proj G y)).
rewrite scal_opp_one; reflexivity.
rewrite Ho.
rewrite <- LL2.
rewrite LL1.
rewrite scal_opp_one.
reflexivity.
rewrite HL.
apply Rle_lt_trans with (Hnorm (minus x y)).
apply proj_min.
trivial.
Qed.

Lemma cauchy_proj (u : E) (F : (E -> Prop) -> Prop) :
             ProperFilter F -> cauchy F -> cauchy (clean_proj u F).
Proof.
intros PF cF.
unfold cauchy in *.
intros e.
specialize (cF e).
destruct cF as (x,cF).
exists (proj G x).
unfold clean_proj, filtermap.
apply filter_imp with (Hierarchy.ball x e); try assumption.
intros y Hy.
now apply proj_dist.
Qed.

Lemma cauchy_proj' (u : E) (F : (E -> Prop) -> Prop):
             ProperFilter F -> cauchy F -> cauchy (clean_proj' u F).
Proof.
intros PF cF.
unfold cauchy in *.
intros e.
assert (H2: 0 < e/ 2).
apply Rlt_div_r.
intuition.
ring_simplify.
apply e.
specialize (cF (mkposreal (e/2) H2)).
simpl in cF.
destruct cF as (x,cF).
exists (proj' G x).
unfold clean_proj', filtermap.
apply filter_imp with (Hierarchy.ball x (e/2)); try assumption.
intros y Hy.
unfold proj'.
unfold Hierarchy.ball; simpl.
unfold ball; simpl.
assert (Hl: (minus (minus x (proj G x)) (minus y (proj G y))) =
        (plus (minus x y) (minus (proj G y) (proj G x)))).
unfold minus.
rewrite (Hierarchy.plus_comm (proj G y) (opp (proj G x))).
rewrite plus_assoc_gen.
rewrite opp_plus.
rewrite opp_opp.
reflexivity.
rewrite Hl.
apply Rle_lt_trans with (plus (Hnorm (minus x y))
                        (Hnorm (minus (proj G y) (proj G x)))).
apply: norm_triangle.
destruct e as (e,he).
replace e with ((e/2) + (e /2)) by field.
simpl in *.
unfold plus; simpl.
apply Rplus_lt_compat.
unfold Hierarchy.ball in Hy.
simpl in Hy.
now unfold ball in Hy.
replace (Hnorm (minus (proj G y) (proj G x))) with
        (Hnorm (minus (proj G x) (proj G y))).
generalize (proj_dist (mkposreal (e/2) H2) x y) => Hdi.
unfold Hierarchy.ball in Hdi; simpl in Hdi.
unfold ball in Hdi; simpl in Hdi.
apply Hdi.
apply Hy.
rewrite norm_minus_sym.
reflexivity.
Qed.

(** sum of closed subset and linear span is closed, with 
continuity proofs of proj *)
Lemma sum_span_cl_cl : forall (u : E),
           orth_compl G u ->
         my_complete (fun x:E => exists g : E, exists w : E,
                      G g /\ span u w /\ x = plus g w).
Proof.
assert (GD : forall x:E, decidable (G x)).
intros x; red.
apply classic.
intros u Go.
case (GD u) => GU.
generalize (@direct_sumable_with_orth_compl E G) => Hz.
unfold direct_sumable in Hz.
specialize (Hz u GU Go).
intros F PF cF HF.
exists (lim F).
exists zero.
split.
apply HcG; try easy.
intros P HP S.
specialize (HF P HP).
apply HF.
intro S'.
apply S.
destruct S' as (x,(H1,(g,(w,(H2,(H3,H4)))))).
exists x.
split; try easy.
rewrite H4.
rewrite Hz in H3.
destruct H3 as (l,H3).
rewrite scal_zero_r in H3.
rewrite H3.
now rewrite plus_zero_r.
split.
exists 0%R.
rewrite scal_zero_l.
reflexivity.
rewrite plus_zero_r.
reflexivity.
intros F PF cF H.
simpl in *.
pose (Fw' := clean_proj u F).
pose (Fw'' := clean_proj' u F).
assert (Fw'PF : ProperFilter Fw').
now apply filtermap_proper_filter.
assert (Fw''PF : ProperFilter Fw'').
now apply filtermap_proper_filter.
exists (lim Fw').
exists (lim Fw'').
split.
assert (HG : lim Fw' = proj G (lim F)).
apply @filterlim_locally_unique with (F:=F)
        (f := fun x => proj G x).
now apply Proper_StrongProper.
unfold filterlim, filter_le, filtermap.
intros P HlP.
unfold locally in HlP.
destruct HlP as (e,HlP).
assert (HW'c : cauchy Fw').
unfold Fw'.
apply cauchy_proj; try assumption.
unfold cauchy in cF.
specialize (cF e).
destruct cF as (x,cF).
apply filter_imp with (fun x0 => Hierarchy.ball (lim Fw') e (proj G x0)).
intros x0 HA.
specialize (HlP (proj G x0)).
now apply HlP.
generalize (@complete_cauchy _ Fw' Fw'PF HW'c) => Hgw'.
unfold Fw' at 1 in Hgw'.
unfold clean_proj at 1 in Hgw'.
unfold filtermap in Hgw'.
specialize (Hgw' e).
trivial.
unfold filterlim, filter_le, filtermap.
intros P HlP.
unfold locally in HlP.
destruct HlP as (e,HlP).
apply filter_imp with (fun x0 => Hierarchy.ball (proj G (lim F)) e (proj G x0)).
intros x0 HA.
specialize (HlP (proj G x0)).
now apply HlP.
generalize (@complete_cauchy _ F PF cF) => Hg.
assert (H2p : 0 < e / 2).
apply Rlt_div_r.
intuition.
ring_simplify.
apply e.
specialize (Hg (mkposreal (e/2) H2p)).
apply filter_imp with (Hierarchy.ball (Hierarchy.lim F) (e/2)).
intros x HX.
apply proj_dist.
unfold Hierarchy.ball.
simpl.
unfold ball; simpl.
unfold Hierarchy.ball in HX.
simpl in HX.
unfold ball in HX.
simpl in HX.
apply Rlt_trans with (e/2).
trivial.
apply Rlt_div_l.
intuition.
destruct e as (e,He).
simpl in *.
replace e with (e*1) at 1 by field.
apply Rmult_lt_compat_l.
apply He.
intuition.
trivial.
rewrite HG.
apply projG.
split.
assert (cF'' : cauchy Fw'').
apply cauchy_proj'.
trivial. trivial.
generalize (@complete_cauchy _ Fw'' Fw''PF cF'') => Hgw''.
generalize (span_closed u) => Hj.
unfold my_complete in Hj.
assert (H2 : forall P : E -> Prop,
    F P ->
    (exists x : E, P x /\
     (exists g w : E, G g /\ span u w /\ x = plus g w))).
intros P HP.
apply NNPP.
now apply H.
assert (H3 : forall P, Fw'' P -> exists x : E, P x /\ span u x).
intros V HV.
unfold Fw'' in HV.
unfold clean_proj' in HV.
unfold filtermap in HV.
apply H2 in HV.
destruct HV as (x,HV).
exists (proj' G x).
split.
intuition.
unfold proj'.
destruct HV as (HV1,(g,(w,(HV2,((l,HV3),HV4))))).
rewrite HV4.
generalize (@lin_proj) => LP.
destruct LP as (LP1,LP2).
rewrite (LP1 g w).
rewrite PGuisu; try easy.
unfold minus.
rewrite opp_plus.
rewrite plus_assoc_gen.
rewrite plus_opp_r.
rewrite plus_zero_l.
exists l.
replace (opp (proj G w)) with (@zero E).
now rewrite plus_zero_r.
replace (@zero E) with (opp (opp (@zero E))).
assert (HO : opp zero = proj G w).
rewrite opp_zero.
rewrite HV3.
generalize lin_proj => Hl.
destruct Hl as (_,Hl).
specialize (Hl u l).
rewrite Hl.
rewrite PGorth_compl.
rewrite scal_zero_r.
reflexivity.
trivial.
rewrite HO.
reflexivity.
rewrite opp_opp; reflexivity.
apply Hj.
trivial.
trivial.
intros P HOP.
intro S; apply S.
specialize (H3 _ HOP).
intuition.
apply ball_eq.
intros e.
assert (cF' : cauchy Fw').
apply cauchy_proj.
trivial.
trivial.
assert (cF'' : cauchy Fw'').
apply cauchy_proj'.
trivial.
trivial.
generalize (@complete_cauchy _ Fw' Fw'PF cF') => Hgw'.
generalize (@complete_cauchy _ Fw'' Fw''PF cF'') => Hgw''.
generalize (@complete_cauchy _ F PF cF) => Hg.
assert (h2 : 0 < e/2).
apply Rlt_div_r.
intuition.
ring_simplify.
apply e.
specialize (Hg (mkposreal (e/2) h2)).
assert (H4p : 0 < e/4).
apply Rlt_div_r.
apply Rlt_trans with 3.
apply Rlt_trans with 2.
intuition.
intuition.
replace 3 with (2 + 1) by ring.
replace 4 with (3 + 1) by ring.
apply Rplus_lt_le_compat.
intuition.
intuition.
ring_simplify.
apply e.
specialize (Hgw' (mkposreal (e/4) H4p)).
specialize (Hgw'' (mkposreal (e/4) H4p)).
unfold Fw' at 1 in Hgw'.
unfold clean_proj in Hgw'.
unfold Fw'' at 1 in Hgw''.
unfold clean_proj' in Hgw''.
unfold filtermap in Hgw', Hgw''.
assert (H2 : forall P : E -> Prop,
    F P ->
    (exists x : E, P x /\
     (exists g w : E, G g /\
                   span u w /\ x = plus g w))).
intros P HP.
apply NNPP.
now apply H.
simpl in Hgw', Hgw''.
specialize (H2 (fun x : E => (Hierarchy.ball (Hierarchy.lim Fw') (e/4) (proj G x) /\
            Hierarchy.ball (Hierarchy.lim Fw'') (e/4) (proj' G x)) /\
            Hierarchy.ball (Hierarchy.lim F) (e/2) x)).
assert (Hand : F
       (fun x : E =>
        (Hierarchy.ball (Hierarchy.lim Fw') (e/4) (proj G x) /\
         Hierarchy.ball (Hierarchy.lim Fw'') (e/4) (proj' G x)) /\
         Hierarchy.ball (Hierarchy.lim F) (e/2) x)).
apply filter_and.
now apply filter_and.
trivial.
specialize (H2 Hand).
destruct H2 as (x2,(H21,(g2,(w2,(H22,(H23,H24)))))).
clear Hand.
unfold Hierarchy.ball in H21; simpl in H21.
unfold ball in H21; simpl in H21.
destruct H21 as ((Hn1,Hn2),Hn3).
unfold Hierarchy.ball; simpl.
unfold ball; simpl.
assert (Hss : minus (lim F) (plus (lim Fw') (lim Fw'')) =
         (plus (minus (lim F) x2) (minus x2 (plus (lim Fw') (lim Fw''))))).
unfold minus.
rewrite (Hierarchy.plus_comm (lim F) (opp x2)).
rewrite plus_assoc_gen.
rewrite plus_opp_l.
rewrite plus_zero_l.
reflexivity.
rewrite Hss.
apply Rle_lt_trans with (plus (Hnorm (minus (lim F) x2))
                    (Hnorm (minus x2 (plus (lim Fw') (lim Fw''))))).
apply: norm_triangle.
destruct e as (e,He).
simpl.
replace e with ((e/2)+(e/2)) by field.
simpl in *.
apply Rplus_lt_compat.
trivial.
assert (Hx : plus (Hnorm (minus (Hierarchy.lim Fw') (proj G x2)))
                  (Hnorm (minus (Hierarchy.lim Fw'') (proj' G x2))) < e / 2).
replace (e/2) with ((e/4) + (e/4)) by field.
now apply Rplus_lt_compat.
rewrite norm_minus_sym.
replace (Hnorm (minus (plus (lim Fw') (lim Fw'')) x2)) with
        (Hnorm (minus (plus (lim Fw') (lim Fw''))
               (plus (proj G x2) (proj' G x2)))).
unfold minus.
unfold minus in Hx.
rewrite opp_plus.
rewrite plus_assoc_gen.
apply Rle_lt_trans with (plus (Hnorm (plus (Hierarchy.lim Fw')
                (opp (proj G x2))))
       (Hnorm (plus (Hierarchy.lim Fw'') (opp (proj' G x2))))).
apply: norm_triangle.
trivial.
rewrite PFsum.
reflexivity.
Qed.

End FDIM_sum.

(** Finite dim subspace is the sum of linear span and finite dim *)

Section FDIM_closed.

Context {E : Hilbert}.

Definition B_ortho (B : nat -> E) := forall (i : nat), Hnorm (B i) = 1
                     /\ (forall i j, i <> j ->
                        (inner (B i) (B j)) = 0).

Lemma dim_f_span_sum : forall (d: nat) (B : nat -> E), (0 < d)%nat ->
           B_ortho B -> forall Phi : E -> Prop,
           (phi_FDIM Phi (S d) B) <->
           (exists phi_m, phi_FDIM phi_m d B /\
             orth_compl phi_m (B (S (d-1))) /\
             (forall x:E, Phi x  <->
            (exists a s, span (B (S (d -1))) s /\ phi_m a /\ x = plus s a))).
Proof.
intros d B dpos B_ortho Phi.
split.
intros Hphin.
unfold phi_FDIM in *.
destruct (eq_nat_dec (S d) 0).
exfalso.
intuition.
destruct (eq_nat_dec d 0).
exfalso; auto with zarith.
exists (fun r : E =>
       (exists L : nat -> R, r = sum_n (fun n : nat => scal (L n) (B n)) (d-1))).
split.
unfold phi_FDIM.
intros u0; reflexivity.
split.
unfold orth_compl.
intros y Hy.
destruct Hy as (L,Hy).
rewrite Hy.
rewrite inner_sym.
rewrite inner_sum_n.
replace 0 with (sum_n (fun n : nat => 0) (d-1)).
apply sum_n_ext_loc.
intros m Hm.
rewrite inner_scal_l.
destruct B_ortho with m.
specialize (H0 m (S (d-1))).
assert (H0' : m <> S (d-1)).
auto with zarith.
specialize (H0 H0').
rewrite H0.
ring_simplify.
reflexivity.
unfold sum_n.
rewrite sum_n_m_const_zero.
reflexivity.
intros x.
split.
intros Hx.
specialize (Hphin x).
apply Hphin in Hx.
destruct Hx as (L,Hx).
exists (sum_n (fun n : nat => scal (L n) (B n)) (d-1)).
exists (scal (L (S d -1)%nat) (B (S d -1)%nat)).
split.
unfold span.
exists (L (S (d - 1))).
replace (S d -1)%nat with (S (d -1)) by auto with zarith.
reflexivity.
split.
exists L; reflexivity.
rewrite Hx.
replace (S d -1)%nat with (S (d-1))%nat by auto with zarith.
rewrite sum_Sn.
rewrite Hierarchy.plus_comm.
reflexivity.
intros Has.
specialize (Hphin x).
apply Hphin.
destruct Has as (a,(s,(Ha1,(Ha2,Ha3)))).
destruct Ha2 as (L,Ha2).
unfold span in Ha1.
destruct Ha1 as (l,Ha1).
exists (fun n : nat => match le_gt_dec n (d-1) with
               | left _ => L n
               | right _ => l end).
rewrite Ha3.
rewrite Ha2.
rewrite Ha1.
replace (S d -1)%nat with (S (d -1)%nat) by auto with zarith.
rewrite sum_Sn.
destruct (le_gt_dec (S d) d).
exfalso; intuition.
rewrite Hierarchy.plus_comm.
f_equal.
apply sum_n_ext_loc.
intros m Hm.
destruct (le_gt_dec m (d-1)).
reflexivity.
exfalso; intuition.
destruct (le_gt_dec (S (d -1)) (d-1)).
exfalso; auto with zarith.
reflexivity.
intros Hh.
destruct Hh as (phi_m,(K1,(K3,K2))).
unfold phi_FDIM in *.
intros x.
split.
intros Px.
specialize (K2 x).
apply K2 in Px.
destruct Px as (a,HPx).
destruct HPx as (s,(P1,(P2,P3))).
destruct (eq_nat_dec d 0).
exfalso; auto with zarith.
specialize (K1 a).
apply K1 in P2.
destruct P2 as (L,P2).
unfold span in P1.
destruct P1 as (l,P1).
exists (fun n : nat => match le_gt_dec n (d-1) with
               | left _ => L n
               | right _ => l end).
rewrite P3 P2 P1.
replace (S d -1)%nat with (S (d-1)) by auto with zarith.
rewrite sum_Sn.
rewrite Hierarchy.plus_comm.
f_equal.
apply sum_n_ext_loc.
intros m Hm.
destruct (le_gt_dec m (d-1)).
reflexivity.
exfalso; intuition.
destruct (le_gt_dec (S (d-1)) (d-1)).
exfalso; intuition.
reflexivity.
intros H.
specialize (K2 x).
apply K2.
destruct H as (L,H).
exists (sum_n (fun n : nat => scal (L n) (B n)) (d-1)).
exists (scal (L (S (d-1))) (B (S (d-1)))).
split.
unfold span.
exists (L (S (d-1))).
reflexivity.
split.
destruct (eq_nat_dec d 0).
exfalso; auto with zarith.
specialize (K1 ((sum_n (fun n : nat => scal (L n) (B n)) (d-1)))).
apply K1.
exists L.
reflexivity.
rewrite H.
replace (S d -1)%nat with (S (d-1)) by auto with zarith.
rewrite sum_Sn.
rewrite Hierarchy.plus_comm.
reflexivity.
Qed.

(** * Finite subspace is ModuleSpace-compatible *)

Lemma FDIM_comp_m : forall (d:nat) (phi : E -> Prop) (b : nat -> E),
                phi_FDIM phi d b -> compatible_m phi.
Proof.
intros dim phi b phi_EV.
unfold phi_FDIM in phi_EV.
destruct (eq_nat_dec dim 0).
split.
split.
intros x y Hx Hy.
apply phi_EV in Hx.
apply phi_EV in Hy.
rewrite Hx Hy.
rewrite plus_zero_l.
rewrite opp_zero.
apply phi_EV.
reflexivity.
exists zero.
apply phi_EV; reflexivity.
intros x l Hl.
apply phi_EV in Hl.
rewrite Hl.
rewrite scal_zero_r.
apply phi_EV; reflexivity.
split.
split.
intros x y Hx Hy.
apply (phi_EV x) in Hx.
apply (phi_EV y) in Hy.
apply phi_EV.
destruct Hx as (Lx,Hx).
destruct Hy as (Ly,Hy).
exists (fun n: nat => minus (Lx n) (Ly n)).
rewrite Hx Hy.
unfold minus.
rewrite <- scal_opp_one.
rewrite <- sum_n_scal_l.
rewrite <- sum_n_plus.
f_equal.
apply functional_extensionality.
intros m.
rewrite scal_distr_r.
rewrite scal_opp_one.
rewrite scal_opp_l.
reflexivity.
exists zero.
apply phi_EV.
exists (fun n => zero).
transitivity (sum_n
             (fun n : nat => (@zero E)) (dim-1)).
unfold sum_n.
rewrite sum_n_m_const_zero.
reflexivity.
apply sum_n_ext_loc.
intros m Hm.
rewrite scal_zero_l.
reflexivity.
intros x l Hx.
apply phi_EV.
apply (phi_EV x) in Hx.
destruct Hx as (L,Hx).
exists (fun n : nat => scal l (L n)).
rewrite Hx.
rewrite <- sum_n_scal_l.
apply sum_n_ext_loc.
intros m Hm.
rewrite scal_assoc.
reflexivity.
Qed.

(** * Finite dim subspace is closed *)

Lemma FDIM_closed : forall (d : nat) (B : nat -> E),
                    forall Phi : E -> Prop,
                   phi_FDIM Phi d B -> B_ortho B -> my_complete Phi.
Proof.
induction d.
intros B Phi H B_ortho.
assert (Heq : forall u:E, Phi u <-> span zero u).
intros u.
split.
intros Hphi.
exists 0.
rewrite scal_zero_l.
unfold phi_FDIM in H.
apply (H u) in Hphi.
trivial.
intros Hss.
unfold phi_FDIM in H.
destruct (eq_nat_dec 0 0).
apply H.
destruct Hss as (l,Hl).
rewrite scal_zero_r in Hl.
rewrite Hl.
reflexivity.
exfalso; auto with zarith.
intros F PF cF HH.
apply Heq.
assert (Heq' : (forall P0 : E -> Prop,
           F P0 -> ~ ~ (exists x : E, P0 x /\ Phi x))
             -> (forall K : E -> Prop,
           F K -> ~ ~ (exists x : E, K x /\ span zero x))).
intros H1 Q HQ.
intro HF.
specialize (HH Q HQ).
apply HH.
intro HF2.
destruct HF2 as (w,(W1,W2)).
apply HF.
exists w.
split; try assumption.
now apply Heq.
assert (HH2 : forall K : E -> Prop,
        F K -> ~ ~ (exists x : E, K x /\ span zero x)).
now apply Heq'.
generalize HH2.
generalize F PF cF.
assert (my_complete ((@span E) zero)).
apply span_closed.
trivial.
intros B Phi HS B_ortho.
assert (P := HS).
destruct (eq_nat_dec d 0).
unfold phi_FDIM in HS.
destruct (eq_nat_dec (S d) 0).
exfalso; auto with zarith.
rewrite e in HS.
simpl in HS.
assert (HS' : forall u : E,
     Phi u <-> span (B O) u).
intros u.
split.
intros Hph.
apply HS in Hph.
destruct Hph as (L,Hph).
rewrite sum_O in Hph.
now exists (L 0%nat).
intros Hsp.
apply HS.
destruct Hsp as (l,Hsp).
exists (fun n => l).
now rewrite sum_O.
generalize (@span_closed E (B 0%nat)) => SC.
intros F PF cF HF.
apply HS'.
apply SC; try easy.
intros V HV.
intro VF.
specialize (HF V HV).
apply HF.
intros (f,GF).
apply VF.
exists f.
split; try easy.
apply HS'.
easy.
apply dim_f_span_sum in P.
destruct P as (phi_m,(P1,(P0,P2))).
assert (P3 : forall x : E, Phi x <->
       (exists a s : E, phi_m a /\ span (B (S (d-1))) s /\ x = plus a s)).
intros z.
specialize (P2 z).
split.
intros Hp.
apply P2 in Hp.
destruct Hp as (a,(s,(hp1,(hp2,hp3)))).
exists a, s.
split; try assumption.
split; try assumption.
now rewrite Hierarchy.plus_comm.
intros Hex.
destruct Hex as (a,(s,(hp1,(hp2,hp3)))).
apply P2.
exists a, s.
split; try assumption.
split; try assumption.
now rewrite Hierarchy.plus_comm.
assert (PP : my_complete Phi <-> my_complete (fun x => exists a s : E, phi_m a
               /\ span (B (S (d-1))) s
           /\ x = plus a s)).
split.
intros Hmcp.
unfold my_complete in Hmcp.
unfold my_complete.
intros F PF cF HF.
specialize (Hmcp F PF cF).
rewrite <- P3.
apply Hmcp.
intros P FP.
specialize (HF P FP).
intro.
apply HF.
intro.
apply H.
destruct H0 as (x,H0).
exists x.
split.
intuition.
destruct H0 as (H01,H02).
rewrite P3.
trivial.
intros Hcls.
unfold my_complete.
intros F PF cF HF.
specialize (Hcls F PF cF).
rewrite P3.
apply Hcls.
intros P FP.
specialize (HF P FP).
intro.
apply HF.
intro.
apply H.
destruct H0 as (x,H0).
exists x.
split.
intuition.
destruct H0 as (H01,H02).
rewrite <- P3.
trivial.
apply PP.
apply sum_span_cl_cl; trivial.
apply IHd with B; trivial.
apply FDIM_comp_m with d B; trivial.
auto with zarith.
trivial.
Qed.

End FDIM_closed.
