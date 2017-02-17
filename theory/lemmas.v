Require Import util syntax.  

(* Read ω ∈* Ω as ω ∈ Ω* *)
Reserved Notation " ω ∈* Ω " (at level 40).
Inductive cclo (Ω : Ω) : ω → Prop := 
  | trivial : ∀ ω, ω ∈ Ω → ω ∈* Ω
  | sub_refl : ∀ r, subr r r ∈* Ω
  | sub_trans : ∀ ri rj rk, subr ri rj ∈* Ω → subr rj rk ∈* Ω  → 
                                  subr ri rk ∈* Ω 
  | dis_sub : ∀ ri rj rk, subr ri rj ∈* Ω → disj rj rk ∈*  Ω → 
                                  disj ri rk ∈* Ω
  | dis_comm : ∀ ri rj, disj ri rj ∈* Ω → disj rj ri ∈* Ω 
where " ω ∈* Ω " := (cclo Ω ω).

Definition resp (M : M) (elem : Ω → ω → Prop) (Ω : Ω) :=
  (∀ r1 r2, elem Ω (subr r1 r2) → lu r1 M ⊆ lu r2 M)
                              ∧ 
  (∀ r1 r2, elem Ω (disj r1 r2) → lu r1 M ∩ lu r2 M = [])
.

(* Read M ~* Ω as M ~ Ω* *)
Notation " M ~ Ω " := (resp M (λ Ω ω, In ω Ω) Ω) (at level 40).
Notation " M ~* Ω " := (resp M cclo Ω) (at level 40).

Lemma resp_clos_sub : ∀ r1 r2 Ω (M:M), (∀ r1 r2, subr r1 r2 ∈ Ω → lu r1 M ⊆ lu r2 M) → 
                                                 subr r1 r2 ∈* Ω → 
																								lu r1 M ⊆ lu r2 M.
intros. prep_induction H0. induction H0; intros; subst. apply H0. assumption.
inversion H2. subst. clear H2. apply subset_refl. inversion H2. subst. clear H2.
specialize (IHcclo2 _ _ _ H eq_refl).  specialize (IHcclo1 _ _ _ H eq_refl).
apply (subset_trans _ _ _ IHcclo1 IHcclo2). inversion H2. inversion H2. Qed.

(* Lemma 6 from the oopsla13 paper *)
Lemma resp_clos : ∀ M Ω, M ~ Ω ↔ M ~* Ω.
intros. split; intros; split; intros; destruct H. apply resp_clos_sub with
(Ω := Ω). assumption. assumption. prep_induction H0. induction
H0; intros; subst. apply H1. assumption. inversion H3. subst. inversion H3.
inversion H3. subst. clear H3.  specialize (IHcclo2 _ H H1 _ _ eq_refl). apply
resp_clos_sub with (M:=M) in H0_. apply subset_intersection with (zs:=lu r2
M) in H0_.  rewrite IHcclo2 in H0_. apply subset_nil_nil in H0_. assumption.
assumption. inversion H3. subst. clear H3. specialize (IHcclo _ H H1 _ _ eq_refl). 
apply subset_nil_nil. apply subset_trans with (ys:=lu r2 M ∩ lu r1 M). apply
intersection_comm. rewrite IHcclo. apply subset_refl. apply H. apply trivial.
assumption. apply H1. apply trivial. assumption. Qed.  

