Require Export Unicode.Utf8.
Require Export JRWTactics.
Require Export List Init.Datatypes.
Export ListNotations.
Open Scope program_scope.

Require Export EqNat Arith.Peano_dec Program.Basics.

Definition all := fold_right andb true.

Fixpoint zipWith {a b c} (f : a → b → (c a b)) (xs : list a) (ys : list b) : list (c a b) := 
  match xs, ys with
  | [], _ => []
  | _, [] => []
  | x::xs, y::ys => f x y::zipWith f xs ys
  end.

Definition zip {a b} := @zipWith a b _ pair. 

Fixpoint tails {a} (l : list a) : list (list a) := match l with
  | [] => []
  | x::xs => (x::xs) :: tails xs
  end.

Fixpoint contains {a} (eq : a → a → bool) (y : a) (xs : list a) := 
  match xs with 
  | [] => false
  | x::xs => if eq x y then true else contains eq y xs
  end.


Fixpoint groupBy {a} (f : a → a → bool) (xs : list a) := match xs with  
  | [] => []
  | x::xs => (x::filter (f x) xs) :: filter (negb ∘ contains f x) (groupBy f xs)
  end.
  
Definition Map a b := list (prod a b).

Definition lookup {a} (x:nat) (l:Map nat a) : option a := 
  match find (λ p, beq_nat x (fst p)) l with 
    | None => None
    | Some (k,v) => Some v
  end.

Lemma lookup_cons : ∀ {a} (x:nat) (l:Map nat a) (v:a), lookup x ((x,v)::l) = Some v.
intros. unfold lookup. unfold find. simpl. rewrite <- beq_nat_refl. reflexivity.
Qed. 

Notation " x ∈ y " := (In x y) (at level 30).
Notation " x ∉ y " := (¬ In x y) (at level 30).

Definition subset {a} xs ys := ∀ x:a, In x xs → In x ys.
Notation " x ⊆ y " := (subset x y) (at level 50).

Lemma subset_nil_nil {a} : ∀ xs:list a, xs ⊆ [] → xs = [].
intros. unfold subset in H. simpl in H. destruct xs. auto. assert False.
apply H with (x:=a0). simpl. apply or_introl. auto. inversion H0. Qed.

Lemma subset_refl {a} : ∀ xs:list a, subset xs xs. intros. unfold subset;
intros. assumption. Qed. 

Lemma subset_trans {a} : ∀ xs ys zs : list a, xs ⊆ ys → ys ⊆ zs → xs ⊆ zs.
intros. unfold subset. intros. apply H in H1. apply H0. assumption. Qed. 

Lemma contains_beq_nat_in : ∀ x xs, contains beq_nat x xs = true ↔ x ∈ xs.
intros; split; intros. induction xs. simpl in H. inversion H. simpl. simpl in
H. destruct (PeanoNat.Nat.eqb a x) eqn:ax. apply beq_nat_true in ax. subst.
apply or_introl.  reflexivity. apply or_intror. apply IHxs. assumption.
induction xs. inversion H. destruct H . subst. simpl. rewrite <- beq_nat_refl.
reflexivity. apply IHxs in H. simpl. rewrite H. destruct (beq_nat a x); auto.
Qed.  

Lemma contains_beq_nat_not_in : ∀ x xs, contains beq_nat x xs = false ↔ x ∉ xs.
intros; split; intros. induction xs. auto. simpl in H. destruct
(PeanoNat.Nat.eqb a x) eqn:ax. inversion H. apply beq_nat_false in ax. unfold
not. intros. destruct H0. subst. apply ax. reflexivity. apply IHxs in H. apply
H. assumption. induction xs; intros. auto. simpl. destruct (beq_nat a x) eqn:ax.
simpl in H.  assert False. apply H. apply or_introl. apply beq_nat_true in ax.
assumption. inversion H0. apply IHxs. unfold not. intros. unfold not in H.
apply H. simpl. apply or_intror. assumption. Qed.

Fixpoint intersection (xs ys : list nat) : list nat := match xs with
  | [] => []
  | x::xs => (if contains beq_nat x ys then cons x else id) (intersection xs ys)
  end.

Notation " x ∩ y " := (intersection x y) (at level 50).

Lemma intersection_in : ∀ x xs ys, x ∈ (xs ∩ ys) ↔ x ∈ xs ∧ x ∈ ys.
intros. split; intros. induction xs; intros. inversion
H. simpl in H.  destruct (contains PeanoNat.Nat.eqb a ys) eqn:cays. simpl in H. destruct H. subst. 
rewrite contains_beq_nat_in in cays. split. simpl. apply or_introl. reflexivity. assumption. apply IHxs in H. 
destruct H. split. apply or_intror. assumption. assumption. rewrite contains_beq_nat_not_in in cays. apply IHxs in H. 
destruct H. split. apply or_intror. assumption. assumption. induction xs. simpl. destruct H. inversion H. simpl. simpl. 
destruct (contains beq_nat a ys) eqn:cays. simpl. destruct H. rewrite contains_beq_nat_in in cays. simpl in H. destruct H. 
subst. apply or_introl. reflexivity. apply or_intror. apply IHxs. split; assumption. apply IHxs. destruct H. 
rewrite contains_beq_nat_not_in in cays. destruct H. subst. apply cays in H0. inversion H0. split; assumption. Qed. 

Definition seteq {a} (xs ys : list a) := subset xs ys /\ subset ys xs. 

Lemma intersection_comm : forall xs ys, subset (intersection xs ys) (intersection ys xs).
intros. unfold subset; intros. rewrite intersection_in. rewrite intersection_in in H. 
destruct H. split; auto. Qed. 

Lemma subset_intersection : ∀ xs ys zs, xs ⊆ ys → (xs ∩ zs) ⊆ (ys ∩ zs).
intros. unfold subset. intros. rewrite intersection_in. rewrite intersection_in in H0. 
destruct H0. apply H in H0. split; auto. Qed.

Fixpoint inits {a} (xs : list a) : list (list a) := match xs with
  | [] => []
  | x::xs => [x] :: map (cons x) (inits xs)
  end.

Definition lu {a} (x:nat) (l:Map nat (list a)) : list a := 
  match lookup x l with 
    | None => []
    | Some l => l
  end.

