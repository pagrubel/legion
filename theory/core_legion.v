Require Import EqNat Arith.Peano_dec Program.Basics.
Require Import Unicode.Utf8.
Require Import List.
Import ListNotations. 
Open Scope program_scope.

(* Based directly on oopsla 2013 paper *)

(* Syntax definitions *)
Definition r := nat. (* Logical region *)
Definition l := nat. (* Location (pointer) *)
Definition Color := nat.
Definition set := list. (* We use lists for sets *)
Definition ρ := set l. (* Physical region, which is a set of  *)
Definition var := nat.

Inductive constraint := 
  | subr : r → r → constraint
  | disjoint : r → r → constraint.

Inductive privilege := 
  | reads 
  | writes 
  | reduces.

Inductive coherence := 
  | exclusive 
  | atomic 
  | simult.

Inductive T := 
  | tbool 
  | tint
  | ttuple : list T → T
  | pointer : T → r → T
  | coloring : r → T
  | reg_rel (rs : list r) : T → list constraint → T
  | function : list r → list T → list privilege → list coherence → T.

Inductive v := 
  | vbv : bool → v  
  | viv : nat → v
  | vtuple : list v → v
  | vnull 
  | vl : nat → v
  | vcoloring : list (prod l nat) → v 
  | vreg_rel : list ρ → v → v.

Inductive e :=
  | bv : bool → e
  | iv : nat → e
  | etuple : list e → e
  | index : e → nat → e
  | id : var → e
  | new : T → r → e
  | null : T → r → e
  | isnull : e → e
  | upr : e → list r → e
  | downr : e → list r → e
  | read : e → e 
  | write : e → e → e
  | reduce : var → e → e
  | newcolor : r → e
  | color : e → e → e → e
  | add : e → e → e
  | lt : e → e → e
  | elet : var → T → e → e → e
  | eif : e → e → e → e
  | call : var → list r → list e → e
  | partition : r → e → list r → e → e
  | pack : e → T → list r → e
  | unpack : e → var → T → list r → e → e.

Inductive memop := 
  | mread : l → memop
  | mwrite : l → v → memop
  | mreduce : l → id → v → memop.

(* Utility definitions *) 
Fixpoint zip {a b} (xs : list a) (ys : list b) : list (prod a b) := 
  match xs, ys with
  | [], _ => []
  | _, [] => []
  | x::xs, y::ys => (x,y)::zip xs ys
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

Notation " x ∈ y " := (In x y) (at level 30).
Notation " x ∉ y " := (¬ In x y) (at level 30).

Fixpoint inits {a} (xs : list a) : list (list a) := match xs with
  | [] => []
  | x::xs => [x] :: map (cons x) (inits xs)
  end.

Definition lu {a} (x:nat) (l:Map nat (list a)) : list a := 
  match lookup x l with 
    | None => []
    | Some l => l
  end.

(* TODO implement interleaves and apply *)
Definition valid_interleave (S : Map l v) (C : list l) (E' : list memop) 
                             (es : list (list memop)) : Prop := True.
Fixpoint apply (E : list memop) (S : Map l v) : Map l v := S. 
Definition domain {A B} := @map (A * B) A fst.

Inductive eval: Map r ρ 
              → Map var v
              → Map l T
              → Map l v
              → list l 
              → e 
              → v * list memop
              → Prop := 
  | ERead1 : ∀ M L H S C e l E v,
    eval M L H S C e (vl l, E) →
    l ∉ C → 
    lookup l (apply E S) = Some v → 
    eval M L H S C (read e) (v, E ++ [mread l])
  | ERead2 : ∀ M L H S C e l E v,
    eval M L H S C e (vl l, E) →
    l ∉ C → 
    eval M L H S C (read e) (v, E ++ [mread l]) 
  | EWrite : ∀ M L H S S' C e1 e2 l E1 E2 E v,
    eval M L H S C e1 (vl l, E1) →
    eval M L H S' C e2 (v, E2) →
    valid_interleave S C E (E1::E2::[]) →
    eval M L H S' C (write e1 e2) (vl l, E ++ [mwrite l v])
  | ENew : ∀ M L H S C t l r, 
    l ∈ lu r M →
    l ∉ domain S →
    eval M L H S C (new t r) (vl l, [])
  | EUpRgn : ∀ M L H S C e v E rs,
    eval M L H S C e (v, E) →
    eval M L H S C (upr e rs) (v, E)
  | EDnRgn1 : ∀ M L H S C e E rs r l,
    eval M L H S C e (vl l, E) →
    r ∈ rs →
    l ∈ lu r M → 
    eval M L H S C (downr e rs) (vl l, E)
  | EDnRgn2 : ∀ M L H S C e E rs l,
    eval M L H S C e (vl l, E) →
    (∀ r, r ∈ rs → l ∉ lu r M) →
    eval M L H S C (downr e rs) (vnull, E)
  | ENewColor : ∀ M L H S C K r, 
    (∀ i iv, (i, iv) ∈ K → i ∈ (lu r M)) →
    eval M L H S C (newcolor r) (vcoloring K, [])
  | EColor : ∀ M L H S C K E1 E2 E3 E l e1 e2 e3 v, 
    eval M L H S C e1 (vcoloring K, E1) → 
    eval M L H (apply E1 S) C e2 (vl l, E2) → 
    eval M L H (apply E2 (apply E1 S)) C e3 (viv v, E3) → 
    valid_interleave S C E (E1::E2::E3::[]) →
    eval M L H S C (color e1 e2 e3) (vcoloring ((l,v)::K), E) 
	| EPartition : ∀ M M' L H S C rs rp ρs e1 e2 K E' E1 E2 v, 
    eval M L H S C e1 (vcoloring K, E1) → 
    ρs = map (map fst) (groupBy (λ x y, beq_nat (snd x) (snd y)) K) →
    M' = zip rs ρs ++ M →  
    eval M' L H S C e2 (v, E2) →
    valid_interleave S C E' (E1 :: E2 :: []) →
    eval M L H S C (partition rp e1 rs e2) (v, E')  
  | EPack : ∀ M L H S C e1 v E E' ρs rs v' T,
    eval M L H S C e1 (v, E') →
    ρs = map (λ r, lu r M) rs →
    v' = vreg_rel ρs v →
    eval M L H S C (pack e1 T rs) (v', E)
  | EUnpack : ∀ M L H S C e1 ρs E1 M' rs L' id v1 S' v2 e2 E' T1, 
    eval M L H S C e1 (vreg_rel ρs v1, E') →
    M' = zip rs ρs →  
    S' = apply E1 S →
    L' = (id, v1)::L →
    eval M' L' H S C (unpack e1 id T1 rs e2) (v2, E') 
.

