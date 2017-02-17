Require Import util.  
(* Syntax *)
Definition r := nat. (* Logical region *)
Definition l := nat. (* Location (pointer) *)
Definition Color := nat.
Definition set := list. (* We use lists for sets *)
Definition ρ := set l. (* Physical region, which is a set of  *)
Definition var := nat.
Definition M := Map r ρ.
Set Boolean Equality Schemes.

(* Constraints *)
Inductive ω := 
  | subr : r → r → ω 
  | disj : r → r → ω.
Definition Ω := set ω.


(* Privileges *)
Inductive φ := 
  | reads : r → φ 
  | writes : r → φ 
  | reduces : var → r → φ.
Definition Φ := set φ.


(* Coherence modes *)
Inductive q := 
  | atomic : r → q  
  | simult : r → q.
Definition Q := set q.

(* Closures mode *) 

Inductive T := 
  | tbool 
  | tint
  | ttuple : list T → T
  | pointer : T → list r → T
  | coloring : r → T
  | reg_rel : list r → T → Ω → T
  | tfunction : list T → Φ → Q → T.

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
  | eindex : e → nat → e
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

(* Inductive definition for what functions are defined, default to any *)
Inductive function : var → list r → list var → list T → Φ → Q → T → e → Prop := 
  | mkfunction : ∀ id rs xs Ts T Phi Q e, function id rs xs Ts T Phi Q e.

Inductive memop := 
  | mread : l → memop
  | mwrite : l → v → memop
  | mreduce : l → var → v → memop.
