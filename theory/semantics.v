Require Import util syntax.

(* Based directly on oopsla 2013 paper *)

Inductive any_interleave : list memop → list (list memop) → Prop :=
  | noops : ∀ xs, (∀ x, x ∈ xs → x = []) → any_interleave [] xs
  | oneop : ∀ x xs ys zs t, any_interleave t (ys ++ xs :: zs) → 
                            any_interleave (x::t) (ys ++ (x::xs) :: zs).

Fixpoint apply (E : list memop) (S : Map l v) : Map l v := S. 


(* TODO implement interleaves and apply *)
Definition valid_interleave (S : Map l v) (C : list l) (E' : list memop) 
                            (es : list (list memop)) : Prop := 
  any_interleave E' es ∧ 
  ∀ l, lookup l (apply E' S) = lookup l (apply (concat es) S).
Definition domain {A B} := @map (A * B) A fst.

Reserved Notation " input ↦ output " (at level 50).
Inductive eval: Map r ρ 
              * Map var v
              * Map l T
              * Map l v
              * list l 
              * e 
              → v * list memop
              → Prop := 
  | ERead1 : ∀ M L H S C e l E v,
    (M, L, H, S, C, e) ↦ (vl l, E) →
    l ∉ C → 
    lookup l (apply E S) = Some v → 
    (M, L, H, S, C, read e) ↦ (v, E ++ [mread l v])
  | ERead2 : ∀ M L H S C e l E v,
    (M, L, H, S, C, e) ↦ (vl l, E) →
    l ∉ C → 
    (M, L, H, S, C, read e) ↦ (v, E ++ [mread l v]) 
  | EWrite : ∀ M L H S S' C e1 e2 l E1 E2 E v,
    (M, L, H, S, C, e1) ↦ (vl l, E1) →
    (M, L, H, S', C, e2) ↦ (v, E2) →
    valid_interleave S C E [E1; E2] →
    (M, L, H, S', C, write e1 e2) ↦ (vl l, E ++ [mwrite l v])
  | ENew : ∀ M L H S C t l r, 
    l ∈ lu r M →
    l ∉ domain S →
    (M, L, H, S, C, new t r) ↦ (vl l, [])
  | EUpRgn : ∀ M L H S C e v E rs,
    (M, L, H, S, C, e) ↦ (v, E) →
    (M, L, H, S, C, upr e rs) ↦ (v, E)
  | EDnRgn1 : ∀ M L H S C e E rs r l,
    (M, L, H, S, C, e) ↦ (vl l, E) →
    r ∈ rs →
    l ∈ lu r M → 
    (M, L, H, S, C, downr e rs) ↦ (vl l, E)
  | EDnRgn2 : ∀ M L H S C e E rs l,
    (M, L, H, S, C, e) ↦ (vl l, E) →
    (∀ r, r ∈ rs → l ∉ lu r M) →
    (M, L, H, S, C, downr e rs) ↦ (vnull, E)
  | ENewColor : ∀ M L H S C K r, 
    (∀ i iv, (i, iv) ∈ K → i ∈ (lu r M)) →
    (M, L, H, S, C, newcolor r) ↦ (vcoloring K, [])
  | EColor : ∀ M L H S C K E1 E2 E3 E l e1 e2 e3 v, 
    (M, L, H, S, C, e1) ↦ (vcoloring K, E1) → 
    (M, L, H, apply E1 S, C, e2) ↦ (vl l, E2) → 
    (M, L, H, apply E2 (apply E1 S), C, e3) ↦ (viv v, E3) → 
    valid_interleave S C E [E1; E2; E3] →
    (M, L, H, S, C, color e1 e2 e3) ↦ (vcoloring ((l,v)::K), E) 
	| EPartition : ∀ M M' L H S C rs rp ρs e1 e2 K E' E1 E2 v, 
    (M, L, H, S, C, e1) ↦ (vcoloring K, E1) → 
    ρs = map (map fst) (groupBy (λ x y, beq_nat (snd x) (snd y)) K) →
    M' = zip rs ρs ++ M →  
    (M', L, H, S, C, e2) ↦ (v, E2) →
    valid_interleave S C E' [E1; E2] →
    (M, L, H, S, C, partition rp e1 rs e2) ↦ (v, E')  
  | EPack : ∀ M L H S C e1 v E E' ρs rs v' T,
    (M, L, H, S, C, e1) ↦ (v, E') →
    ρs = map (λ r, lu r M) rs →
    v' = vreg_rel ρs v →
    (M, L, H, S, C, pack e1 T rs) ↦ (v', E)
  | EUnpack : ∀ M L H S C e1 ρs E1 M' rs L' id v1 S' v2 e2 E' T1, 
    (M, L, H, S, C, e1) ↦ (vreg_rel ρs v1, E') →
    M' = zip rs ρs →  
    S' = apply E1 S →
    L' = (id, v1)::L →
    (M', L', H, S, C, unpack e1 id T1 rs e2) ↦ (v2, E') 
  | ECall : ∀ M L H S C es vs Es xs id rs En1 E'' E' M' L' S' C' t ts rs' e Phi Q v, 
    (∀ e v E, In (e, (v, E)) (zip es (zip vs Es)) → (M, L, H, S, C, e) ↦ (v, E)) →
    valid_interleave S C E' Es →
    M' = zip rs' (map (λ r, lu r M) rs) →  
    L' = zip xs vs →
    S' = apply E' S → 
    function id rs xs ts Phi Q t e →
    (M', L', H, S', C', e) ↦ (v, En1) → 
    valid_interleave S C E'' [E'; En1] →
    (M, L, H, S, C, call id rs es) ↦ (v, E'')
  | ELet : ∀ M L H S C e b id v E v' E' t S', 
    (M, L, H, S, C, e) ↦ (v, E) →
    S' = apply E S →
    (M, (id, v) :: L, H, S, C, b) ↦ (v', E')  →
    (M, L, H, S, C, elet id t e b) ↦ (v', E')
  | EId : ∀ M L H S C x v,
    lookup x L = Some v → 
    (M, L, H, S, C, id x) ↦ (v, [])
where " input ↦ output " := (eval input output).

