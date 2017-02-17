Require Import util syntax.
Require Import Strings.String.
Open Scope type_scope.
Open Scope string_scope.

(*
Inductive T := 
  | tbool 
  | tint
  | ttuple : list T → T
  | pointer : T → list r → T
  | coloring : r → T
  | reg_rel : list r → T → Ω → T
  | tfunction : list T → Φ → Q → T.
*)

Definition Γ := Map var T.

Fixpoint typecheck (env : (Γ * Φ * Ω)) (e : e) : T + string := let '(Γ, Φ, Ω) := env in 
  match e with
  | read e => match typecheck env e with 
    | inl (pointer t rs) => if forallb (λ r, existsb (φ_beq (reads r)) Φ) rs
        then inl t
        else inr "don't have read permission"
    | inl _ => inr "expected pointer type"
    | inr x => inr x
    end
  | write e₁ e₂ => match typecheck env e₁ with
    | inl (pointer t rs) => if forallb (λ r, existsb (φ_beq (writes r)) Φ) rs
        then match typecheck env e₂ with
          | inl t' => if T_beq t t' then inl t else inr "mismatched types for write"
          | inr e => inr e
          end
        else inr "don't have write permission"
    | inl _ => inr "expected pointer type"
    | inr x => inr x
    end
  | _ => inr "unimplemented"
  end.
  
Reserved Notation " xs ⊢ e :: T " (at level 50). 
