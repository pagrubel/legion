Require Import Unicode.Utf8.
Require Import syntax semantics util.
Require Import List.
Import ListNotations.

Definition read_write x y t T r :=
  elet x t (read (id y)) 
    (write (new T r) (id x)).

Lemma read_write_ordering : ∀ x y l t T r v l',
  ([(r, [l'])], [(y, vl l)], [], [(l,v)], [], new T r) ↦ (vl l', []) →
  ([(r, [l'])], [(y, vl l)], [], [(l,v)], [], read_write x y t T r) ↦ (vl l', [mwrite l' v; mread l v]).
intros. unfold read_write. apply ELet with (v0:=v) (E:=[mread l v]) (S:=[(l,v)])
(S':=[(l,v)]) (E':=[mwrite l' v]). assert ([mread l v] = [] ++ [mread l v]). symmetry. apply
app_nil_l. rewrite H0. constructor. constructor. apply lookup_cons. auto. apply
lookup_cons. simpl. reflexivity.  assert ([mwrite l' v] = [] ++ [mwrite l' v]). rewrite <-
app_nil_l. reflexivity. rewrite H0. apply EWrite with (S':=[(l,v)]) (E1:=[])
(E2:=[]). constructor. unfold lu. rewrite lookup_cons. constructor. reflexivity.
inversion H. subst. assumption. constructor. apply lookup_cons. constructor.
constructor. intros; auto. inversion H1; auto. inversion H2; auto. inversion H3.
reflexivity. constructor. assert ([[mread l v] ; [mwrite l' v]] = ([[mread l v]]
++ ([mwrite l' v ]) :: [])). auto. rewrite H0. constructor. simpl. assert
([[mread l v]; []] = [] ++ [mread l v] :: [[]]). reflexivity. rewrite H1.
constructor. constructor. intros. simpl in *. destruct H2; auto. destruct H2;
auto. inversion H2. reflexivity. Qed.


