Add LoadPath "C:\Coq\Classical Foundations" as LF.
From LF Require Export Foundations.
Require Import Ltac.

(*Equality*)
Theorem eq_symmetry (T:Type) : forall x y:T, x=y->y=x.
Proof fun (x y:T) (p:x=y) => p (fun t:T => t=x) (eqi x).
Notation "'eqs' x" := (eq_symmetry _ _ _ x) (at level 190, right associativity). 
Theorem eq_transitivity (T:Type) : forall x y z:T, x=y->y=z->x=z.
Proof fun (x y z:T) (p:x=y) (p0:y=z) => fun (P:T->Prop) (p1:P x) => p0 P (p P p1). 
Notation "'eqt' x y" := (eq_transitivity _ _ _ _ x y) (at level 190, right associativity). 

(*Quantifier*)
Theorem fa_comm@{u u0} (A:Type@{u}) (B:Type@{u0}) (P:A->B->Prop) : (forall (a:A) (b:B), P a b)->(forall (b:B) (a:A), P a b).
Proof fun p:forall (a:A) (b:B), P a b => fun (b:B) (a:A) => p a b.
Theorem ex_comm1@{u u0} (A:Type@{u}) (B:Type@{u0}) (P:A->B->Prop) : (∃a:A, ∃b:B, P a b)->(∃b:B, ∃a:A, P a b).
Proof. intros p. 
assert (forall a:A, (∃b:B, P a b)->∃b:B, ∃a:A, P a b).
  intros a p0. 
  assert(forall b:B, P a b-> ∃a:A, P a b).
    intros b p1. apply (ex_intro A (fun a0:A => P a0 b) a). exact p1. exact (exe p0 H).
assert (∃a0:A,∃b:B,∃a:A, P a b).
  exact (exe p H).
exact (H0 _ (fun a0:A => fun x => x)). Qed.
Theorem ex_comm2@{u u0} (A:Type@{u}) (B:Type@{u0}) (P:A->B->Prop) : (∃a:A, forall b:B, P a b)->(forall b:B, ∃a:A, P a b).
Proof. intros p.
assert (forall a:A, (forall b:B, P a b)->(forall b:B, ∃a:A, P a b)).
  intros a p0 b. exact(exi _ (p0 b)).
pose proof (exe p H).
exact (H0 (forall b:B, ∃a:A, P a b) (fun a:A => fun x => x)). Qed.




