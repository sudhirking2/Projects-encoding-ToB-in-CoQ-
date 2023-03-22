Require Import Ltac.
(*Definitions of Logical Constants in Propect Calculus.*)
Notation "x '->' y" := (forall (_ : x), y) (at level 99, right associativity, y at level 200). 
Definition False : Prop := forall x:Prop, x.
Notation "⊥" := False. 
Definition not : Prop -> Prop := fun P:Prop => P->⊥.
Notation "¬ x" := (not x) (at level 75, right associativity).
Definition and : Prop->Prop->Prop := fun P Q:Prop => forall x:Prop, (P -> Q -> x) -> x.
Notation "x ∧ y" := (and x y) (at level 80, right associativity).
Theorem and_intro : forall (P Q : Prop), P -> Q -> P ∧ Q.
Proof fun _ _ p q _ f => f p q.
Notation "'andi'" := (and_intro _ _).
Theorem and_elim1 : forall (P Q:Prop) (f:P∧Q), P.
Proof fun P Q:Prop => fun f:P∧Q => f P (fun p:P => fun q:Q => p).
Notation "'ande1'" := (and_elim1 _ _).
Theorem and_elim2 : forall (P Q:Prop) (f:P∧Q), Q.
Proof fun P Q:Prop => fun f:P∧Q => f Q (fun p:P => fun q:Q => q).
Notation "'ande2'" := (and_elim2 _ _).
Definition or : Prop->Prop->Prop := fun P Q:Prop => forall x:Prop, (P->x)->(Q->x)->x.
Notation "x ∨ y" := (or x y) (at level 85, right associativity).
Theorem or_intro1 : forall P Q:Prop, P->P∨Q.
Proof fun P Q:Prop => fun p:P => fun x:Prop => fun f:P->x => fun g:Q->x => f p.
Notation "'ori1'" := (or_intro1 _ _).
Theorem or_intro2 : forall P Q:Prop, Q->P∨Q.
Proof fun P Q:Prop => fun q:Q => fun x:Prop => fun f:P->x => fun g:Q->x => g q.
Notation "'ori2'" := (or_intro2 _ _).
Definition iff : Prop->Prop->Prop := fun P Q:Prop => (P->Q)∧(Q->P).
Notation "x ⇔ y" := (iff x y) (at level 95, right associativity).
Theorem iff_intro : forall P Q:Prop, (P->Q)->(Q->P)->P⇔Q.
Proof fun P Q:Prop => fun f:P->Q => fun g:Q->P => andi f g.
Notation "'iffi'" := (iff_intro _ _).
Theorem iff_elim1 : forall P Q:Prop, P⇔Q->P->Q.
Proof fun P Q:Prop => fun f:P⇔Q => fun p:P => (ande1 f) p.
Notation "'iffe1'" := (iff_elim1 _ _).
Theorem iff_elim2 : forall P Q:Prop, P⇔Q->Q->P.
Proof fun P Q:Prop => fun f:P⇔Q => fun q:Q => (ande2 f) q.
Notation "'iffe2'" := (iff_elim2 _ _).
Definition eq (T:Type) : T->T->Prop := fun x y:T => forall P:T->Prop, P x->P y.
Notation "x = y" := (eq _ x y) (at level 70).
Notation "x ≠ y" := (¬ x = y) (at level 70). 
Theorem eq_intro (T:Type) : forall x:T, x=x.
Proof fun (x:T) (P:T->Prop) (f:P x) => f.
Notation "'eqi'" := (eq_intro _).
Definition ex (T:Type) (P:T->Prop) : Prop := forall x:Prop, (forall t:T, P t->x)->x.
Notation "'∃' t ':' T ',' p" := (ex T (fun t:T => p))  (at level 200, t name, right associativity). 
Theorem ex_intro (T:Type) (P:T->Prop) : forall t:T, P t->∃t:T, P t.
Proof fun t:T => fun p: P t => fun x:Prop => fun f:(forall t:T, P t->x) => f t p. 
Notation "'exi'" := (ex_intro _ _).
Theorem ex_elim (T:Type) (P:T->Prop) (Q:T->Prop) : (∃t:T, P t)->(forall t:T, P t->Q t)->∃t:T, Q t.
Proof fun f:∃t:T, P t => fun g: forall t:T, P t->Q t => f (∃t:T, Q t) (fun t:T => fun h:P t => ex_intro _ _ _ (g t h)).
Notation "'exe'" := (ex_elim _ _ _).
Definition exu (T:Type) (P:T->Prop) : Prop := (∃t:T, P t)∧forall t0 t1:T, P t0->P t1->t0=t1.
Notation "'∃!' t ':' T ',' p" := (exu T (fun t:T => p))  (at level 200, t name, right associativity). 
Theorem exu_intro (T:Type) (P:T->Prop) : (∃t:T, P t)->(forall t0 t1:T, P t0->P t1->t0=t1)->∃!t:T, P t.
Proof fun (h:∃t:T, P t) (h1:forall t0 t1:T, P t0->P t1->t0=t1) => andi h h1.
Notation "'exui'" := (exu_intro _ _).
Theorem exu_elim1 (T:Type) (P:T->Prop) : (∃!t:T, P t)->∃t:T, P t.
Proof fun h:∃!t:T, P t => ande1 h.
Notation "'exue1'" := (exu_elim1 _ _).
Theorem exu_elim2 (T:Type) (P:T->Prop) : (∃!t:T, P t)->forall t0 t1:T, P t0->P t1->t0=t1.
Proof fun h:∃!t:T, P t => ande2 h.
Notation "'exue2'" := (exu_elim2 _ _).
Parameter hilberts_epsilon : forall (T:Type) (P:T->Prop), (∃t:T, P t)->T.
Notation "'eps' x" := (hilberts_epsilon _ _ x) (at level 100).
Axiom definition : forall (T:Type) (P:T->Prop) (p:∃t:T, P t), P (eps p).
Notation "'def' x" := (definition _ _ x) (at level 100).








