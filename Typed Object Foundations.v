Require Import Ltac.
(*Chapter 0: Logical Constants in Object Calculus.*)
(*Notation "'Obj'" := (Prop).*)
Notation "x '->' y" := (forall (_ : x), y) (at level 99, right associativity, y at level 200). 

Definition eq (T:Type) : T->T->Prop := fun x y:T => forall P:T->Prop, P x->P y.
Notation "x = y" := (eq _ x y) (at level 70). 
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
Definition exu (T:Type) (P:T->Prop) : Prop := forall x:Prop, ((∃t:T, P t)->(forall t0 t1:T, P t0->P t1->t0=t1)->x)->x.
Notation "'∃!' t ':' T ',' p" := (exu T (fun t:T => p))  (at level 200, t name, right associativity). 
Theorem exu_intro (T:Type) (P:T->Prop) : (∃t:T, P t)->(forall t0 t1:T, P t0->P t1->t0=t1)->∃!t:T, P t.
Proof fun (h:∃t:T, P t) (h1:forall t0 t1:T, P t0->P t1->t0=t1) => fun x f=>f h h1. 
Notation "'exui'" := (exu_intro _ _).
Theorem exu_elim1 (T:Type) (P:T->Prop) : (∃!t:T, P t)->∃t:T, P t.
Proof. unfold exu. intros. apply H. intros. assumption. Qed.
Notation "'exue1'" := (exu_elim1 _ _).
Theorem exu_elim2 (T:Type) (P:T->Prop) : (∃!t:T, P t)->forall t0 t1:T, P t0->P t1->t0=t1.
Proof. unfold exu. intros. apply H. intros. apply H3. assumption. assumption. Qed.
Notation "'exue2'" := (exu_elim2 _ _).

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

Notation "x ≠ y" := (¬ x = y) (at level 70). 
Notation "'eqr'" := (eqi _ ). 
Theorem eq_symmetry (T:Type) : forall x y:T, x=y->y=x.
Proof fun (x y:T) (p:x=y) => p (fun t:T => t=x) (eqi x).
Notation "'eqs'" := (eq_symmetry _ _ _). 
Theorem eq_transitivity (T:Type) : forall x y z:T, x=y->y=z->x=z.
Proof fun (x y z:T) (p:x=y) (p0:y=z) => fun (P:T->Prop) (p1:P x) => p0 P (p P p1). 
Notation "'eqt'" := (eq_transitivity _ _ _ _ ). 
Theorem neq_symmetry (T:Type) : forall x y:T, x≠y->y≠x.
Proof.  intros. unfold not. intros. apply H. exact (eqs H0). Qed.
Notation "'neqs'" := (neq_symmetry _ _ _). 

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

Parameter nameing : forall (T:Type) (P:T->Prop), (∃t:T, P t)->T.
Notation "'name'" := (nameing _ _).
Axiom description : forall (T:Type) (P:T->Prop) (p:∃t:T, P t), P (name p).
Notation "'descr'" := (description _ _).


(*Prop Theory Axioms*)
Parameter In:Prop->Prop->Prop.
Notation "x ∈ y" := (In x y) (at level 10).
Notation "x ∉ y" := (not (In x y)) (at level 10).
Parameter H : Prop->Prop.
Definition cf : (Prop->Prop)->Prop := fun P:Prop->Prop => forall x:Prop, H x->H (P x).
Axiom ax_her : forall x:Prop, H x-> forall x0:Prop, x0∈x->H x0.
Axiom ax_ext : forall x y:Prop, H x->H y->(forall t:Prop, t∈x⇔t∈y)->x=y.
Axiom ax_emp : ∃x:Prop, H x∧forall y:Prop, y∉x.
Axiom ax_par : forall x y:Prop, H x->H y->∃z:Prop, H z∧forall z0:Prop, z0∈z⇔z0=x∨z0=y.
Axiom ax_uun : forall x:Prop, H x->∃y:Prop, H y∧forall y0:Prop, y0∈y⇔∃x0:Prop, x0∈x∧y0∈x0.
Axiom ax_spf : forall (x:Prop) (P:Prop->Prop), H x->∃y:Prop, H y∧forall y0:Prop, y0∈y⇔y0∈x∧P y0.
Axiom ax_rep : forall (x:Prop) (f:Prop->Prop), H x->cf f->∃y:Prop, H y∧forall y0:Prop, y0∈y⇔∃x0:Prop, x0∈x∧f x=y0.
Axiom ax_inf : forall (x:Prop) (f:Prop->Prop), H x->cf f->∃y:Prop, H y∧forall y0:Prop, y0∈y->f y0∈y.
Axiom ax_pow : forall x:Prop, H x->∃y:Prop, H y∧forall y0:Prop, y0∈y⇔(forall y1:Prop, y1∈y0->y1∈x).
Axiom ax_fnd : forall P:Prop->Prop, (forall x:Prop, H x->(forall x0:Prop, x0∈x-> P x0)->P x) -> forall x:Prop, H x->P x.
Axiom ax_gch : ∃f:Prop->Prop, forall x:Prop, H x->(∃x_0:Prop, x_0∈x)->f x∈x.
Axiom ax_gen_bin_rel@{u u0} : forall (A:Type@{u}) (B:Type@{u0}) (P:A->B->Prop) (Q:A->B->Prop->Prop), (forall (x:A) (y:B), P x y->
∃!z:Prop, Q x y z)->∃f:A->B->Prop, forall (x:A) (y:B) (z:Prop),  P x y->Q x y z⇔f x y=z.


(*Chapter 1: Foundational Principles and Operators.*)

(*Section 1.1: Law of Excluded Middle*)
Definition non_emp := fun x:Prop => ∃x_0:Prop, x_0∈x.
Definition zero := name ax_emp.
Notation "0" := (name ax_emp).
Theorem zero_intro : H 0∧forall x:Prop, x∉0.
Proof descr ax_emp.
Notation "'0i1'" := (ande1 zero_intro).
Notation "'0i2'" := (ande2 zero_intro).
Notation "'0e'" := (ande2 zero_intro _).
Definition one := name (ax_par _ _ 0i1 0i1).
Notation "1" := (name (ax_par _ _ 0i1 0i1)).
Theorem one_intro : H 1∧forall x:Prop, x∈1⇔x=0.
Proof. apply andi. exact (ande1 (descr (ax_par _ _ 0i1 0i1))). 
pose proof ande2 (descr (ax_par _ _ 0i1 0i1)). intros. pose proof H0 x. apply iffi. intro. apply (iffe1 H1 H2).
exact (fun x=>x). exact (fun x=>x). intro. apply (iffe2 H1). apply (ori1 H2). Qed.
Notation "'1i1'" := (ande1 one_intro).
Notation "'1i2'" := (ande2 one_intro).
Notation "'1e'" := (ande2 one_intro _).
Definition two := name (ax_par _ _ 0i1 1i1).
Notation "2" := (name (ax_par _ _ 0i1 1i1)).
Theorem two_intro : H 2∧forall x:Prop, x∈2⇔x=0∨x=1.
Proof. apply andi. exact (ande1 (descr (ax_par _ _ 0i1 1i1))). 
pose proof ande2 (descr (ax_par _ _ 0i1 1i1)). intros. pose proof H0 x. apply iffi. intro. apply (iffe1 H1 H2).
intro. apply (iffe2 H1 H2). Qed.
Notation "'2i1'" := (ande1 two_intro).
Notation "'2i2'" := (ande2 two_intro).
Notation "'2e'" := (ande2 two_intro _).
Lemma id_01 : 0∈1.
Proof. pose proof (1i2 0). exact (iffe2 H0 (eqr)). Qed.
Lemma id_02 : 0∈2.
Proof. pose proof (2i2 0). apply (iffe2 H0). exact (ori1 (eqr)). Qed.
Lemma id_12 : 1∈2.
Proof. pose proof (2i2 1). apply (iffe2 H0). exact (ori2 (eqr)). Qed.
Lemma neq_1_0 : ¬1=0.
Proof. intro. pose proof id_01. pose proof H0 _ H1. exact (0e H2). Qed.
Theorem lem : forall p:Prop, p∨¬p.
Proof. intro. pose proof (ax_spf 2 (fun x:Prop => x=0∨p) 2i1). apply H0. intros a ai. pose proof (ax_spf 2 (fun x:Prop => x=1∨p) 2i1).
apply H1. intros b bi. assert (non_emp a). apply (exi 0). apply (iffe2 (ande2 ai _)). apply andi. exact(id_02). exact(ori1 (eqi _)).
assert (non_emp b). apply (exi 1). apply (iffe2 (ande2 bi _)). apply andi. exact(id_12). exact(ori1 (eqi _)). pose proof ax_gch.
apply H4. intros f fi. pose proof fi a (ande1 ai) H2. pose proof fi b (ande1 bi) H3. pose proof iffe1 (ande2 ai _) H5.
pose proof ande2 H7. apply H8. intro. pose proof iffe1 (ande2 bi _) H6. pose proof ande2 H10. apply H11. intro. apply ori2. intro.
assert (a=b). apply ax_ext. exact (ande1 ai). exact (ande1 bi). intros. apply iffi. intro. apply (iffe2 (ande2 bi _)). apply andi.
pose proof ande2 ai t. pose proof iffe1 H15 H14. exact (ande1 H16). exact (ori2 H13). intro. apply (iffe2 (ande2 ai _)). apply andi.
pose proof ande2 bi t. pose proof iffe1 H15 H14. exact (ande1 H16). exact (ori2 H13). assert (f a=f b). apply H14. apply eqi.
pose proof H9 (fun x:Prop => x = f b) H15. apply neq_1_0. apply eqs. apply H12. exact H16. intro. exact (ori1 H12). intro.
exact (ori1 H9). Qed.
Theorem lem2 : forall p:Prop, ¬¬p->p.
Proof. intros. pose proof lem p. apply H1. exact (fun x=>x). intro. pose proof H0 H2. apply H3. Qed.
Theorem lem_comm_ne@{u} (A:Type@{u}) (P:A->Prop) : ¬ (∃a:A, P a)->(forall a:A, ¬P a).
Proof. unfold not. intros. apply H0. exact (exi _ H1). Qed.
Theorem lem_comm_na@{u} (A:Type@{u}) (P:A->Prop) : ¬ (forall a:A, P a)->(∃a:A, ¬P a).
Proof. intro. pose proof lem (∃a:A, ¬P a). apply H1. exact (fun x=>x). intro. pose proof (lem_comm_ne _ _ H2).
assert (⊥). apply H0. intro. pose proof H3 a. exact (lem2 _ H4). apply H4. Qed.

(*Section 1.2: Unique Axiom Variants.*)
Theorem emp_un : ∃!x:Prop, H x∧forall y:Prop, y∉x.
Proof. refine (exui _ _). exact ax_emp. intros. apply ax_ext. exact (ande1 H0). exact (ande1 H1). intro.
pose proof ande2 H0. pose proof ande2 H1. apply iffi. intro. apply (H2 t H4). intro. apply (H3 t H4). Qed. 
Theorem par_un : forall x y:Prop, H x->H y->∃!z:Prop, H z∧forall z0:Prop, z0∈z⇔z0=x∨z0=y.
Proof. intros. refine (exui _ _). exact (ax_par _ _ H0 H1). intros. apply ax_ext. exact (ande1 H2). exact (ande1 H3). intro.
pose proof ande2 H2. pose proof ande2 H3. apply iffi. intro. apply (iffe2 (H5 t)). exact (iffe1 (H4 t) H6).
intro. apply (iffe2 (H4 t)). exact (iffe1 (H5 t) H6). Qed.
Theorem uun_un : forall x:Prop, H x->∃!y:Prop, H y∧forall y0:Prop, y0∈y⇔∃x0:Prop, x0∈x∧y0∈x0.
Proof. intros. refine (exui _ _). exact (ax_uun _ H0). intros. apply ax_ext. exact (ande1 H1). exact (ande1 H2). intro.
pose proof ande2 H1. pose proof ande2 H2. apply iffi. intro. apply (iffe2 (H4 t)). exact (iffe1 (H3 t) H5).
intro. apply (iffe2 (H3 t)). exact (iffe1 (H4 t) H5). Qed.
Theorem spf_un : forall (x:Prop) (P:Prop->Prop), H x->∃!y:Prop, H y∧forall y0:Prop, y0∈y⇔y0∈x∧P y0.
Proof. intros. refine (exui _ _). exact (ax_spf _ _ H0). intros. apply ax_ext. exact (ande1 H1). exact (ande1 H2). intro.
pose proof ande2 H1. pose proof ande2 H2. apply iffi. intro. apply (iffe2 (H4 t)). exact (iffe1 (H3 t) H5).
intro. apply (iffe2 (H3 t)). exact (iffe1 (H4 t) H5). Qed.
Theorem rep_un : forall (x:Prop) (f:Prop->Prop), H x->cf f->∃!y:Prop, H y∧forall y0:Prop, y0∈y⇔∃x0:Prop, x0∈x∧f x=y0.
Proof. intros. refine (exui _ _). exact (ax_rep _ _ H0 H1). intros. apply ax_ext. exact (ande1 H2). exact (ande1 H3). intro.
pose proof ande2 H2. pose proof ande2 H3. apply iffi. intro. apply (iffe2 (H5 t)). exact (iffe1 (H4 t) H6).
intro. apply (iffe2 (H4 t)). exact (iffe1 (H5 t) H6). Qed.
Theorem pow_un : forall x:Prop, H x->∃!y:Prop, H y∧forall y0:Prop, y0∈y⇔(forall y1:Prop, y1∈y0->y1∈x).
Proof. intros. refine (exui _ _). exact (ax_pow _ H0). intros. apply ax_ext. exact (ande1 H1). exact (ande1 H2). intro.
pose proof ande2 H1. pose proof ande2 H2. apply iffi. intro. apply (iffe2 (H4 t)). exact (iffe1 (H3 t) H5).
intro. apply (iffe2 (H3 t)). exact (iffe1 (H4 t) H5). Qed.

(*Section 1.3: Operational Theory.*)
Theorem gen_un_rel@{u} : forall (A:Type@{u}) (P:A->Prop) (Q:A->Prop->Prop), (forall x:A, P x->
∃!y:Prop, Q x y)->∃f:A->Prop, forall (x:A) (y:Prop),  P x->Q x y⇔f x=y.
Proof. intros. pose proof ax_gen_bin_rel A A. assert ((forall x y:A, P x->∃!z:Prop, Q x z)->∃f:A->A->Prop, forall (x y:A) 
(z:Prop), P x->Q x z⇔f x y=z). exact(H1 (fun a b=>P a) (fun a b p=> Q a p)). apply H2. intros. apply H0. assumption.
intros f H3. apply (exi (fun a=> f a a)). intros. apply H3. assumption. Qed.
Definition cfb := fun f:Prop->Prop->Prop => forall x y:Prop, H x->H y->H (f x y). 
Theorem abc (P:Prop->Prop->Prop->Prop) : (forall x y:Prop, H x->H y->∃!z:Prop, H z∧P x y z)->∃f:Prop->Prop->Prop, cfb f∧
forall x y z:Prop, H x->H y->H z->P x y z⇔f x y=z.
Proof. intros. pose proof ax_gen_bin_rel _ _ (fun a b=>H a∧H b) (fun a b c=>H c∧P a b c). cbv beta in H1. apply H1.
intros. apply H0. exact(ande1 H2). exact(ande2 H2). intros f fi. apply (exi f). apply andi. unfold cfb. intros.
pose proof fi x y (f x y). apply H4. exact(andi H2 H3). intros. pose proof H6 eqr. exact(ande1 H7). intros. 
pose proof fi x y z (andi H2 H3). apply iffi. intro. apply (iffe1 H5). exact(andi H4 H6). intro. apply (iffe2 H5 H6). intros.
assumption. Qed.
Definition cfg1 := fun f:Prop->(Prop->Prop)->Prop => forall (x:Prop) (P:Prop->Prop), H x->H (f x P).
Theorem abr1 (G:Prop->(Prop->Prop)->Prop->Prop) : (forall (x:Prop) (P:Prop->Prop), H x->∃!y:Prop, H y∧G x P y)->
∃f:Prop->(Prop->Prop)->Prop, cfg1 f∧forall (x:Prop) (P:Prop->Prop) (y:Prop), H x->H y->G x P y⇔f x P=y.
Proof. intros. pose proof ax_gen_bin_rel _ _ (fun a b=>H a) (fun a b c=>H c∧G a b c). cbv beta in H1. apply H1. assumption.
intros f fi. apply (exi f). apply andi. unfold cfg1. intros.
pose proof fi x P (f x P) H2. apply (iffe2 H3). exact(eqr). intros. assumption. intros. 
pose proof fi x P y H2. apply iffi. intro. apply (iffe1 H4). exact(andi H3 H5). intro. apply (iffe2 H4 H5). intros.
assumption. Qed.
Definition cfg2 := fun f:Prop->(Prop->Prop)->Prop => forall (x:Prop) (g:Prop->Prop), H x->cf g->H (f x g).
Theorem abr2 (G:Prop->(Prop->Prop)->Prop->Prop) : (forall (x:Prop) (f:Prop->Prop), H x->cf f->∃!y:Prop, H y∧G x f y)->
∃f:Prop->(Prop->Prop)->Prop, cfg2 f∧forall (x:Prop) (g:Prop->Prop) (y:Prop), H x->cf g->H y->G x g y⇔f x g=y.
Proof. intros. pose proof ax_gen_bin_rel _ _ (fun a b=>H a∧cf b) (fun a b c=>H c∧G a b c). cbv beta in H1. apply H1. intros.
apply H0. exact(ande1 H2). exact(ande2 H2). intros f fi. apply (exi f). apply andi. unfold cfg2. intros.
pose proof fi x g (f x g) (andi H2 H3). apply (iffe2 H4). exact(eqr). intros. assumption. intros. 
pose proof fi x g y (andi H2 H3). apply iffi. intro. apply (iffe1 H5). exact(andi H4 H6). intro. apply (iffe2 H5 H6). intros.
assumption. Qed.


Definition par_ex : ∃f:Prop->Prop->Prop, forall x y :Prop, H x->H y-> H (f x y)∧forall t:Prop, t∈(f x y)⇔t=x∨t=y.
Proof. pose proof abc _ (par_un). cbv beta in H0. apply H0. intros par pari. apply (exi par). intros. apply andi. apply (ande1 pari).
assumption. assumption. pose proof ande2 pari x y (par x y). pose proof ande1 pari _ _ H1 H2. apply (H3 H1 H2 H4). 
intros. apply H6. exact(eqr). Qed.
Notation "'par'" := (name par_ex).
Theorem par_thm : forall (x y:Prop), H x->H y-> H (par x y)∧forall t:Prop, t∈(par x y)⇔t=x∨t=y.
Proof. intros. exact (descr (par_ex) x y H0 H1). Qed.
Notation "'pari1'" := (fun Hx Hy=>ande1 (par_thm _ _ Hx Hy )).
Notation "'pari2'" := (fun Hx Hy=>iffe2 (ande2 (par_thm _ _ Hx Hy) _)).
Notation "'pare'" := (fun Hx Hy=>iffe1 (ande2 (par_thm _ _ Hx Hy) _)).
Corollary par_fact1 : forall x y:Prop, H x->H y-> x∈(par x y).
Proof. intros. apply pari2. assumption. assumption. apply ori1. apply eqr. Qed.
Corollary par_fact2 : forall x y:Prop, H x->H y-> y∈(par x y).
Proof. intros. apply pari2. assumption. assumption. apply ori2. apply eqr. Qed.
Corollary par_sym : forall x y:Prop, H x->H y-> par x y=par y x.
Proof. intros. apply ax_ext. apply pari1. assumption. assumption. apply pari1. assumption. assumption. intros. apply iffi.
intros. pose proof pare H0 H1 H2. apply pari2. assumption. assumption. apply H3. intros. apply ori2. assumption.
intros. apply ori1. assumption. intro. pose proof pare H1 H0 H2. apply pari2. assumption. assumption. apply H3.
intros. apply ori2. assumption. intros. apply ori1. assumption. Qed.
  
Definition uun_ex := fun (x:Prop) (Hx:H x)=> name (ax_uun _ Hx).

Notation "'uun'" := (uun_op _).
Theorem uun_intro : forall x t:Set, t∈⋃x⇔∃x0:Set, x0∈x∧t∈x0.
Proof. intros. pose proof def (ax_uun x). apply iffi. intro. pose proof H t. exact (iffe1 H1 H0).
intro. pose proof H t. exact (iffe2 H1 H0). Qed.
Definition uuniff := fun x:Set => uun_intro x.
Notation "'uunif' p" := (iffe2 (uuniff  _ _) p) (at level 10).
Notation "'uune' p" := (iffe1 (uuniff  _ _) p) (at level 10). 





