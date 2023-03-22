Add LoadPath "C:\Coq\Classical Foundations" as LF.
From LF Require Export Foundations.
From LF Require Export Logical_Properties.
Require Import Ltac.

Parameter In:Set->Set->Prop.
Notation "x ∈ y" := (In x y) (at level 10).
Notation "x ∉ y" := (not (In x y)) (at level 10).
Axiom ax_ext : forall x y:Set, (forall t:Set, t∈x⇔t∈y)->x=y.
Axiom ax_emp : ∃x:Set, forall y:Set, y∉x.
Axiom ax_par : forall x y:Set, ∃z:Set, forall z0:Set, z0∈z⇔z0=x∨z0=y.
Axiom ax_uun : forall x:Set, ∃y:Set, forall y0:Set, y0∈y⇔∃x0:Set, x0∈x∧y0∈x0.
Axiom ax_spf : forall (x:Set) (P:Set->Prop), ∃y:Set, forall y0:Set, y0∈y⇔y0∈x∧P y0.
Axiom ax_rep : forall (x:Set) (f:Set->Set), ∃y:Set, forall y0:Set, y0∈y⇔∃x0:Set, x0∈x∧f x0=y0.
Axiom ax_ind : forall (x:Set) (f:Set->Set), ∃y:Set, forall y0:Set, y0∈y->f y0∈y.
Axiom ax_pow : forall x:Set, ∃y:Set, forall y0:Set, y0∈y⇔(forall y1:Set, y1∈y0->y1∈x).
Axiom ax_fnd : forall P:Set->Prop, (forall x:Set, (forall x0:Set, x0∈x-> P x0)->P x) -> forall x:Set, P x.
Axiom ax_gch : ∃f:Set->Set, forall x:Set, (∃x0:Set, x0∈x)->f x∈x.

Theorem abc : forall P:Set->Set->Prop, (forall x:Set, ∃!y:Set, P x y)->∃f:Set->Set, forall x y:Set, P x y⇔f x=y.
Proof. intros.
assert (forall x y:Set, P x y⇔ (fun x:Set => eps exue1 (H x)) x =y). intros. refine (iffi _ _).
intro. pose proof def exue1 (H x). exact (exue2 (H x) _ _ H1 H0).
intro. pose proof def exue1 (H x). exact (H0 _ H1). exact (exi _ H0). Qed.

Definition non_emp := fun x:Set => ∃x0:Set, x0∈x.
Theorem lch : forall x:Set, (forall x0:Set, x0∈x->non_emp x0)->∃f:Set->Set, forall x0:Set, x0∈x->f x0∈x0.
Proof. intros. pose proof (ax_gch). refine(exe H0 _).
intros. pose proof (H x0 H2).  
exact (H1 x0 H3). Qed.


Definition zero := eps ax_emp.
Notation "0" := (zero).
Theorem zeroi : forall x:Set, x∉0.
Proof def ax_emp.
Definition one : Set := eps (ax_par 0 0).
Notation "1" := (one).
Theorem onei : forall x:Set, x∈1⇔x=0.
Proof. intro. assert (forall x:Set, x∈1 ⇔ x=0∨x=0). exact (def (ax_par 0 0)). 
assert (x∈1->x=0).
  intro. pose proof (H x). pose proof (iffe1 H1 H0). pose proof(fun a:x=0 => a).
exact (H2 (x=0) H3 H3).
assert (x=0->x∈1).
  intro. pose proof (or_intro1 (x=0) (x=0) H1).
exact (iffe2 (H x) H2).
exact (iffi H0 H1). Qed.
Definition two : Set := eps (ax_par 0 1).
Notation "2" := (two).
Theorem twoi : forall x:Set, x∈2⇔x=0∨x=1.
Proof def (ax_par 0 1).
Lemma id_01 : 0∈1.
Proof. pose proof (onei 0). exact (iffe2 H (eqi 0)). Qed.
Lemma id_02 : 0∈2.
Proof. pose proof (twoi 0). pose proof (eqi 0). pose proof (or_intro1 (0=0) (0=1) H0). 
exact (iffe2 H H1). Qed.
Lemma id_12 : 1∈2.
Proof.  pose proof (twoi 1). pose proof (eqi 1). pose proof (or_intro2 (1=0) (1=1) H0). 
exact (iffe2 H H1). Qed.
Lemma id_setfalse : ¬1=0.
Proof. intro. pose proof id_01. pose proof H _ H0. pose proof zeroi 0. exact (H2 H1). Qed.
 
Theorem lem : forall p:Prop, p∨¬p.
Proof. intro p. pose proof (ax_spf 2 (fun x:Set => x=0∨p)). pose proof (ax_spf 2 (fun x:Set => x=1∨p)).
assert (forall a b:Set, (forall a0:Set, a0∈a⇔a0∈2∧(a0=0∨p))->(forall b0:Set, b0∈b⇔b0∈2∧(b0=1∨p))->p∨¬p).
  intros.
  assert (non_emp a).
    pose proof (H1 0). pose proof (or_intro1 (0=0) p (eqi 0)). pose proof (iffe2 H3 (andi id_02 H4)).
  exact (exi _ H5).
  assert (non_emp b).
    pose proof (H2 1). pose proof (or_intro1 (1=1) p (eqi 1)). pose proof (iffe2 H4 (andi id_12 H5)).
  exact (exi _ H6).
  pose proof (ax_par a b).
  assert(forall c:Set, (forall z0 : Set, z0 ∈ c ⇔ z0 = a ∨ z0 = b)->p∨¬p).
    intros. 
    assert (forall c0:Set, c0∈c-> non_emp c0). 
      intros. pose proof iffe1 (H6 c0) H7.
        assert(c0=a-> non_emp c0).
          intro. pose proof (eqs H9).
        exact (H10 _ H3).
        assert(c0=b->non_emp c0).
          intro. pose proof (eqs H10).
        exact(H11 _ H4).
      exact (H8 _ H9 H10).
    pose proof (lch c  H7).
    assert (forall f:Set->Set, (forall x:Set, x∈c->f x∈x)->p∨¬p).
      intros. pose proof H9 a (iffe2 (H6 a) (or_intro1 _ _ (eqi a))).
      pose proof  H9 b (iffe2 (H6 b) (or_intro2 _ _ (eqi b))).
      pose proof H1 (f a). pose proof ande2 (iffe1 H12 H10). pose proof (fun x:p => or_intro1 p (¬p) x).
      assert  (f a =0 -> p∨¬p).
        intro. pose proof H2 (f b). pose proof ande2 (iffe1 H16 H11).
        assert(f b=1-> p∨¬p).
          intro. assert(¬p). intro. assert (forall x:Set, x∈a⇔x∈b). intro.
          assert (x∈a->x∈b). intro. pose proof (H1 x). pose proof (iffe1 H21 H20). pose proof ande1 H22.
          pose proof (or_intro2 (x=1) _ H19). pose proof andi  H23 H24. exact(iffe2 (H2 x) H25). assert(x∈b->x∈a).
          intro. pose proof H2 x. pose proof iffe1 H22 H21. pose proof ande1 H23. pose proof or_intro2 (x=0) _ H19.
          pose proof andi H24 H25. exact(iffe2 (H1 x) H26). exact (iffi H20 H21). pose proof ax_ext a b H20.
          assert (f b=0). exact(H21 (fun x:Set => f x=0) H15). assert (1=0) by exact(H18 (fun x:Set => x=0) H22). 
          exact (id_setfalse H23). 
        exact(or_intro2 p _ H19).
      exact(H17 _ H18 H14).
    exact(H13 _ H15 H14). 
  exact(H8 _ H9).
exact (H5 _ H6).
assert (forall a:Set, (forall a0 : Set, a0∈a⇔a0∈2∧(a0=0∨p))->(∃b:Set, (forall b0:Set, b0∈b⇔b0∈2∧(b0=1∨p)))->p∨¬p).
  intros. pose proof H1 a. assert (forall b:Set, (forall b0:Set, b0∈b⇔b0∈2∧(b0=1∨p))->p∨¬ p). intros.
  exact (H1 a b H2 H5). 
exact (H3 _ H5).
pose proof (H _ H2). exact (H3 H0). Qed.

Theorem lem2 : forall p:Prop, ¬¬p->p.
Proof. intros. pose proof lem p. apply H0. exact (fun x => x). intro. pose proof H H1. apply H2. Qed.
Theorem lem_comm_ne@{u} (A:Type@{u}) (P:A->Prop) : ¬ (∃a:A, P a)->(forall a:A, ¬P a).
Proof. unfold not. intros. apply H. exact (exi _ H0). Qed.
Theorem lem_comm_na@{u} (A:Type@{u}) (P:A->Prop) : ¬ (forall a:A, P a)->(∃a:A, ¬P a).
Proof. intro. pose proof lem (∃a:A, ¬P a). apply H0. exact (fun x => x). intro. pose proof (lem_comm_ne _ _ H1).
assert (⊥). apply H. intro. pose proof H2 a. exact (lem2 _ H3). apply H3. Qed.

Theorem empu : ∃!x:Set, forall y:Set, y∉x.
Proof. refine (exui _ _). exact ax_emp. intros. apply ax_ext. intro. apply iffi.
intro. pose proof H t H1. exact (H2 _).
intro. pose proof H0 t H1. exact (H2 _). Qed.
Theorem paru : forall x y:Set, ∃!z:Set, forall z0:Set, z0∈z⇔z0=x∨z0=y.
Proof. intros. refine (exui _ _). exact (ax_par x y). intros. refine (ax_ext t0 t1 _).
intro. pose proof H t. pose proof H0 t. refine (iffi _ _). intro. pose proof (iffe1 H1 H3).
exact (iffe2 H2 H4). intro. pose proof iffe1 H2 H3. exact (iffe2 H1 H4). Qed. 
Theorem uunu : forall x:Set, ∃!y:Set, forall y0:Set, y0∈y⇔∃x0:Set, x0∈x∧y0∈x0.
Proof. intros. apply exui. apply ax_uun. intros. apply ax_ext. intro. apply iffi. 
intro. pose proof H t. pose proof iffe1 H2 H1. pose proof H0 t. exact (iffe2 H4 H3).
intro. pose proof H0 t. pose proof iffe1 H2 H1. pose proof H t. exact (iffe2 H4 H3). Qed.
Theorem spfu : forall (x:Set) (P:Set->Prop), ∃!y:Set, forall y0:Set, y0∈y⇔y0∈x∧P y0.
Proof. intros. apply exui. apply ax_spf. intros. apply ax_ext. intro. apply iffi. 
intro. pose proof H t. pose proof iffe1 H2 H1. pose proof H0 t. exact (iffe2 H4 H3).
intro. pose proof H0 t. pose proof iffe1 H2 H1. pose proof H t. exact (iffe2 H4 H3). Qed.
Theorem repu : forall (x:Set) (f:Set->Set), ∃!y:Set, forall y0:Set, y0∈y⇔∃x0:Set, x0∈x∧f x0=y0.
Proof. intros. apply exui. apply ax_rep. intros. apply ax_ext. intro. apply iffi. 
intro. pose proof H t. pose proof iffe1 H2 H1. pose proof H0 t. exact (iffe2 H4 H3).
intro. pose proof H0 t. pose proof iffe1 H2 H1. pose proof H t. exact (iffe2 H4 H3). Qed.
Theorem powu : forall x:Set, ∃!y:Set, forall y0:Set, y0∈y⇔(forall y1:Set, y1∈y0->y1∈x).
Proof. intros. apply exui. apply ax_pow. intros. apply ax_ext. intro. apply iffi. 
intro. pose proof H t. pose proof iffe1 H2 H1. pose proof H0 t. exact (iffe2 H4 H3).
intro. pose proof H0 t. pose proof iffe1 H2 H1. pose proof H t. exact (iffe2 H4 H3). Qed.

Definition par := fun x y:Set => eps (ax_par x y).
Theorem par_intro : forall x y:Set, forall t:Set, t∈(par x y)⇔t=x∨t=y. 
Proof. intros. pose proof (def (ax_par x y)). apply iffi. intro. pose proof H t. exact (iffe1 H1 H0).
intro. pose proof H t. exact (iffe2 H1 H0). Qed.
Definition parif := fun x y:Set => par_intro x y.
Notation "'pari' p" := (iffe2 (parif  _ _ _) p) (at level 10).
Notation "'pare' p" := (iffe1 (parif  _ _ _) p) (at level 10). 

Definition uun := fun x:Set => eps (ax_uun x).
Notation "⋃ x" := (uun x) (at level 9).
Theorem uun_intro : forall x t:Set, t∈⋃x⇔∃x0:Set, x0∈x∧t∈x0.
Proof. intros. pose proof def (ax_uun x). apply iffi. intro. pose proof H t. exact (iffe1 H1 H0).
intro. pose proof H t. exact (iffe2 H1 H0). Qed.
Definition uuniff := fun x:Set => uun_intro x.
Notation "'uunif' p" := (iffe2 (uuniff  _ _) p) (at level 10).
Notation "'uune' p" := (iffe1 (uuniff  _ _) p) (at level 10). 

Definition spf := fun (x:Set) (P:Set->Prop) => eps (ax_spf x P).
Notation "{ x0 ∈ x | P }" := (spf x (fun x0:Set => P)) (at level 9, x0 name).
Theorem spf_intro : forall (x:Set) (P:Set->Prop) (t:Set), t∈(spf x P)⇔t∈x∧P t.
Proof. intros. pose proof def (ax_spf x P). apply iffi. intro. pose proof H t. exact (iffe1 H1 H0).
intro. pose proof H t. exact (iffe2 H1 H0). Qed.
Definition spfif := fun (x:Set) (P:Set->Prop) => spf_intro x P.
Notation "'spfi' p" := (iffe2 (spfif  _ _) p) (at level 10).
Notation "'spfe' p" := (iffe1 (spfif  _ _) p) (at level 10). 

Definition subs := fun x y:Set => (forall t:Set, t∈x->t∈y).
Notation "x ⊆ y" := (subs x y) (at level 9).

Definition pow := fun x:Set => eps ax_pow x.
Theorem pow_intro : forall x t:Set, t∈(pow x)⇔t⊆x.
Proof. intros. pose proof def (ax_pow x). apply iffi. intro. pose proof H t. exact (iffe1 H1 H0).
intro. pose proof H t. exact (iffe2 H1 H0). Qed.
Definition powif := fun x:Set => pow_intro x.
Notation "'powi' p" := (iffe2 (uuniff  _ _) p) (at level 10).
Notation "'powe' p" := (iffe1 (uuniff  _ _) p) (at level 10). 

Definition rep := fun (x:Set) (f:Set->Set) => eps (ax_rep x f).
Notation "{ P | x0 ∈ x }" := (rep x (fun x0:Set => P)) (at level 9, x0 name).
Theorem rep_intro : forall (x:Set) (f:Set->Set) (t:Set), t∈(rep x f)⇔∃x0:Set, x0∈x∧f x0=t.
Proof. intros. pose proof def (ax_rep x f). apply iffi. intro. pose proof H t. exact (iffe1 H1 H0).
intro. pose proof H t. exact (iffe2 H1 H0). Qed.
Definition repif := fun (x:Set) (f:Set->Set) => rep_intro x f.
Notation "'repi' p" := (iffe2 (repif  _ _) p) (at level 10).
Notation "'repe' p" := (iffe1 (repif  _ _) p) (at level 10). 

Definition un := fun x y:Set => ⋃(par x y).
Notation "x ∪ y" := (un x y) (at level 9, right associativity).
Theorem un_intro : forall x y:Set, forall t:Set, t∈x∪y⇔t∈x∨t∈y.
Proof. intros. pose proof uuniff (par x y). pose proof H t. apply iffi. intro. pose proof iffe1 H0 H1.
assert (forall x0:Set, x0∈(par x y)∧t∈x0->t∈x∨t∈y). intros. pose proof ande1 H3. pose proof parif x y x0.
pose proof iffe1 H5 H4. pose proof ande2 H3. apply H6.
intro. apply ori1. apply H8. assumption. intro. apply ori2. apply H8. assumption.
pose proof exe H2 H3. apply H4. exact (fun _ x => x).
intro. apply (iffe2 H0). apply H1. intro. assert (x∈(par x y)). pose proof parif x y. pose proof H3 x.
apply (iffe2 H4). apply ori1. exact (eqi x). pose proof (andi H3 H2). exact (ex_intro _ _ x H4). 
intro. assert (y∈(par x y)). pose proof parif x y. pose proof H3 y.
apply (iffe2 H4). apply ori2. exact (eqi y). pose proof (andi H3 H2). exact (ex_intro _ _ y H4). Qed.
Definition unif := fun x y:Set => un_intro x y. 
Notation "'uni' p" := (iffe2 (unif  _ _) p) (at level 10).
Notation "'une' p" := (iffe1 (unif  _ _) p) (at level 10). 

Definition pun := fun (I:Set) (f:Set->Set) => ⋃ (rep I f).
Theorem pun_intro : forall (I:Set) (f:Set->Set), forall t:Set, t∈(pun I f)⇔∃i:Set, i∈I∧t∈(f i).
Proof. intros. unfold pun. pose proof uuniff (rep I f) t. pose proof repif I f. apply iffi.
intro. pose proof iffe1 H H1. apply H2. intros. pose proof ande1 H3. pose proof iffe1 (H0 t0) H4.
apply H5. intros. pose proof ande2 H6. pose proof ande2 H3. assert (t∈(f t1)). pose proof eqs H7. apply H9. exact H8.
pose proof ande1 H6. pose proof andi H10 H9. apply (exi t1 H11). 
intro. apply (iffe2 H). apply H1. intros. refine (exi (f t0) _). apply andi. apply (iffe2 (H0 (f t0))). pose proof ande1 H2.
pose proof eqi (f t0). pose proof andi H3 H4. exact (exi t0 H5). exact (ande2 H2). Qed.
Definition punif := fun (I:Set) (f:Set->Set) => pun_intro I f.
Notation "'puni' p" := (iffe2 (punif  _ _) p) (at level 10).
Notation "'pune' p" := (iffe1 (punif  _ _) p) (at level 10). 

Definition ins := fun x y:Set => spf x (fun t:Set => t∈y).
Notation "x ∩ y" := (ins x y) (at level 9, right associativity).
Theorem ins_intro : forall x y:Set, forall t:Set, t∈x∩y⇔t∈x∧t∈y.
Proof. unfold ins. intros. apply iffi. intro. pose proof spfif x (fun s => s∈y). pose proof H0 t. exact (iffe1 H1 H).
intro. pose proof spfif x (fun s => s∈y). pose proof H0 t. exact (iffe2 H1 H). Qed.
Definition insi := fun x y:Set => ins_intro x y.
Notation "'inse' p" := (iffe1 (insi  _ _ _) p) (at level 10). 

Definition pins := fun (I:Set) (f:Set->Set) (i:Set) (p:i∈I) => spf (f i) (fun x => forall i0:Set, i0∈I->x∈(f i0)).
Theorem pins_intro : forall (I:Set) (f:Set->Set) (i:Set) (p:i∈I), forall x:Set, x∈(pins I f i p)⇔forall i:Set, i∈I-> x∈(f i).
Proof. intros. pose proof spfif (f i) ((fun x => forall i0:Set, i0∈I->x∈(f i0))). apply iffi.
intros. pose proof H x. apply (iffe1 H2 H0). intros. exact (H4 i0 H1). 
intro. pose proof H x. apply (iffe2 H1). apply andi. exact (H0 i p). intros. exact (H0 i0 H2). Qed.
Notation "'pinsi' I f p" := (pins_intro I f _ p) (at level 9, right associativity).

Definition setm := fun x y:Set => spf x (fun t => t∉y).
Theorem setm_intro : forall x y:Set, forall t:Set, t∈(setm x y) ⇔ t∈x∧t∉y.
Proof. intros. apply iffi. intro. pose proof spfif x (fun t=>t∉y). pose proof H0 t. exact (iffe1 H1 H).
intro. pose proof spfif x (fun t=>t∉y). pose proof H0 t. exact (iffe2 H1 H). Qed.
Definition setmi := fun x y:Set => setm_intro x y.

Definition orp := fun x y:Set => par (par x y) (par x x).
Theorem orp_intro : forall a b c d:Set, orp a b = orp c d->a=c∧b=d.
Proof. unfold orp. intros. pose proof parif (par a b) (par a a). assert(a=c). assert ((par a a)∈(orp a b)). 
pose proof H0 (par a a). apply (iffe2 H1). apply ori2. exact (eqi _). pose proof (H _ H1). 
pose proof parif (par c d) (par c c). pose proof iffe1 (H3 _) H2. apply H4. intro. pose proof parif c d.
pose proof H6 c. pose proof (iffe2 H7 (ori1 (eqi c))). pose proof eqs H5. pose proof H9 _ H8.
pose proof parif a a. pose proof iffe1 (H11 c) H10. apply H12. intro. exact (eqs H13). intro. exact (eqs H13).
intro. pose proof parif a a. pose proof H6 a. pose proof iffe2 H7 (ori1 (eqi a)). pose proof H5 _ H8.
pose proof parif c c. pose proof iffe1 (H10 a) H9. apply H11. exact (fun x=>x). exact (fun x=>x).
assert (par (par c b) (par c c) = par (par c d) (par c c)).  
exact (H1 (fun a=> par (par a b) (par a a)= par (par c d) (par c c)) H). pose proof parif (par c b) (par c c).
pose proof H3 (par c b). pose proof iffe2 H4 (ori1 (eqi _)). pose proof H2 _ H5. pose proof parif (par c d) (par c c).
pose proof iffe1 (H7 (par c b)) H6. apply andi. assumption. apply H8. intro. assert (b∈(par c d)).
pose proof parif c b. pose proof iffe2 (H10 b) (ori2 (eqi _)). exact (H9 _ H11). pose proof parif c d b. pose proof iffe1 H11 H10.
apply H12. intro. pose proof H13 (fun x=>par c x=par c d) H9. pose proof parif c d d. pose proof iffe2 H15 (ori2 (eqi d)).
pose proof eqs H14. pose proof H17 _ H16. pose proof parif c c d. pose proof iffe1 H19 H18. assert (d=c). apply H20. exact (fun x=>x). 
exact (fun x=>x). pose proof eqs H21. exact (eq_transitivity _ _ _ _ H13 H22). exact (fun x=>x). intro. pose proof parif c b b.
pose proof iffe2 H10 (ori2 (eqi b)). pose proof parif c c b. pose proof H9 _ H11. pose proof iffe1 H12 H13. assert (b=c). 
apply H14. exact (fun x=>x). exact (fun x=>x). pose proof parif (par c d) (par c c) (par c d).
pose proof iffe2 H16 (ori1 (eqi _)). pose proof eqs H. pose proof H18 _ H17. pose proof parif (par a b) (par a a) (par c d).
pose proof iffe1 H20 H19. pose proof parif c d d. pose proof iffe2 H22 (ori2 (eqi _)). apply H21. intro. 
pose proof H24 _ H23. pose proof parif a b d. pose proof iffe1 H26 H25. apply H27. intro. pose proof eq_transitivity _ _ _ _ H28 H1.
pose proof eqs H29. exact (eq_transitivity _ _ _ _ H15 H30). intro. exact (eqs H28). intro. pose proof H24 _ H23. pose proof parif a a d. 
pose proof iffe1 H26 H25. assert (d=a). apply H27. exact (fun x=>x). exact (fun x=>x). pose proof eq_transitivity _ _ _ _ H28 H1.
pose proof eqs H29. exact (eq_transitivity _ _ _ _ H15 H30). Qed.
Definition orpi := fun (a b c d:Set) => orp_intro a b c d. 

Definition cart := fun X Y:Set => ⋃ (rep X (fun x:Set => rep Y (fun y:Set => orp x y))).
Notation "x × y" := (cart x y) (at level 9, right associativity).
Theorem cart_intro : forall X Y:Set, forall s:Set, s∈X×Y⇔∃x:Set, ∃y:Set, x∈X∧y∈Y∧(orp x y)=s. 
Proof. intros. unfold cart. apply iffi. intro. pose proof iffe1 (uuniff _ _) H. apply H0. intros. pose proof ande2 H1.
pose proof ande1 H1. pose proof iffe1 (repif _ _ _) H3. apply H4. intros. pose proof ande1 H5. pose proof ande2 H5. 
pose proof (eqs H7) _ H2. pose proof iffe1 (repif _ _ _) H8. apply H9. intros. pose proof ande1 H10. pose proof ande2 H10.
pose proof andi H11 H12. pose proof andi H6 H13. refine (exi t0 _). refine (exi t1 _). exact H14. 
intro. apply (iffe2 (uuniff _ _)). apply H. intros x H0. apply H0. intros y H1. 
assert (rep Y (fun y=> orp x y)∈(rep X (fun x=> rep Y (fun y=>orp x y))) ∧ s∈(rep Y (fun y=> orp x y))). apply andi.
apply (iffe2 (repif _ _ _)). refine (exi x _). apply andi. exact (ande1 H1). exact (eqi _). apply (iffe2 (repif _ _ _)).
refine (exi y _). apply andi. exact (ande1 (ande2 H1)). exact (ande2 (ande2 H1)). exact (exi (rep Y (fun y=> orp x y)) H2). Qed.
Definition carti := fun x y:Set => cart_intro x y.

Lemma ur1 : forall x:Set, x∉x.
Proof. refine (ax_fnd (fun x=> x∉x) _). intros. unfold not. intro. pose proof H x H0.  exact (H1 H0). Qed.
Lemma ur2 : forall x y:Set, x∈y->y∉x. 
Proof. refine (ax_fnd (fun x=> forall y:Set, x∈y->y∉x) _). unfold not. intros.  exact (H y H1 x H1 H0). Qed. 
Lemma non_0 : forall x:Set, x≠0-> ∃y:Set, y∈x.
Proof. intros. pose proof lem (∃y:Set, y∈x). apply H0. exact (fun x=>x). intro. pose proof lem_comm_ne _ _ H1. 
assert (x=0). apply ax_ext. intros. pose proof zeroi. apply iffi. intro. pose proof H2 t H4. apply H5. intro. apply (H3 t H4).
exact (H H3 _). Qed.  
Theorem reg : forall x:Set, non_emp x -> ∃y:Set, y∈x∧y∩x=0.
Proof. assert(forall x:Set, forall y:Set, x∈y->∃z:Set, z∈y∧z∩y=0). 
apply (ax_fnd (fun x:Set => (forall y:Set, x∈y->∃z:Set, z∈y∧z∩y=0))). intros. pose proof lem (x∩y=0). 
apply H1. intro. exact (exi x (andi H0 H2)). intro. pose proof non_0 (x∩y) H2. apply H3. intros. pose proof inse H4.
pose proof ande1 H5. pose proof ande2 H5. exact (H _ H6 _ H7). intros.
apply H0. intros. exact (H _ _ H1). Qed.
 

