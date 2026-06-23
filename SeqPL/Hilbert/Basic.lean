module

public import SeqPL.Basic
public import SeqPL.Formula
public import SeqPL.Gentzen.WithCut

@[expose]
public section

inductive HilbertProof : Formula → Type
| prop1  {A B}   : HilbertProof $ A 🡒 B 🡒 A
| prop2  {A B C} : HilbertProof $ (A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C)
| prop3  {A B}   : HilbertProof $ (∼A 🡒 ∼B) 🡒 (B 🡒 A)
| modalK {A B}   : HilbertProof $ □(A 🡒 B) 🡒 (□A 🡒 □B)
| modal4 {A}     : HilbertProof $ □A 🡒 □□A
| modalL {A}     : HilbertProof $ □(□A 🡒 A) 🡒 □A
| mdp    {A B}   : HilbertProof (A 🡒 B) → HilbertProof A → HilbertProof B
| nec    {A}     : HilbertProof A → HilbertProof (□A)
prefix:50 "⊢ᴴ! " => HilbertProof

abbrev HilbertProvable (A : Formula) := Nonempty (⊢ᴴ! A)
prefix:50 "⊢ᴴ " => HilbertProvable

abbrev HilbertUnprovable (A : Formula) : Prop := ¬⊢ᴴ A
prefix:120 "⊬ᴴ " => HilbertUnprovable


namespace HilbertProvable

variable {A B C : Formula}

@[grind <=] lemma nec : ⊢ᴴ A → ⊢ᴴ □A := λ ⟨h⟩ => ⟨HilbertProof.nec h⟩
@[grind =>] lemma mdp : ⊢ᴴ (A 🡒 B) → ⊢ᴴ A → ⊢ᴴ B := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨HilbertProof.mdp h₁ h₂⟩
@[simp, grind .] lemma prop1 : ⊢ᴴ A 🡒 B 🡒 A := ⟨HilbertProof.prop1⟩
@[simp, grind .] lemma prop2 : ⊢ᴴ (A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C) := ⟨HilbertProof.prop2⟩
@[simp, grind .] lemma prop3 : ⊢ᴴ (∼A 🡒 ∼B) 🡒 (B 🡒 A) := ⟨HilbertProof.prop3⟩
@[simp, grind .] lemma modalK : ⊢ᴴ □(A 🡒 B) 🡒 (□A 🡒 □B) := ⟨HilbertProof.modalK⟩
@[simp, grind .] lemma modal4 : ⊢ᴴ □A 🡒 □□A := ⟨HilbertProof.modal4⟩
@[simp, grind .] lemma modalL : ⊢ᴴ □(□A 🡒 A) 🡒 □A := ⟨HilbertProof.modalL⟩
@[grind <=] lemma af :  ⊢ᴴ A → ⊢ᴴ B 🡒 A := λ h => mdp prop1 h

@[simp, grind .]
lemma impId : ⊢ᴴ A 🡒 A := mdp (mdp (prop2 (B := A 🡒 A)) prop1) prop1

@[induction_eliminator]
lemma rec
  {motive : (A : Formula) → ⊢ᴴ A → Prop}
  (prop1  : ∀ {A B} (h : ⊢ᴴ A 🡒 B 🡒 A), motive _ h)
  (prop2  : ∀ {A B C} (h : ⊢ᴴ (A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C)), motive _ h)
  (prop3  : ∀ {A B} (h : ⊢ᴴ (∼A 🡒 ∼B) 🡒 (B 🡒 A)), motive _ h)
  (modalK : ∀ {A B} (h : ⊢ᴴ □(A 🡒 B) 🡒 (□A 🡒 □B)), motive _ h)
  (modal4 : ∀ {A} (h : ⊢ᴴ □A 🡒 □□A), motive _ h)
  (modalL : ∀ {A} (h : ⊢ᴴ □(□A 🡒 A) 🡒 □A), motive _ h)
  (mdp    : ∀ {A B} (h₁ : ⊢ᴴ A 🡒 B) (h₂ : ⊢ᴴ A), motive _ h₁ → motive _ h₂ → motive _ (mdp h₁ h₂))
  (nec    : ∀ {A} (h : ⊢ᴴ A), motive A h → motive _ (nec h))
  : ∀ {A} (h : ⊢ᴴ A), motive _ h := by
  rintro A ⟨h⟩;
  induction h <;> grind;

end HilbertProvable


inductive HilbertDeduction : Set Formula → Formula → Type _
| ofProof {X A} : ⊢ᴴ! A → HilbertDeduction X A
| ofContext {X A} : A ∈ X → HilbertDeduction X A
| mdp {X A B} : (HilbertDeduction X (A 🡒 B)) → (HilbertDeduction X A) → (HilbertDeduction X B)
infix:50 " ⊢ᴴ! " => HilbertDeduction

abbrev HilbertDeducible (X : Set Formula) (A : Formula) := Nonempty (X ⊢ᴴ! A)
infix:50 " ⊢ᴴ " => HilbertDeducible

namespace HilbertDeducible

variable {X Y : Set Formula} {A B : Formula}

@[grind <=] lemma ofProvable : (⊢ᴴ A) → (X ⊢ᴴ A) := λ ⟨h⟩ => ⟨.ofProof h⟩
@[grind <=] lemma ofContext : A ∈ X → (X ⊢ᴴ A) := λ h => ⟨.ofContext h⟩
@[grind =>] lemma mdp : X ⊢ᴴ A 🡒 B → X ⊢ᴴ A → X ⊢ᴴ B := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨.mdp h₁ h₂⟩

@[induction_eliminator]
protected lemma rec
  {motive : (X : Set (Formula)) → (A : Formula) → (X ⊢ᴴ A) → Prop}
  (ofProvable : ∀ {X A}, (h : ⊢ᴴ A) → motive X A (ofProvable h))
  (ofContext : ∀ {X A}, (h : A ∈ X) → motive X A (ofContext h))
  (mdp : ∀ {X A B}, (hAB : X ⊢ᴴ A 🡒 B) → (hA : X ⊢ᴴ A) → (motive X (A 🡒 B) hAB) → (motive X A hA) → (motive X B (mdp hAB hA)))
  : ∀ {X A}, (h : X ⊢ᴴ A) → motive X A h := by
  rintro X A ⟨h⟩;
  induction h with
  | ofProof h => apply ofProvable ⟨h⟩;
  | _ => grind;

lemma of_subset_ctx (hXY : X ⊆ Y) : (X ⊢ᴴ A) → (Y ⊢ᴴ A) := λ h => by induction h <;> grind;

lemma to_ctx : (X ⊢ᴴ A 🡒 B) → (insert A X ⊢ᴴ B) := λ h => by
  apply mdp;
  . show insert A X ⊢ᴴ A 🡒 B;
    exact of_subset_ctx (by simp) h;
  . exact ofContext (by simp);

lemma drop_ctx (h : insert A X ⊢ᴴ B) : (X ⊢ᴴ A 🡒 B) := by
  generalize e : insert A X = Y at h;
  induction h with
  | ofProvable h =>
    subst e;
    exact ofProvable $ .af h;
  | ofContext h =>
    subst e;
    rcases Set.mem_insert_iff.mp h with (rfl | h);
    . exact ofProvable .impId;
    . apply mdp;
      . exact ofProvable (.prop1);
      . exact ofContext h;
  | mdp _ _ ihAB ihA =>
    subst e;
    replace ihAB := ihAB rfl;
    replace ihA := ihA rfl;
    exact mdp (mdp (ofProvable (.prop2)) ihAB) ihA;

theorem deduction_theorem : (insert A X ⊢ᴴ B) ↔ (X ⊢ᴴ A 🡒 B) := ⟨drop_ctx, to_ctx⟩

lemma iff_empty_ctx : (∅ ⊢ᴴ A) ↔ (⊢ᴴ A) := by
  constructor
  . intro h;
    generalize e : (∅ : Set Formula) = X at h;
    induction h <;> grind;
  . apply ofProvable;

lemma iff_singleton_deducible_provable : ({A} ⊢ᴴ B) ↔ (⊢ᴴ A 🡒 B) := by
  rw [show ({A} : Set Formula) = insert A ∅ by simp];
  apply Iff.trans deduction_theorem iff_empty_ctx;

end HilbertDeducible




namespace Provable

theorem of_provableHilbert : ⊢ᴴ A → ⊢ (∅ ⟹ {A}) := by
  intro h;
  induction h with
  | prop1 => exact .axiomŁ1;
  | prop2 => exact .axiomŁ2;
  | prop3 => exact .axiomŁ3;
  | modalK => exact .axiomK;
  | modal4 => exact .axiom4;
  | modalL => exact .axiomL;
  | nec _ h => exact .ruleNec h;
  | mdp _ _ ih₁ ih₂ => exact .mdp ih₁ ih₂;

@[induction_eliminator]
lemma rec
  {motive : (S : Sequent) → ⊢ S → Prop}
  (axm : ∀ A, motive ({A} ⟹ {A}) (Provable.axm A))
  (botL : motive ({⊥} ⟹ ∅) Provable.botL)
  (wkL : ∀ {Γ Γ' Δ} (h : ⊢ (Γ ⟹ Δ)) (h' : Γ ⊆ Γ'), motive (Γ ⟹ Δ) h → motive (Γ' ⟹ Δ) (wkL h h'))
  (wkR : ∀ {Γ Δ Δ'} (h : ⊢ (Γ ⟹ Δ)) (h' : Δ ⊆ Δ'), motive (Γ ⟹ Δ) h → motive (Γ ⟹ Δ') (wkR h h'))
  (impL : ∀ {Γ Δ A B} (h₁ : ⊢ (Γ ⟹ insert A Δ)) (h₂ : ⊢ (insert B Γ ⟹ Δ)),
    motive (Γ ⟹ insert A Δ) h₁ → motive (insert B Γ ⟹ Δ) h₂ → motive ((insert (A 🡒 B) Γ) ⟹ Δ) (impL h₁ h₂)
  )
  (impR : ∀ {Γ Δ A B} (h : ⊢ ((insert A Γ) ⟹ (insert B Δ))),
    motive ((insert A Γ) ⟹ (insert B Δ)) h → motive (Γ ⟹ (insert (A 🡒 B) Δ)) (impR h)
  )
  (boxGL : ∀ {Γ A} (h : ⊢ ((insert (□A) (Γ ∪ Γ.box)) ⟹ {A})),
    motive ((insert (□A) (Γ ∪ Γ.box)) ⟹ {A}) h → motive (Γ.box ⟹ {□A}) (boxGL h)
  )
  : ∀ {S : Sequent} (h : ⊢ S), motive S h := by
    rintro S ⟨h⟩;
    induction h <;> grind;

end Provable


attribute [simp, grind .] not_provable_empty

namespace HilbertProvable

variable {A B C G : Formula}

@[simp, grind .] lemma top : ⊢ᴴ ⊤ := by simp [Formula.top];

lemma impTrans : ⊢ᴴ A 🡒 B → ⊢ᴴ B 🡒 C → ⊢ᴴ A 🡒 C := by
  intro h₁ h₂;
  replace h₁ := HilbertDeducible.iff_singleton_deducible_provable.mpr h₁;
  replace h₂ : {A} ⊢ᴴ B 🡒 C := HilbertDeducible.ofProvable h₂;
  exact HilbertDeducible.iff_singleton_deducible_provable.mp $ HilbertDeducible.mdp h₂ h₁;

@[simp, grind .] lemma efq : ⊢ᴴ ⊥ 🡒 A := mdp prop3 (af top)
@[grind <=] lemma efqRule : ⊢ᴴ ⊥ → ⊢ᴴ A := mdp efq

@[simp, grind .]
lemma andL : ⊢ᴴ (A ⋏ B) 🡒 A := by
  apply HilbertDeducible.iff_singleton_deducible_provable.mp;
  rw [Formula.and]
  sorry;

@[simp, grind .]
lemma andR : ⊢ᴴ (A ⋏ B) 🡒 B := by
  apply HilbertDeducible.iff_singleton_deducible_provable.mp;
  rw [Formula.and];
  sorry;

@[grind =>] lemma andLRule : ⊢ᴴ (A ⋏ B) → ⊢ᴴ A := mdp andL
@[grind =>] lemma andRRule : ⊢ᴴ (A ⋏ B) → ⊢ᴴ B := mdp andR



@[simp, grind .]
lemma orL : ⊢ᴴ A 🡒 (A ⋎ B) := by
  apply HilbertDeducible.iff_singleton_deducible_provable.mp;
  apply HilbertDeducible.deduction_theorem.mp;

  have h₁ : {∼A, A} ⊢ᴴ ∼A := HilbertDeducible.ofContext (by grind);
  have h₂ : {∼A, A} ⊢ᴴ A := HilbertDeducible.ofContext (by grind);
  have h₃ : {∼A, A} ⊢ᴴ ⊥ 🡒 B := HilbertDeducible.ofProvable efq;
  have : {∼A, A} ⊢ᴴ ⊥ := HilbertDeducible.mdp h₁ h₂;
  exact HilbertDeducible.mdp h₃ this;

@[simp, grind .]
lemma orR : ⊢ᴴ B 🡒 (A ⋎ B) := by
  apply HilbertDeducible.iff_singleton_deducible_provable.mp;
  apply HilbertDeducible.deduction_theorem.mp
  rw [show {∼A, B} = {B, ∼A} by grind];
  apply HilbertDeducible.deduction_theorem.mpr;
  apply HilbertDeducible.ofProvable;
  exact impId;

@[grind =>] lemma orLRule : ⊢ᴴ A → ⊢ᴴ (A ⋎ B) := mdp orL
@[grind =>] lemma orRRule : ⊢ᴴ B → ⊢ᴴ (A ⋎ B) := mdp orR

attribute [grind <=] HilbertDeducible.ofContext
attribute [grind =>] HilbertDeducible.mdp

lemma mdp₂ : ⊢ᴴ A 🡒 B 🡒 C → ⊢ᴴ A → ⊢ᴴ B → ⊢ᴴ C := λ h₁ h₂ h₃ => mdp (mdp h₁ h₂) h₃

@[simp, grind .]
lemma andIntro : ⊢ᴴ A 🡒 B 🡒 (A ⋏ B) := by
  apply HilbertDeducible.iff_singleton_deducible_provable.mp;
  apply HilbertDeducible.deduction_theorem.mp;
  apply HilbertDeducible.deduction_theorem.mp;
  have h₁ : {A 🡒 ∼B, B, A} ⊢ᴴ A 🡒 (∼B) := by grind;
  have h₂ : {A 🡒 ∼B, B, A} ⊢ᴴ A := by grind;
  have h₃ : {A 🡒 ∼B, B, A} ⊢ᴴ B := by grind;
  exact HilbertDeducible.mdp (HilbertDeducible.mdp h₁ h₂) h₃;

@[grind <=]
lemma andIntroRule : ⊢ᴴ A → ⊢ᴴ B → ⊢ᴴ (A ⋏ B) := mdp₂ andIntro

@[simp, grind .]
lemma ctxAndIntro : ⊢ᴴ (G 🡒 A) 🡒 (G 🡒 B) 🡒 (G 🡒 (A ⋏ B)) := by
  apply HilbertDeducible.iff_singleton_deducible_provable.mp;
  apply HilbertDeducible.deduction_theorem.mp;
  apply HilbertDeducible.deduction_theorem.mp;
  apply HilbertDeducible.deduction_theorem.mp;
  have h₁ : {A 🡒 ∼B, G, G 🡒 B, G 🡒 A} ⊢ᴴ A 🡒 (∼B) := by grind;
  have h₂ : {A 🡒 ∼B, G, G 🡒 B, G 🡒 A} ⊢ᴴ G 🡒 A := by grind;
  have h₃ : {A 🡒 ∼B, G, G 🡒 B, G 🡒 A} ⊢ᴴ G 🡒 B := by grind;
  have h₄ : {A 🡒 ∼B, G, G 🡒 B, G 🡒 A} ⊢ᴴ G := by grind;
  grind;

lemma ctxAndIntroRule : ⊢ᴴ (G 🡒 A) → ⊢ᴴ (G 🡒 B) → ⊢ᴴ (G 🡒 (A ⋏ B)) := mdp₂ ctxAndIntro


lemma imp_lconj_of_mem {Γ : FormulaList} (h : A ∈ Γ) : ⊢ᴴ ⋀Γ 🡒 A := by
  match Γ with
  | [] | [B] => simp_all;
  | B :: C :: Γ =>
    simp only [List.mem_cons] at h;
    rcases h with (rfl | rfl | h);
    . simp [FormulaList.conj];
    . exact impTrans andR $ imp_lconj_of_mem (Γ := A :: Γ) (by simp);
    . exact impTrans andR $ imp_lconj_of_mem (Γ := C :: Γ) (by grind);


lemma imp_lconj_lconj_of_subset {Γ Γ' : FormulaList} (h : Γ' ⊆ Γ) : ⊢ᴴ ⋀Γ 🡒 ⋀Γ' := by
  match Γ' with
  | [] => apply af; simp;
  | [B] => apply imp_lconj_of_mem; grind;
  | B :: C :: Γ' =>
    have h₁ := imp_lconj_of_mem (Γ := Γ) (A := B) (by grind);
    have h₂ := imp_lconj_lconj_of_subset (Γ := Γ) (Γ' := C :: Γ') (by grind);
    exact ctxAndIntroRule h₁ h₂;

@[grind <=]
lemma imp_fconj_fconj_of_subset {Γ Γ' : FormulaFinset} (h : Γ' ⊆ Γ) : ⊢ᴴ ⋀Γ 🡒 ⋀Γ' := by
  apply imp_lconj_lconj_of_subset;
  intro A;
  simpa using @h A;


lemma imp_ldisj_of_mem {Γ : FormulaList} {A : Formula} (h : A ∈ Γ) : ⊢ᴴ A 🡒 ⋁Γ := by
  match Γ with
  | [] | [B] => simp_all;
  | B :: C :: Γ =>
    simp only [List.mem_cons] at h;
    rcases h with (rfl | rfl | h);
    . simp [FormulaList.disj];
    . exact impTrans (imp_ldisj_of_mem (Γ := A :: Γ) (by simp)) orR;
    . exact impTrans (imp_ldisj_of_mem (Γ := C :: Γ) (by grind)) orR;

@[grind <=]
lemma imp_ldisj_ldisj_of_subset {Γ Γ' : FormulaList} (h : Γ ⊆ Γ') : ⊢ᴴ ⋁Γ 🡒 ⋁Γ' := by
  match Γ with
  | [] => simp;
  | [B] => apply imp_ldisj_of_mem; grind;
  | B :: C :: Γ =>
    have h₁ := imp_ldisj_of_mem (Γ := Γ') (A := B) (by grind);
    have h₂ := imp_ldisj_ldisj_of_subset (Γ := C :: Γ) (Γ' := Γ') (by grind);
    sorry;

@[grind <=]
lemma imp_fdisj_fdisj_of_subset {Γ Γ' : FormulaFinset} (h : Γ ⊆ Γ') : ⊢ᴴ ⋁Γ 🡒 ⋁Γ' := by
  apply imp_ldisj_ldisj_of_subset;
  intro A;
  simpa using @h A;

theorem of_provableGentzen : ⊢ S → ⊢ᴴ (⋀S.ant) 🡒 (⋁S.suc) := by
  intro h;
  induction h with
  | axm A => simp;
  | botL => simp;
  | wkL _ hΓ ih =>
    exact HilbertProvable.impTrans (imp_fconj_fconj_of_subset (by grind)) ih;
  | wkR _ hΔ ih =>
    exact HilbertProvable.impTrans ih (imp_fdisj_fdisj_of_subset (by grind));
  | impL h₁ h₂ ih₁ ih₂ =>
    simp_all;
    sorry;
  | impR h ih =>
    simp_all;
    sorry;
  | boxGL h ih =>
    simp_all;
    sorry;

end HilbertProvable


theorem LogicGL_TFAE : [
  ⊢ᴴ A,
  ⊢ (∅ ⟹ {A}),
  ⊢ᵍᶜ (∅ ⟹ {A})
].TFAE
  := by
  tfae_have 1 → 2 := Provable.of_provableHilbert;
  tfae_have 2 → 1 := by
    intro h;
    simpa using HilbertProvable.mdp (HilbertProvable.of_provableGentzen (S := ∅ ⟹ {A}) h) (by simp);
  tfae_have 2 → 3 := GentzenWithCutProvable.of_without_cut;
  tfae_have 3 → 2 := Provable.of_with_cut;
  tfae_finish;

end
