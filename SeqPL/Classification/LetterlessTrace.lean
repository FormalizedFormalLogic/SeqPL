module

public import SeqPL.Formula
public import SeqPL.Kripke.Rank
public import SeqPL.Logic.Basic

@[expose]
public section

namespace Set

variable {α : Type*} {s t : Set α} {a b : α}

abbrev Cofinite (s : Set α) := sᶜ.Finite
abbrev Coinfinite (s : Set α) := sᶜ.Infinite

lemma iff_cofinite_comp_finite : s.Cofinite ↔ sᶜ.Finite := by grind;
lemma iff_coinfinite_comp_infinite : s.Coinfinite ↔ sᶜ.Infinite := by grind;

@[push] lemma iff_cofinite_not_coinfinite : s.Cofinite ↔ ¬s.Coinfinite := by simp;
@[push] lemma iff_coinfinite_not_cofinite : s.Coinfinite ↔ ¬s.Cofinite := by simp;

@[push, grind =_] lemma iff_cofinite_compl : sᶜ.Cofinite ↔ s.Finite := by simp [Cofinite];
@[push, grind =_] lemma iff_coinfinite_compl : sᶜ.Coinfinite ↔ s.Infinite := by simp [Coinfinite];

@[grind ->]
lemma Cofinite.subset (h : s ⊆ t) : s.Cofinite → t.Cofinite := by
  intro h;
  apply Set.Finite.subset (s := sᶜ) h;
  tauto_set;

@[grind ->]
lemma Coinfinite.subset (h : t ⊆ s) : s.Coinfinite → t.Coinfinite := by
  contrapose!;
  suffices t.Cofinite → s.Cofinite by grind;
  grind;

@[simp, grind .]
lemma univ_cofinite : (Set.univ (α := α)).Cofinite := by simp [Set.Cofinite];

@[grind <=]
lemma cofinite_union_left (hs : s.Cofinite) : (s ∪ t).Cofinite := by
  grind [compl_union, Set.Finite.inter_of_left];

@[grind <=]
lemma cofinite_union_right (ht : t.Cofinite) : (s ∪ t).Cofinite := by
  exact (show (t ∪ s) = (s ∪ t) by tauto_set) ▸ cofinite_union_left ht;

end Set


namespace Formula


@[grind]
def letterlessSpectrum (A : Formula Empty) : Set ℕ :=
  match A with
  | ⊥ => ∅
  | A 🡒 B => (A.letterlessSpectrum)ᶜ ∪ B.letterlessSpectrum
  | □A => { n | ∀ i < n, i ∈ A.letterlessSpectrum }

variable {A B : Formula Empty}

lemma letterlessSpectrum_bot : (⊥ : Formula Empty).letterlessSpectrum = ∅ := by grind;
lemma letterlessSpectrum_top : (⊤ : Formula Empty).letterlessSpectrum = Set.univ := by grind;
lemma letterlessSpectrum_imp : (A 🡒 B).letterlessSpectrum = A.letterlessSpectrumᶜ ∪ B.letterlessSpectrum := by simp [letterlessSpectrum]
lemma letterlessSpectrum_neg : (∼A).letterlessSpectrum = A.letterlessSpectrumᶜ := by simp [letterlessSpectrum]
lemma letterlessSpectrum_or  : (A ⋎ B).letterlessSpectrum = A.letterlessSpectrum ∪ B.letterlessSpectrum := by simp [letterlessSpectrum];
lemma letterlessSpectrum_and : (A ⋏ B).letterlessSpectrum = A.letterlessSpectrum ∩ B.letterlessSpectrum := by simp [letterlessSpectrum];
lemma letterlessSpectrum_box : (□A).letterlessSpectrum = { n | ∀ i < n, i ∈ A.letterlessSpectrum } := by simp [letterlessSpectrum];

attribute [simp, grind .]
  letterlessSpectrum_bot
  letterlessSpectrum_top
attribute [grind =]
  letterlessSpectrum_imp
  letterlessSpectrum_neg
  letterlessSpectrum_or
  letterlessSpectrum_and
  letterlessSpectrum_box

@[simp, grind =]
lemma letterlessSpectrum_boxItr {n : ℕ} : (□^[(n + 1)]A).letterlessSpectrum = { k | ∀ i < k, i ∈ (□^[n]A).letterlessSpectrum } := by
  induction n <;> grind;

@[grind =]
lemma letterlessSpectrum_boxdot : (⊡A).letterlessSpectrum = { n | ∀ i ≤ n, i ∈ A.letterlessSpectrum } := by grind;

@[simp, grind =]
lemma letterlessSpectrum_boxItr_bot : letterlessSpectrum (□^[n]⊥) = { i | i < n } := by
  induction n with
  | zero => grind;
  | succ n ih =>
    calc
      _ = { i | ∀ k < i, k ∈ letterlessSpectrum (□^[n]⊥) } := by grind
      _ = { i | ∀ k < i, k < n }                           := by simp [ih];
      _ = { i | i < n + 1 }                                := by grind;

@[simp, grind =]
lemma letterlessSpectrum_lconj {Γ : FormulaList Empty} : (⋀Γ).letterlessSpectrum = ⋂ A ∈ Γ, A.letterlessSpectrum := by
  match Γ with
  | [] | [A] | A :: B :: Γ => simp [FormulaList.conj, letterlessSpectrum_and, letterlessSpectrum_lconj]

@[simp, grind =]
lemma letterlessSpectrum_fconj {Γ : FormulaFinset Empty} : (⋀Γ).letterlessSpectrum = ⋂ A ∈ Γ, A.letterlessSpectrum := by
  simp [FormulaFinset.conj, letterlessSpectrum_lconj];

@[simp, grind =]
lemma letterlessSpectrum_TBB : (TBB n).letterlessSpectrum = {n}ᶜ := by
  rw [TBB, letterlessSpectrum_imp, letterlessSpectrum_boxItr_bot, letterlessSpectrum_boxItr_bot];
  ext i;
  grind;

@[grind]
def letterlessTrace (A : Formula Empty) := (A.letterlessSpectrum)ᶜ

lemma letterlessTrace_bot : (⊥ : Formula Empty).letterlessTrace = Set.univ := by grind;
lemma letterlessTrace_top : (⊤ : Formula Empty).letterlessTrace = ∅ := by grind;
lemma letterlessTrace_and : (A ⋏ B).letterlessTrace = A.letterlessTrace ∪ B.letterlessTrace := by grind;
lemma letterlessTrace_or  : (A ⋎ B).letterlessTrace = A.letterlessTrace ∩ B.letterlessTrace := by grind;
lemma letterlessTrace_imp : (A 🡒 B).letterlessTrace = A.letterlessTraceᶜ ∩ B.letterlessTrace := by grind;
lemma letterlessTrace_neg : (∼A).letterlessTrace = A.letterlessTraceᶜ := by grind;

attribute [simp, grind .]
  letterlessTrace_bot
  letterlessTrace_top
attribute [grind =]
  letterlessTrace_and
  letterlessTrace_or
  letterlessTrace_imp
  letterlessTrace_neg

@[simp, grind =]
lemma letterlessTrace_TBB : (TBB n).letterlessTrace = {n} := by grind;

@[grind .]
lemma letterlessSpectrum_finite_or_cofinite : A.letterlessSpectrum.Finite ∨ A.letterlessSpectrum.Cofinite := by
  induction A with
  | atom a => grind;
  | bot => grind;
  | imp A B ihA ihB =>
    simp only [letterlessSpectrum_imp, Set.finite_union];
    rcases ihA with (hA | hA) <;> rcases ihB with (hB | hB) <;> grind;
  | box A ih =>
    by_cases h : A.letterlessSpectrum = Set.univ;
    . grind;
    . left;
      obtain ⟨k, hk₁, hk₂⟩ := exists_minimal_of_wellFoundedLT (λ k => k ∉ A.letterlessSpectrum) $ Set.ne_univ_iff_exists_notMem _ |>.mp h;
      have : {n | ∀ i < n, i ∈ A.letterlessSpectrum} = { n | n ≤ k} := by
        ext i;
        suffices (∀ j < i, j ∈ A.letterlessSpectrum) ↔ i ≤ k by simpa [Set.mem_setOf_eq];
        constructor;
        . intro h;
          contrapose! hk₁;
          exact h k (by omega);
        . intro h j hji;
          contrapose! hk₂;
          use j;
          constructor;
          . assumption;
          . omega;
      rw [letterlessSpectrum_box, this];
      apply Set.finite_le_nat;

@[grind .]
lemma letterlessTrace_finite_or_cofinite : A.letterlessTrace.Finite ∨ A.letterlessTrace.Cofinite := by
  grind [letterlessTrace, letterlessSpectrum_finite_or_cofinite];

end Formula


namespace Model

variable
  [Nonempty κ]
  {M : Model κ Empty} [Fintype M.World] [M.IsGL]
  {x : M.World} {A : Formula Empty}

lemma iff_forces_rank_mem_letterlessSpectrum : x ⊩ A ↔ x.rank ∈ A.letterlessSpectrum := by
  induction A generalizing x with
  | box A ih =>
    calc
      _ ↔ ∀ y, x ≺ y → y ⊩ A := by grind;
      _ ↔ ∀ y, x ≺ y → y.rank ∈ A.letterlessSpectrum := by simp [ih];
      _ ↔ ∀ i < x.rank, i ∈ A.letterlessSpectrum := by
        constructor;
        . intro h i hi;
          grind [of_lt_rank hi];
        . grind [rank_lt_of_rel];
      _ ↔ x.rank ∈ (□A).letterlessSpectrum := by grind;
  | _ => grind;

lemma iff_not_forces_rank_mem_trace : x ⊮ A ↔ x.rank ∈ A.letterlessTrace := by
  grind [iff_forces_rank_mem_letterlessSpectrum];

end Model

abbrev finiteLineModel (n : ℕ) : RootedModel (Fin (n + 1)) Empty where
  Rel' := (· < ·)
  Val' _ _ := False
  root := ⟨0, by sorry⟩

namespace finiteLineModel

variable {n : ℕ}

instance : Fintype (finiteLineModel n).World := inferInstance
instance : (finiteLineModel n).IsFiniteGL where
  finite := by infer_instance
instance : (finiteLineModel n).IsGL := Model.instIsGLOfIsFiniteGL

protected abbrev of (i : Fin (n + 1)) : (finiteLineModel n).World := i
instance : Coe (Fin (n + 1)) (finiteLineModel n).World := ⟨finiteLineModel.of⟩

lemma _root_.PNat.exists_eq_succ (n : ℕ+) : ∃ m : ℕ, n = m + 1 := by
  if n = 1 then
    use 0;
    simp_all;
  else
    obtain ⟨m, hm⟩ := PNat.exists_eq_succ_of_ne_one ‹_›;
    use m;
    simp_all;

lemma rank_eq (i : (finiteLineModel n).World) : i.rank = (n - i) := by
  induction i using Fin.reverseInduction with
  | last => sorry;
  | cast i ih =>
    suffices (finiteLineModel.of i.castSucc).rank = (finiteLineModel.of i.succ).rank + 1 by grind;
    apply Model.iff_rank_eq.mpr;
    constructor;
    . sorry;
    . intro z;
      sorry;

lemma height_eq : (finiteLineModel n).height = n := by apply rank_eq;

end finiteLineModel

section

variable {A B : Formula Empty}

lemma letterlessSpectrum_TFAE : [
  n ∈ A.letterlessSpectrum,
  ∀ {κ : Type 0}, [Nonempty κ] → [Fintype κ] → ∀ M : Model κ Empty, [M.IsGL] → ∀ x : M.World, x.rank = n → x ⊩ A,
  ∃ κ : Type 0, ∃ _ : Nonempty κ, ∃ _ : Fintype κ, ∃ M : Model κ Empty, ∃ _ : M.IsGL, ∃ x : M.World, x.rank = n ∧ x ⊩ A,
].TFAE := by
  tfae_have 1 → 2 := by grind [Model.iff_forces_rank_mem_letterlessSpectrum];
  tfae_have 3 → 1 := by grind [Model.iff_forces_rank_mem_letterlessSpectrum];
  tfae_have 2 → 3 := by
    intro h;
    use Fin (n + 1), inferInstance, inferInstance, (finiteLineModel n).toModel, inferInstance, (finiteLineModel n).root.1;
    constructor;
    . exact finiteLineModel.height_eq;
    . apply h;
      exact finiteLineModel.height_eq;
  tfae_finish;

lemma iff_GL_proves_letterlessSpectrum_univ : A ∈ LogicGL _ ↔ A.letterlessSpectrum = Set.univ := by
  rw [Set.eq_univ_iff_forall];
  apply Iff.trans $ LogicGL_TFAE.out 0 4;
  constructor;
  . intro h n;
    apply letterlessSpectrum_TFAE.out 1 0 |>.mp;
    intro κ _ _ M _ x rfl;
    apply @h κ _ M (by sorry);
  . intro h κ _ M _ x;
    sorry;

lemma iff_GL_proves_imp_GL_subset_letterlessSpectrum : (A 🡒 B) ∈ LogicGL _ ↔ A.letterlessSpectrum ⊆ B.letterlessSpectrum := by
  apply Iff.trans iff_GL_proves_letterlessSpectrum_univ;
  simp only [Formula.letterlessSpectrum_imp, Set.eq_univ_iff_forall, Set.mem_union, Set.mem_compl_iff];
  grind;

lemma iff_GL_proves_iff_GL_subset_letterlessSpectrum : (A 🡘 B) ∈ LogicGL _ ↔ A.letterlessSpectrum = B.letterlessSpectrum := by
  suffices (A 🡘 B) ∈ LogicGL _ ↔ (A 🡒 B) ∈ LogicGL _ ∧ (B 🡒 A) ∈ LogicGL _ by
    grind [Set.Subset.antisymm_iff, iff_GL_proves_imp_GL_subset_letterlessSpectrum];
  constructor;
  . intro h;
    sorry;
  . sorry;

lemma GL_proves_letterless_axiomWeakPoint3 : ((□((⊡A) 🡒 B)) ⋎ (□((⊡B) 🡒 A))) ∈ LogicGL _ := by
  apply iff_GL_proves_letterlessSpectrum_univ.mpr;
  grind;

end

end
