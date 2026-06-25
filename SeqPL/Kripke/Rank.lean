module

public import SeqPL.Kripke.Basic
public import SeqPL.Kripke.RootExtension

@[expose]
public section

open Classical

variable [Nonempty κ]

structure RootedModel (κ) [Nonempty κ] (α) extends M : Model κ α where
  root : M.Root

namespace Model

variable {M : Model κ α} [Fintype M.World] [M.IsGL] {i j : M.World}

noncomputable def World.rank {M : Model κ α} [Fintype M.World] [M.IsGL] (x : M.World) : ℕ := cwfHeight (· ≺ ·) x

lemma rank_lt_of_rel (hij : i ≺ j) : i.rank > j.rank := cwfHeight_gt_of hij

end Model


namespace RootedModel

variable {M : RootedModel κ α} [Fintype M.World] [M.IsGL] {x y : M.World} {n : ℕ}

noncomputable def height (M : RootedModel κ α) [Fintype M.World] [M.IsGL] : ℕ := M.root.1.rank

lemma exists_of_lt_height (hn : n < x.rank) : ∃ y : M.World, x ≺ y ∧ y.rank = n := cwfHeight_lt hn

lemma height_lt_iff_relItr {n : ℕ} {x : M.World} : x.rank < n ↔ ∀ y, ¬x ≺^[n] y := by
  match n with
  |     0 => simp_all
  | n + 1 =>
    suffices x.rank ≤ n ↔ ∀ y : M.World, x ≺ y → y.rank < n by
      calc
        _ ↔ x.rank ≤ n                   := Nat.lt_add_one_iff
        _ ↔ ∀ y, x ≺ y → y.rank < n      := this
        _ ↔ ∀ y, x ≺ y → ∀ k, ¬y ≺^[n] k := by grind [height_lt_iff_relItr (n := n)];
        _ ↔ ∀ k j, x ≺ j → ¬j ≺^[n] k    := by grind;
        _ ↔ ∀ j, ¬x ≺^[n + 1] j          := by simp;
    constructor
    · intro h y Rxy;
      exact lt_of_lt_of_le (cwfHeight_gt_of Rxy) h;
    · exact cwfHeight_le;

lemma le_height_iff_relItr : n ≤ x.rank ↔ ∃ y, x ≺^[n] y := calc
  _ ↔ ¬x.rank < n    := Iff.symm Nat.not_lt
  _ ↔ ∃ y, x ≺^[n] y := by simp [height_lt_iff_relItr]

lemma height_eq_iff_relItr : x.rank = n ↔ (∃ y, x ≺^[n] y) ∧ (∀ y, x ≺^[n] y → ∀ k, ¬y ≺ k) := calc
  _ ↔ x.rank < n + 1 ∧ n ≤ x.rank                       := by simpa [Nat.lt_succ_iff] using Nat.eq_iff_le_and_ge;
  _ ↔ (∀ y, ¬x ≺^[n + 1] y) ∧ (∃ y, x ≺^[n] y)          := by rw [height_lt_iff_relItr, le_height_iff_relItr];
  _ ↔ (∀ k y, x ≺^[n] y → ¬y ≺ k) ∧ (∃ y, x ≺^[n] y)    := by simp only [Model.relItr_succ']; grind;
  _ ↔ (∃ y, x ≺^[n] y) ∧ (∀ y, x ≺^[n] y → ∀ k, ¬y ≺ k) := by grind;

lemma exists_rank_terminal (x : M.World) : ∃ y, x ≺^[x.rank] y := le_height_iff_relItr.mp (by simp)

lemma terminal_rel_height (h : x ≺^[x.rank] y) : ∀ z, ¬y ≺ z := by
  intro z Ryz;
  suffices x.rank + 1 ≤ x.rank by omega;
  apply le_height_iff_relItr.mpr;
  exact ⟨z, Model.relItr_succ'.mpr ⟨y, h, Ryz⟩⟩;

@[grind <=]
lemma rank_lt_height (Rrx : M.root.1 ≺ x) : x.rank < M.height := cwfHeight_gt_of Rrx

@[grind .]
lemma rank_le_height : x.rank ≤ M.height := by
  by_cases exi : x = M.root.1
  · subst exi; rfl;
  · apply le_of_lt;
    apply rank_lt_height;
    grind;

@[grind =]
lemma iff_eq_rank_height_is_root : x.rank = M.height ↔ x = M.root.1 := by
  constructor;
  . contrapose!;
    intro h;
    apply Nat.ne_of_lt;
    apply rank_lt_height;
    grind;
  . tauto;

end RootedModel

end
