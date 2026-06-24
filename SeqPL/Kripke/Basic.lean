module

public import SeqPL.Gentzen.Basic

@[expose]
public section

structure Model (κ : Type u) [Nonempty κ] (α : Type v) where
  Rel' : κ → κ → Prop
  Val' : κ → α → Prop

namespace Model

variable [Nonempty κ] {M : Model κ α}

abbrev World (_ : Model κ α) := κ
abbrev Rel {M : Model κ α} : M.World → M.World → Prop := M.Rel'
infixl:60 " ≺ " => Rel

abbrev Val {M : Model κ α} : M.World → α → Prop := M.Val'

abbrev _root_.IsConverseWellFounded (α) (R : α → α → Prop) := IsWellFounded α (λ x y => R y x)

lemma has_terminal [IsConverseWellFounded _ M.Rel] : ∀ (X : Set M.World), Set.Nonempty X → ∃ t ∈ X, ∀ x ∈ X, ¬(t ≺ x) :=
  WellFounded.wellFounded_iff_has_min.mp (by apply IsWellFounded.wf)

class IsGL (M : Model κ α) extends IsTrans _ M.Rel, IsConverseWellFounded _ M.Rel

class IsFiniteGL (M : Model κ α) extends IsTrans _ M.Rel, Std.Irrefl M.Rel where
  finite : Finite M.World

instance [M.IsFiniteGL] : M.IsGL where
  wf := by apply @Finite.wellFounded_of_trans_of_irrefl M.World (IsFiniteGL.finite);

end Model




variable [Nonempty κ] {M : Model κ α} {A B : Formula α} {Γ Γ' Δ Δ' : FormulaFinset α}

namespace Model.World

variable {M : Model κ α} {x : M.World} {A B : Formula α}

@[grind]
def Forces (x : M.World) : Formula α → Prop
| #a    => M.Val x a
| ⊥     => False
| A 🡒 B => Forces x A → Forces x B
| □A    => ∀ y, x ≺ y → Forces y A
infix:55 " ⊩ " => Forces

abbrev NotForces (x : M.World) (A : Formula α) : Prop := ¬x ⊩ A
infix:55 " ⊮ " => NotForces


@[grind =]
lemma iff_not_forced_box {A : Formula α} : ¬x ⊩ □A ↔ ∃ y, x ≺ y ∧ ¬y ⊩ A := by grind;

@[simp, grind .]
lemma not_forces_bot : x ⊮ ⊥ := by grind;


@[grind]
def ForcesSet (x : M.World) (Γ : FormulaFinset α) : Prop := ∀ A ∈ Γ, x ⊩ A
infix:55 " ⊩ " => ForcesSet

end Model.World



namespace Model

@[grind]
def Validate (M : Model κ α) (A : Formula α) : Prop := ∀ x : M.World, x ⊩ A
infix:50 " ⊧ " => Model.Validate

end Model


end
