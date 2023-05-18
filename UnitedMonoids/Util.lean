import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Aesop

class Projective (X : Type _) where
  lift {α : Sort u} {β : Sort v} [s : Setoid α] (f : (X → α) → β)
    (h : ∀ (a b : X → α), (∀ x, a x ≈ b x) → f a = f b) (q : X → Quotient s) : β
  lift_mk {α : Sort u} {β : Sort v} [s : Setoid α] (f : (X → α) → β)
    (h : ∀ (a b : X → α), (∀ x, a x ≈ b x) → f a = f b) (q : X → α) : lift f h (Quotient.mk s ∘ q) = f q
  ind {α : Sort u} [s : Setoid α] {motive : (X → Quotient s) → Prop}
    (h : ∀ (a : X → α), motive (Quotient.mk s ∘ a)) (q : X → Quotient s) : motive q

structure finProjectiveData (α : Sort u) (β : Sort v) [s : Setoid α] (n : Nat) where
  f : (Fin n → α) → β
  q : Fin n → Quotient s
  h : ∀ (a b : Fin n → α), (∀ x, a x ≈ b x) → f a = f b

def finProjectiveStep {α : Sort u} {β : Sort v} [s : Setoid α] (n : Nat)
  (data : finProjectiveData α β (n + 1)) : finProjectiveData α β n := {
    f := fun q => Quotient.liftOn (data.q ⟨0, by linarith⟩) (fun a => data.f (
        fun i => match i with
          | ⟨0, _⟩ => a
          | ⟨i + 1, _⟩ => q ⟨i, by linarith⟩
        )
      ) (by
        intros a b h
        simp
        apply data.h
        intro x
        split
        assumption
        apply s.refl
      )
    q := fun ⟨i, _⟩ => data.q ⟨i + 1, by linarith⟩
    h := fun a b h' => by
      simp
      congr
      ext a'
      apply data.h
      intro x
      split
      apply s.refl
      apply (h' ⟨_, by linarith⟩)
  }

def finProjectiveLift {α : Sort u} {β : Sort v} [s : Setoid α] (f : (Fin n → α) → β)
    (h : ∀ (a b : Fin n → α), (∀ x, a x ≈ b x) → f a = f b) (q : Fin n → Quotient s) : β :=
    let data := Nat.decreasingInduction (P := finProjectiveData α β) finProjectiveStep ((by linarith) : 0 ≤ n) { f := f, h := h, q := q }
    data.f Fin.elim0

theorem finProjectiveLift_mk {α : Sort u} {β : Sort v} [s : Setoid α] (f : (Fin n → α) → β)
    (h : ∀ (a b : Fin n → α), (∀ x, a x ≈ b x) → f a = f b) (q : Fin n → α) : finProjectiveLift f h (Quotient.mk s ∘ q) = f q := by
    sorry

theorem finProjectiveInd {α : Sort u} [s : Setoid α] {motive : (Fin n → Quotient s) → Prop}
    (h : ∀ (a : Fin n → α), motive (Quotient.mk s ∘ a)) (q : Fin n → Quotient s) : motive q := by
    sorry

theorem List.sublist_append {l₁ l₂ l₃ : List α} (h : List.Sublist l₁ (l₂ ++ l₃))
  : ∃ l₄ l₅, l₁ = l₄ ++ l₅ ∧ List.Sublist l₄ l₂ ∧ List.Sublist l₅ l₃ := by
  induction l₂ generalizing l₁
  case nil => simp_all; exact ⟨[], l₁, rfl, rfl, h⟩
  case cons hd tl ih =>
    simp_all
    cases h
    case cons h₁ =>
      rcases ih h₁ with ⟨l₄, l₅, h₂, h₃, h₄⟩
      exact ⟨l₄, l₅, h₂, List.Sublist.cons _ h₃, h₄⟩
    case cons₂ l₁ h₁ =>
      rcases ih h₁ with ⟨l₄, l₅, h₂, h₃, h₄⟩
      exact ⟨hd :: l₄, l₅, by simp [h₂], List.Sublist.cons₂ _ h₃, h₄⟩ 
