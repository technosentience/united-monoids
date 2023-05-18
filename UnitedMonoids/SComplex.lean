import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import UnitedMonoids.UnitedMonoid

structure SComplex (V : Type u) : Type u where
  simplices : Finset (Finset V)
  containment : ∀ S T, S ∈ simplices → T ⊆ S → T ∈ simplices
  contains_zero : ∅ ∈ simplices

namespace SComplex

  def empty : SComplex V := ⟨{ ∅ }, containment, contains_zero⟩
    where
      containment := by intros; simp_all [Finset.subset_empty]
      contains_zero := by simp only [Finset.mem_singleton]

  def singleton [DecidableEq V] (v : V) : SComplex V := ⟨{ ∅, { v } }, containment, by simp⟩
    where
      containment := by
        intros S T h₁ h₂
        simp_all [Finset.mem_insert, Finset.subset_empty]
        rcases h₁ with h₁ | h₁
        simp_all [Finset.subset_empty]
        simp_all [Finset.subset_insert]

  def overlay [DecidableEq V] (X Y : SComplex V) : SComplex V := ⟨X.simplices ∪ Y.simplices, containment, contains_zero⟩
    where
      containment := by
        intros S T h₁ h₂
        simp_all [Finset.mem_union]
        rcases h₁ with h₁ | h₁
        exact .inl $ X.containment S T h₁ h₂
        exact .inr $ Y.containment S T h₁ h₂
      contains_zero := by simp; exact .inl $ X.contains_zero

  def connect [DecidableEq V] (X Y : SComplex V) : SComplex V := ⟨X.simplices.bunionᵢ
    (fun S => Y.simplices.bunionᵢ (fun T => {S ∪ T})), containment, contains_zero⟩
  where
    containment := by
      intros S T h₁ h₂
      simp_all [Finset.mem_bunionᵢ]
      rcases h₁ with ⟨X', h₁, ⟨Y', ⟨h₃, h₄⟩⟩⟩
      have h₅ := X.containment X' (sdiff X' (sdiff S T)) h₁ (by simp_all [Finset.subset_sdiff])
      have h₆ := Y.containment Y' (sdiff Y' (sdiff S T)) h₃ (by simp_all [Finset.subset_sdiff])
      refine ⟨_, h₅, _, h₆, ?_⟩
      subst h₄
      rw [←Finset.union_sdiff_distrib]
      simp_all [Finset.subset_union_left, Finset.subset_union_right]
    contains_zero := by
      simp
      refine ⟨_, X.contains_zero, _, Y.contains_zero, ?_⟩
      simp_all [Finset.subset_empty]

  instance : Zero (SComplex V) := ⟨empty⟩
  instance : One (SComplex V) := ⟨empty⟩
  instance [DecidableEq V] : Add (SComplex V) := ⟨overlay⟩
  instance [DecidableEq V] : Mul (SComplex V) := ⟨connect⟩
  
  @[ext]
  theorem ext (X Y : SComplex V) (h : X.simplices = Y.simplices) : X = Y := by cases X; cases Y; simp_all

  theorem add_assoc [DecidableEq V] (X Y Z : SComplex V) : X + Y + Z = X + (Y + Z) := by
    change overlay (overlay X Y) Z = overlay X (overlay Y Z)
    simp [overlay]

  theorem add_zero [DecidableEq V] (X : SComplex V) : X + 0 = X := by
    change overlay X empty = X
    ext1
    simp [overlay, empty, X.contains_zero]

  theorem zero_add [DecidableEq V] (X : SComplex V) : 0 + X = X := by
    change overlay empty X = X
    ext1
    simp [overlay, empty, X.contains_zero]

  theorem add_comm [DecidableEq V] (X Y : SComplex V) : X + Y = Y + X := by
    change overlay X Y = overlay Y X
    ext1
    simp [overlay, Finset.union_comm]

  theorem mul_assoc [DecidableEq V] (X Y Z : SComplex V) : X * Y * Z = X * (Y * Z) := by
    change connect (connect X Y) Z = connect X (connect Y Z)
    ext1
    simp [connect, Finset.bunionᵢ_bunionᵢ]

  theorem mul_one [DecidableEq V] (X : SComplex V) : X * 1 = X := by
    change connect X empty = X
    ext1
    simp [connect, empty, X.contains_zero]
  
  theorem one_mul [DecidableEq V] (X : SComplex V) : 1 * X = X := by
    change connect empty X = X
    ext1
    simp [connect, empty, X.contains_zero]

  theorem left_distrib [DecidableEq V] (X Y Z : SComplex V) : X * (Y + Z) = X * Y + X * Z := by
    change connect X (overlay Y Z) = overlay (connect X Y) (connect X Z)
    ext1
    simp [connect, overlay, Finset.bunionᵢ_bunionᵢ]
    ext S
    simp
    aesop

  theorem right_distrib [DecidableEq V] (X Y Z : SComplex V) : (X + Y) * Z = X * Z + Y * Z := by
    change connect (overlay X Y) Z = overlay (connect X Z) (connect Y Z)
    ext1
    simp [connect, overlay, Finset.bunionᵢ_bunionᵢ]
    ext S
    simp
    aesop

  instance [DecidableEq V] : UnitedMonoid (SComplex V) := {
    add_assoc := add_assoc,
    add_zero := add_zero,
    zero_add := zero_add,
    add_comm := add_comm,
    mul_assoc := mul_assoc,
    mul_one := mul_one,
    one_mul := one_mul,
    left_distrib := left_distrib,
    right_distrib := right_distrib
    united := by change empty = empty; rfl
  }

end SComplex
