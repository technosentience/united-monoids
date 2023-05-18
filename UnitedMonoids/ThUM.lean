import Mathlib.Data.Nat.Basic
import Std.Data.List.Basic
import UnitedMonoids.UniversalAlgebra
import UnitedMonoids.UnitedMonoid
import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LibrarySearch
import Mathlib.Data.List.Sublists


namespace UniversalAlgebra

inductive ThUM : Type _ where
  | empty
  | overlay
  | connect

instance : Signature ThUM where
  arity := fun
    | .empty => 0
    | .overlay => 2
    | .connect => 2

def eqnAddAssoc : Equation ThUM :=
  EQN ThUM CTX 3 ⊢ @[.overlay @[.overlay #0 #1] #2] ≡ @[.overlay #0 @[.overlay #1 #2]]

def eqnAddComm : Equation ThUM :=
  EQN ThUM CTX 2 ⊢ @[.overlay #0 #1] ≡ @[.overlay #1 #0]

def eqnAddZeroLeft : Equation ThUM :=
  EQN ThUM CTX 1 ⊢ @[.overlay @[.empty] #0] ≡ #0

def eqnAddZeroRight : Equation ThUM :=
  EQN ThUM CTX 1 ⊢ @[.overlay #0 @[.empty]] ≡ #0

def eqnMulAssoc : Equation ThUM :=
  EQN ThUM CTX 3 ⊢ @[.connect @[.connect #0 #1] #2] ≡ @[.connect #0 @[.connect #1 #2]]

def eqnMulOneLeft : Equation ThUM :=
  EQN ThUM CTX 1 ⊢ @[.connect @[.empty] #0] ≡ #0

def eqnMulOneRight : Equation ThUM :=
  EQN ThUM CTX 1 ⊢ @[.connect #0 @[.empty]] ≡ #0

def eqnMulDistrLeft : Equation ThUM :=
  EQN ThUM CTX 3 ⊢ @[.connect #0 @[.overlay #1 #2]] ≡ @[.overlay @[.connect #0 #1] @[.connect #0 #2]]

def eqnMulDistrRight : Equation ThUM :=
  EQN ThUM CTX 3 ⊢ @[.connect @[.overlay #0 #1] #2] ≡ @[.overlay @[.connect #0 #2] @[.connect #1 #2]]

def umEqns := [ eqnAddAssoc
    , eqnAddComm
    , eqnAddZeroLeft
    , eqnAddZeroRight
    , eqnMulAssoc
    , eqnMulOneLeft
    , eqnMulOneRight
    , eqnMulDistrLeft
    , eqnMulDistrRight
    ]

instance : Theory ThUM where
  eqns := fun x => x ∈ umEqns

instance [Model ThUM M] : Add M where
  add x y := (⟦ TERM ThUM CTX 2 ⊢ @[.overlay #0 #1]⟧ M) [x, y].get

instance [Model ThUM M] : Zero M where
  zero := (⟦ TERM ThUM CTX 0 ⊢ @[.empty]⟧ M) [].get

instance [Model ThUM M] : Mul M where
  mul x y := (⟦ TERM ThUM CTX 2 ⊢ @[.connect #0 #1]⟧ M) [x, y].get

instance [Model ThUM M] : One M where
  one := (⟦ TERM ThUM CTX 0 ⊢ @[.empty]⟧ M) [].get

theorem fin0_rewrite (f : Fin (arity ThUM.empty) → α) : f = Fin.elim0 := by
  ext i
  fin_cases i 

theorem list_get_rewrite2_arg {α β : Type _} (i : Fin 2) (f : α → β) (x y : α) : f ([x, y].get i) = [f x, f y].get i := by
  fin_cases i <;> simp_all only [List.get]

theorem list_get_rewrite2_fun {α β : Type _} (i : Fin 2) (f g : α → β) (x : α) : [f, g].get i x = [f x, g x].get i := by
  fin_cases i <;> simp_all only [List.get]

theorem list_get_rewrite2_match {α : Type _} (i : Fin 2) (x y : α) : [x, y].get i = match i with | ⟨0, _⟩ => x | ⟨1, _⟩ => y := by
  fin_cases i <;> simp_all only [List.get]

-- instance [Model ThUM M] : AddSemigroup M where
--   add_assoc x y z := by
--     have h := congr_fun (Model.satisfies (M := M) eqnAddAssoc (by simp [Theory.eqns, umEqns]; tauto)) [x, y, z].get
--     rw [HAdd.hAdd, instHAdd, Add.add, instAdd]
--     simp
--     simp [eqnAddAssoc] at h
--     simp_all [interpretTerm]

--     conv =>
--       lhs
--       congr
--       ext i
--       simp [list_get_rewrite2_arg _ (interpretTerm _), interpretTerm, list_get_rewrite2_fun, List.get]; rw [list_get_rewrite2_match]
--       congr
--       ext ih
--       congr
--       ext j
--       simp [list_get_rewrite2_arg _ (interpretTerm _), interpretTerm, list_get_rewrite2_fun, List.get]; rw [list_get_rewrite2_match]
--       rfl
--       rfl

--     conv =>
--       rhs
--       congr
--       ext i
--       simp [list_get_rewrite2_arg _ (interpretTerm _), interpretTerm, list_get_rewrite2_fun, List.get]; rw [list_get_rewrite2_match]
--       congr
--       rfl
--       ext ih
--       congr
--       ext j
--       simp [list_get_rewrite2_arg _ (interpretTerm _), interpretTerm, list_get_rewrite2_fun, List.get]; rw [list_get_rewrite2_match]
--       rfl

--     conv at h =>
--       lhs
--       congr
--       ext i
--       simp [list_get_rewrite2_arg _ (interpretTerm _), interpretTerm, list_get_rewrite2_fun, List.get]; rw [list_get_rewrite2_match]
--       congr
--       ext ih
--       congr
--       ext j
--       simp [list_get_rewrite2_arg _ (interpretTerm _), interpretTerm, list_get_rewrite2_fun, List.get]; rw [list_get_rewrite2_match]
--       rfl
--       rfl

--     conv at h =>
--       rhs
--       congr
--       ext i
--       simp [list_get_rewrite2_arg _ (interpretTerm _), interpretTerm, list_get_rewrite2_fun, List.get]; rw [list_get_rewrite2_match]
--       congr
--       rfl
--       ext ih
--       congr
--       ext j
--       simp [list_get_rewrite2_arg _ (interpretTerm _), interpretTerm, list_get_rewrite2_fun, List.get]; rw [list_get_rewrite2_match]
--       rfl
    
--     assumption

-- instance {M : Type _} [Model ThUM M] : AddMonoid M where
--   zero_add x := by
--     have h := congr_fun (Model.satisfies (M := M) eqnAddZeroLeft (by simp [Theory.eqns, umEqns]; tauto)) [x].get
--     rw [HAdd.hAdd, instHAdd, AddSemigroup.toAdd, Add.add, instAddSemigroup]
--     simp [instAdd]
--     simp [eqnAddZeroLeft] at h
--     simp_all [interpretTerm] 

--     conv =>
--       lhs
--       congr
--       ext i
--       simp [list_get_rewrite2_arg _ (interpretTerm _), interpretTerm, list_get_rewrite2_fun, List.get]; rw [list_get_rewrite2_match]
--       congr
--       ext ih
--       change (⟦ TERM ThUM CTX 0 ⊢ @[.empty]⟧ M) [].get
--       simp [interpretTerm]
--       congr
--       rw [fin0_rewrite (fun i => (⟦List.get [] i⟧M) (List.get []))]
--       rfl
--       rfl
      
--     conv at h =>
--       lhs
--       congr
--       ext i
--       simp [list_get_rewrite2_arg _ (interpretTerm _), interpretTerm, list_get_rewrite2_fun, List.get]; rw [list_get_rewrite2_match]
--       congr
--       ext ih
--       congr
--       rw [fin0_rewrite (fun (i : Fin (@Signature.arity.{0} ThUM (@Theory.toSignature.{0} ThUM instTheoryThUM) ThUM.empty)) =>
--         @interpretTerm ThUM (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) M
--           (@Theory.toSignature.{0} ThUM instTheoryThUM) (@Model.toInterpretation ThUM M instTheoryThUM _)
--           (@List.get.{0} (@Term.{0} ThUM (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) instSignatureThUM)
--             (@List.nil.{0} (@Term.{0} ThUM (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) instSignatureThUM)) i)
--           (@List.get M (@List.cons M x (@List.nil M))))]
--       rfl
--       rfl
    
--     assumption
  
--   add_zero x := sorry

-- instance [Model ThUM M] : AddCommMonoid M where
--   add_comm := sorry

-- instance [Model ThUM M] : Semigroup M where
--   mul_assoc := sorry

-- instance [Model ThUM M] : Monoid M where
--   one_mul := sorry
--   mul_one := sorry

-- instance [Model ThUM M] : UnitedMonoid M where
--   left_distrib := sorry
--   right_distrib := sorry
--   united := rfl

-- instance [UnitedMonoid M] : Interpretation ThUM M where
--   interpret := fun
--     | .empty => 0
--     | .overlay => fun f => f 0 + f 1
--     | .connect => fun f => f 0 * f 1

-- instance [UnitedMonoid M] : Model ThUM M where
--   interpret := fun
--     | .empty => 0
--     | .overlay => fun f => f 0 + f 1
--     | .connect => fun f => f 0 * f 1
--   satisfies eqn h := by
--     simp [Theory.eqns, umEqns] at h
--     rcases h with h | h | h | h | h | h | h | h | h <;> { 
--       subst h
--       ext i
--       simp [interpretTerm]
--       try simp [united, add_assoc, zero_add, add_zero, add_comm, mul_assoc, one_mul, mul_one, left_distrib, right_distrib]
--     }

end UniversalAlgebra

namespace UniversalAlgebra

def ExtThUM := UniversalAlgebra.ThUM

instance : Signature ExtThUM where
  arity := fun
    | .empty => 0
    | .overlay => 2
    | .connect => 2

abbrev ThUMExtension := { xs : List (Equation ExtThUM) // umEqns ⊆ xs }

def ExtFreeModel (ext : ThUMExtension) (V : Type _) := @FreeModel ExtThUM V ⟨(· ∈ ext.1)⟩

def ExtFreeModel.leaf {ext : ThUMExtension} {V : Type _} := @FreeModel.leaf ExtThUM V ⟨(· ∈ ext.1)⟩

def ExtFreeModel.node {ext : ThUMExtension} {V : Type _} := @FreeModel.node ExtThUM V ⟨(· ∈ ext.1)⟩

theorem Ext_no_leaf_equality (ext : ThUMExtension) (v : V)
  (h : ExtFreeModel.node .connect (fun _ => ExtFreeModel.leaf v) = (ExtFreeModel.leaf v : ExtFreeModel ext V)) :
  ∀ (x : ExtFreeModel ext V), ExtFreeModel.node .connect (fun _ => x) = x := by
    intro x
    let f : V → ExtFreeModel ext V := fun _ => x
    let f' := @FreeModel.freeMap ExtThUM V (ExtFreeModel ext V) ⟨(· ∈ ext.1)⟩
      (@FreeModel.instModelFreeModel ExtThUM V ⟨(· ∈ ext.1)⟩) f
    have h' := congr_arg f' h
    simp [FreeModel.freeMap, ExtFreeModel.node, ExtFreeModel.leaf, FreeModel.node, FreeModel.leaf] at h'
    
    conv at h' =>
      lhs
      congr
      rfl
      congr
      rfl
      change Quotient.mk _ ∘ (fun _ => Tree.leaf v)

    rw [finProjectiveLift_mk] at h'
    simp_rw [@Quotient.lift_mk _ _ (@freeModelSetoid ExtThUM V ⟨(· ∈ ext.1)⟩), Tree.freeMap, interpret] at h'
    assumption


end UniversalAlgebra
