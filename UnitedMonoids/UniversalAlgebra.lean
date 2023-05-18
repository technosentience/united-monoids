import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic
import UnitedMonoids.Util

namespace UniversalAlgebra

class Signature (S : Type _) where
  arity : S → Nat
export Signature (arity)

attribute [reducible, inline] arity

inductive Term (S : Type _) (ctx : Nat) [Signature S] where
  | var (in_ctx : Fin ctx) : Term S ctx
  | app (op : S) (args : Fin (arity op) → Term S ctx) : Term S ctx

structure Equation (S : Type _) [Signature S] where
  ctx : Nat
  lhs : Term S ctx
  rhs : Term S ctx

class Theory (T : Type _) extends Signature T where
  eqns : Set (Equation T)

class Interpretation (S : outParam (Type _)) (I : Type _) [Signature S] where
  interpret : ∀ (op : S), (Fin (arity op) → I) → I
export Interpretation (interpret)

def interpretTerm (I : Type _) [Signature S] [Interpretation S I] : Term S ctx → (Fin ctx → I) → I
  | .var in_ctx, subst => subst in_ctx
  | .app f args, subst => interpret f (fun i => interpretTerm I (args i) subst)

notation:100 "⟦" t:100 "⟧" I:100  => interpretTerm I t

class Model (T : outParam (Type _)) (M : Type _) [Theory T] extends Interpretation T M where
  satisfies : ∀ eqn ∈ Theory.eqns, ⟦eqn.lhs⟧M = ⟦eqn.rhs⟧M

structure Model.Hom (M N : Type _) [Theory T] [Model T M] [Model T N] where
  f : M → N
  preserves : ∀ (op : T), f ∘ interpret op = interpret op ∘ (f ∘ .)

instance (M N : Type _) [Theory T] [Model T M] [Model T N] : CoeFun (Model.Hom M N) (fun _ => M → N) where
  coe f := f.f

inductive Tree (S X : Type _) [Signature S] where
  | leaf (val : X) : Tree S X
  | node (op : S) (args : Fin (arity op) → Tree S X) : Tree S X

namespace Tree
  instance (S X) [Signature S] : Interpretation S (Tree S X) where
    interpret := node

  def freeMap {S X L : Type _} [Signature S] [Interpretation S L] (inclusion : X → L) : Tree S X → L
    | .leaf val => inclusion val
    | .node op args => interpret op (fun i => freeMap inclusion (args i))

  theorem freeMap_commutes {S X L : Type _} [Signature S] [Interpretation S L] (inclusion : X → L) (t : Term S ctx)
    (subst : Fin ctx → Tree S X) : freeMap inclusion ((⟦t⟧ Tree S X) subst) = (⟦t⟧ L) (freeMap inclusion ∘ subst) := by
    induction t with
    | var in_ctx => rfl
    | app op args ih => simp_rw [freeMap, ih]; rfl
end Tree

inductive FreeModelRel (T X : Type _) [Theory T] : Tree T X → Tree T X → Prop
  | refl (t : Tree T X) : FreeModelRel T X t t
  | symm (rel : FreeModelRel T X t₁ t₂) : FreeModelRel T X t₂ t₁
  | trans (rel₁ : FreeModelRel T X t₁ t₂) (rel₂ : FreeModelRel T X t₂ t₃) : FreeModelRel T X t₁ t₃
  | eqn (in_eqns : eqn ∈ Theory.eqns) (subst : Fin eqn.ctx → Tree T X)
    : FreeModelRel T X ((⟦eqn.lhs⟧ Tree T X) subst) ((⟦eqn.rhs⟧ Tree T X) subst)
  | congr (op : T) (args₁ : Fin (arity op) → Tree T X) (args₂ : Fin (arity op) → Tree T X)
    (rel : ∀ i, FreeModelRel T X (args₁ i) (args₂ i)) : FreeModelRel T X (Tree.node op args₁) (Tree.node op args₂)

theorem FreeModelRel.isEquivalence {T X : Type _} [Theory T] : Equivalence (FreeModelRel T X) :=
  ⟨FreeModelRel.refl, FreeModelRel.symm, FreeModelRel.trans⟩

instance freeModelSetoid (T X : Type _) [Theory T] : Setoid (Tree T X) := ⟨FreeModelRel T X, FreeModelRel.isEquivalence⟩

theorem Tree.freeMap_eqv {T X L : Type _} [Theory T] [Model T L] (inclusion : X → L)
  (t₁ t₂ : Tree T X) (rel : t₁ ≈ t₂) : Tree.freeMap inclusion t₁ = Tree.freeMap inclusion t₂ := by
  induction rel with
  | refl _ => rfl
  | symm rel ih => rw [ih]
  | trans rel₁ rel₂ ih₁ ih₂ => rw [ih₁, ih₂]
  | eqn in_eqns subst =>
     have h := Model.satisfies (M := L) _ in_eqns
     simp_rw [freeMap_commutes, h]
  | congr op args₁ args₂ rel ih =>
    simp [freeMap]
    simp_rw [ih]

abbrev FreeModel (T X : Type _) [Theory T] := Quotient (freeModelSetoid T X)

namespace FreeModel
  def leaf {T X : Type _} [Theory T] (val : X) : FreeModel T X := Quotient.mk _ (.leaf val)

  def node {T X : Type _} [Theory T] (op : T) (args : Fin (arity op) → FreeModel T X) : FreeModel T X :=
    finProjectiveLift (Quotient.mk _ ∘ Tree.node op) (by
      intros a₁ a₂ h
      apply Quotient.sound
      exact FreeModelRel.congr op a₁ a₂ h
    ) args

  instance [Theory T] : Interpretation T (FreeModel T X) where
    interpret op args := node op args

  theorem interpretTerm_commutes {T X : Type _} [Theory T] (t : Term T ctx) (subst : Fin ctx → Tree T X) :
    (⟦t⟧ FreeModel T X) (Quotient.mk _ ∘ subst) = Quotient.mk _ ((⟦t⟧ Tree T X) subst) := by
      induction t with
      | var in_ctx => simp [interpretTerm]
      | app op args ih =>
        simp [interpretTerm, interpret, node]
        simp_rw [ih]
        change (finProjectiveLift _ _ (Quotient.mk (freeModelSetoid T X) ∘ _)) = _
        rw [finProjectiveLift_mk]
        rfl

  instance [Theory T] : Model T (FreeModel T X) where
    satisfies eqn in_eqns := by
      ext subst; revert subst
      apply finProjectiveInd
      intro subst
      simp_rw [interpretTerm_commutes]
      apply Quot.sound
      exact FreeModelRel.eqn in_eqns subst

  def freeMap {T X L : Type _} [Theory T] [Model T L] (inclusion : X → L) : FreeModel T X → L :=
    Quotient.lift (Tree.freeMap inclusion) (Tree.freeMap_eqv inclusion)

  theorem freeMap_preserves {T X L : Type _} [Theory T] [Model T L] (inclusion : X → L) :
    ∀ (op : T), freeMap inclusion ∘ interpret op = interpret op ∘ (freeMap inclusion ∘ ·) := by
      intros op
      ext subst; revert subst
      apply finProjectiveInd
      intro subst
      simp [freeMap, node, interpret, finProjectiveLift_mk]
      rw [←Function.comp.assoc, Quotient.lift_comp_mk]
      simp_rw [Tree.freeMap]
      rfl

  def freeHom {T X L : Type _} [Theory T] [Model T L] (inclusion : X → L) : Model.Hom (FreeModel T X) L :=
    ⟨freeMap inclusion, freeMap_preserves inclusion⟩

  theorem freeMap_commutes {T X L : Type _} [Theory T] [Model T L] (inclusion : X → L) :
    inclusion = freeMap inclusion ∘ leaf := by
      ext val
      simp [freeMap, leaf]
      rfl

  theorem freeMap_unique {T X L : Type _} [Theory T] [Model T L] (inclusion : X → L) :
    ∀ (f : Model.Hom (FreeModel T X) L), f ∘ leaf = inclusion → f = freeMap inclusion := by
      intros f h
      ext t; revert t
      apply Quotient.ind
      intro t
      simp [freeMap]
      induction t with
      | leaf val =>
        have h' := congr_fun h val
        simp [leaf] at h'
        rw [h']
        rfl
      | node op args ih =>
        simp_rw [Tree.freeMap]
        cases' f with f h'
        simp_all
        have h'' := h' op
        simp [interpret] at h''
        have h''' := congr_fun h'' (Quotient.mk (freeModelSetoid T X) ∘ args)
        simp [node] at h'''
        simp_rw [finProjectiveLift_mk] at h'''
        simp at h'''
        rw [h''']
        congr
        ext i
        simp
        rw [ih i]

end FreeModel

declare_syntax_cat algebraic

syntax "@[" term algebraic* "]" : algebraic
syntax "#" term : algebraic
syntax "TERM" term "CTX" term "⊢" algebraic : term
syntax "EQN" term "CTX" term "⊢" algebraic "≡" algebraic : term

macro_rules
  | `(TERM $s CTX $n ⊢ #$t ) => `((Term.var ⟨$t, by linarith⟩ : Term $s $n))
  | `(TERM $s CTX $n ⊢ @[ $op $args:algebraic* ]) => do
    let args' ← args.mapM (fun a => `(TERM $s CTX $n ⊢ $a:algebraic))
    `((Term.app $op [$args',*].get : Term $s $n))
  | `(EQN $s CTX $n ⊢ $lhs:algebraic ≡ $rhs:algebraic) => do
    let lhs' ← `(TERM $s CTX $n ⊢ $lhs:algebraic)
    let rhs' ← `(TERM $s CTX $n ⊢ $rhs:algebraic)
    `({ ctx := $n, lhs := $lhs', rhs := $rhs' })

end UniversalAlgebra
