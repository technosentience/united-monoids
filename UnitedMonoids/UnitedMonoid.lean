import Mathlib.Data.Nat.Basic
import Std.Data.List.Basic
import UnitedMonoids.UniversalAlgebra
import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LibrarySearch
import Mathlib.Data.List.Sublists
import Mathlib.Algebra.GroupPower.Ring

class UnitedMonoid (α : Type u) extends Monoid α, AddCommMonoid α, Distrib α where
  united : (0 : α) = (1 : α)

export UnitedMonoid (united)

namespace UnitedMonoid

  def ε [UnitedMonoid α] : α := 0
  
  theorem add_idempotent [UnitedMonoid α] (a : α) : a + a = a := by
    rw [←mul_one a, ←left_distrib, ←united, add_zero]

  theorem containment_left [UnitedMonoid α] (a b : α) : a * b + a = a * b := by
    nth_rewrite 2 [←mul_one a]
    rw [←left_distrib, ←united, add_zero]

  theorem containment_right [UnitedMonoid α] (a b : α) : a * b + b = a * b := by
    nth_rewrite 2 [←one_mul b]
    rw [←right_distrib, ←united, add_zero]

  theorem idempotence_collapses_connect [UnitedMonoid α] (h : ∀ a : α, a * a = a) (a b : α) : a * b = a + b := by
    have h₀ : (a + b) * (a + b) = a + b := h (a + b)
    have h₁ : (a + b) * (a + b) = a * b + b * a := by 
      simp_rw [left_distrib, right_distrib, h, add_comm a (b * a), containment_right, add_comm]
    have h₂ : a * b = a * b + a + b := by simp_rw [containment_left, containment_right]
    have h₃ : a * b + (a + b) = a + b := by rw [←h₀, h₁, ←add_assoc, add_idempotent]
    rw [h₂, add_assoc, h₃]
    
  structure Hom (α β : Type _) [UnitedMonoid α] [UnitedMonoid β] where
    toFun : α → β
    preserves_empty : toFun ε = ε
    preserves_overlay : toFun (a + b) = toFun a + toFun b
    preserves_connect : toFun (a * b) = toFun a * toFun b

end UnitedMonoid

inductive TreeUM (V : Type _) where
  | empty
  | leaf (v : V)
  | overlay (t₁ t₂ : TreeUM V)
  | connect (t₁ t₂ : TreeUM V)

namespace TreeUM
  inductive Rel {V : Type _} : TreeUM V → TreeUM V → Prop
    | refl (t : TreeUM V) : Rel t t
    | symm (rel : Rel t₁ t₂) : Rel t₂ t₁
    | trans (rel₁ : Rel t₁ t₂) (rel₂ : Rel t₂ t₃) : Rel t₁ t₃
    | overCongr (rel₁ : Rel t₁ t₂) (rel₃ : Rel t₃ t₄) : Rel (overlay t₁ t₃) (overlay t₂ t₄)
    | connCongr (rel₁ : Rel t₁ t₂) (rel₃ : Rel t₃ t₄) : Rel (connect t₁ t₃) (connect t₂ t₄)
    | overAssoc (t₁ t₂ t₃ : TreeUM V) : Rel (overlay (overlay t₁ t₂) t₃) (overlay t₁ (overlay t₂ t₃))
    | overComm (t₁ t₂ : TreeUM V) : Rel (overlay t₁ t₂) (overlay t₂ t₁)
    | overEmptyLeft (t : TreeUM V) : Rel (overlay empty t) t
    | overEmptyRight (t : TreeUM V) : Rel (overlay t empty) t
    | connAssoc (t₁ t₂ t₃ : TreeUM V) : Rel (connect (connect t₁ t₂) t₃) (connect t₁ (connect t₂ t₃))
    | connEmptyLeft (t : TreeUM V) : Rel (connect empty t) t
    | connEmptyRight (t : TreeUM V) : Rel (connect t empty) t
    | connDistrLeft (t₁ t₂ t₃ : TreeUM V) : Rel (connect t₁ (overlay t₂ t₃)) (overlay (connect t₁ t₂) (connect t₁ t₃))
    | connDistrRight (t₁ t₂ t₃ : TreeUM V) : Rel (connect (overlay t₁ t₂) t₃) (overlay (connect t₁ t₃) (connect t₂ t₃))

  theorem Rel.isEquivalence : @Equivalence (TreeUM V) Rel := ⟨refl, symm, trans⟩

  instance setoid (V : Type _) : Setoid (TreeUM V) := ⟨Rel, Rel.isEquivalence⟩

  theorem Rel.overIdemp {V : Type _} (t : TreeUM V) : Rel (overlay t t) t := by
    refine Rel.trans (Rel.overCongr (Rel.connEmptyRight _).symm (Rel.connEmptyRight _).symm) ?_
    refine Rel.trans (Rel.connDistrLeft _ _ _).symm ?_
    refine Rel.trans (Rel.connCongr (Rel.refl _) (Rel.overEmptyLeft _)) ?_
    exact Rel.connEmptyRight _

  theorem Rel.containLeft {V : Type _} (t₁ t₂ : TreeUM V) : Rel (overlay (connect t₁ t₂) t₁) (connect t₁ t₂) := by
    refine Rel.trans (Rel.overCongr (Rel.refl _) (Rel.connEmptyRight _).symm) ?_
    refine Rel.trans (Rel.connDistrLeft _ _ _).symm ?_
    exact Rel.connCongr (Rel.refl _) (Rel.overEmptyRight _)

  theorem Rel.containRight {V : Type _} (t₁ t₂ : TreeUM V) : Rel (overlay (connect t₁ t₂) t₂) (connect t₁ t₂) := by
    refine Rel.trans (Rel.overCongr (Rel.refl _) (Rel.connEmptyLeft _).symm) ?_
    refine Rel.trans (Rel.connDistrRight _ _ _).symm ?_
    exact Rel.connCongr (Rel.overEmptyRight _) (Rel.refl _)

  inductive IsSimplex : TreeUM V → Prop
    | empty : IsSimplex empty
    | connect (v : V) {t : TreeUM V} (h : IsSimplex t) : IsSimplex (connect (leaf v) t)

  abbrev Simplex V := { t : TreeUM V // IsSimplex t }

  inductive IsNF₁ : TreeUM V → Prop
    | simp {t : TreeUM V} (h : IsSimplex t) : IsNF₁ t
    | overlay {t₁ t₂ : TreeUM V} (h₁ : IsNF₁ t₁) (h₂ : IsNF₁ t₂) : IsNF₁ (overlay t₁ t₂)

  abbrev NF₁ V := { t : TreeUM V // IsNF₁ t }

  def lconn (v : V) : NF₁ V → NF₁ V
    | ⟨empty, _⟩ => ⟨connect (leaf v) empty, .simp (.connect v .empty)⟩
    | ⟨connect (leaf v') h, _⟩ => ⟨connect (leaf v) (connect (leaf v') h), .simp (.connect v (by {
      next h => cases h; assumption
    }))⟩
    | ⟨overlay t₁ t₂, h⟩ =>
      let ⟨t₁', h₁⟩ := lconn v ⟨t₁, by {cases h; next h => { cases h } ; next h => assumption }⟩
      let ⟨t₂', h₂⟩ := lconn v ⟨t₂, by {cases h; next h => { cases h } ; next h => assumption }⟩
      ⟨overlay t₁' t₂', by
      cases h
      next h => { cases h }
      next h₁ h₂ =>
        apply IsNF₁.overlay
        assumption
        assumption
    ⟩
  
  theorem lconn_rel (v : V) : (t : NF₁ V) → Rel (connect (leaf v) t.val) (lconn v t).val
    | ⟨empty, _⟩ => by simp_all [lconn]; apply Rel.refl
    | ⟨connect (leaf v') h, _⟩ => by simp_all [lconn]; apply Rel.refl
    | ⟨overlay t₁ t₂, h⟩ =>
      have h₁ := lconn_rel v ⟨t₁, by {cases h; next h => { cases h } ; next h => assumption }⟩
      have h₂ := lconn_rel v ⟨t₂, by {cases h; next h => { cases h } ; next h => assumption }⟩
      by
        simp_all [lconn]
        have rel₁ := Rel.connDistrLeft (leaf v) t₁ t₂
        apply Rel.trans rel₁
        apply Rel.overCongr
        assumption
        assumption

  def connect' : TreeUM V → NF₁ V → NF₁ V
    | empty, t => t
    | leaf v', t => lconn v' t
    | connect t₁ t₂, t₃ => connect' t₁ (connect' t₂ t₃)
    | overlay t₁ t₂, t₃ =>
      let ⟨t₁', h₁⟩ := connect' t₁ t₃
      let ⟨t₂', h₂⟩ := connect' t₂ t₃
      ⟨overlay t₁' t₂', by apply IsNF₁.overlay; assumption; assumption⟩

  theorem connect'_rel (t₁ : TreeUM V) (t₂ : NF₁ V) : Rel (connect t₁ t₂.val) (connect' t₁ t₂).val := by
    induction t₁ generalizing t₂
    case empty => simp [connect', Rel.symm, Rel.connEmptyLeft]
    case leaf => simp [connect',Rel.symm, lconn_rel]
    case overlay t₃ t₄ ih₁ ih₂ =>
      simp [connect']
      have rel₁ := Rel.connDistrRight t₃ t₄ t₂
      apply Rel.trans rel₁
      apply Rel.overCongr
      simp [*]
      simp [*]
    case connect t₃ t₄ ih₁ ih₂ =>
      simp [connect']
      have rel₁ := Rel.connAssoc t₃ t₄ t₂
      apply Rel.trans rel₁
      apply Rel.trans _ (ih₁ (connect' t₄ t₂))
      apply Rel.connCongr
      apply Rel.refl
      apply ih₂      

   def toNF₁ : TreeUM V → NF₁ V
    | empty => ⟨.empty, .simp .empty⟩
    | leaf v => ⟨connect (leaf v) empty, .simp (.connect v .empty)⟩
    | overlay t₁ t₂ =>
      let ⟨t₁', h₁⟩ := toNF₁ t₁
      let ⟨t₂', h₂⟩ := toNF₁ t₂
      ⟨overlay t₁' t₂', by apply IsNF₁.overlay; assumption; assumption⟩
    | connect t₁ t₂ => connect' t₁ (toNF₁ t₂)

  theorem toNF₁_rel (t : TreeUM V) : Rel t (toNF₁ t).val := by
    induction t
    case empty => simp [toNF₁, Rel.refl]
    case leaf => simp [toNF₁, Rel.symm, Rel.connEmptyRight]
    case overlay => simp [toNF₁, Rel.overCongr, *]
    case connect t₁ t₂ _ ih₂ =>
      simp [toNF₁]
      have rel₁ := Rel.connCongr (Rel.refl t₁) ih₂
      apply Rel.trans rel₁
      apply connect'_rel

  inductive IsNF₂ : TreeUM V → Prop
    | empty : IsNF₂ empty
    | overlay {s t : TreeUM V} (h₁ : IsSimplex s) (h₂ : IsNF₂ t) : IsNF₂ (overlay s t)

  def NF₂ V := {t : TreeUM V // IsNF₂ t}

  namespace NF₂
    def ofList : List (Simplex V) → NF₂ V
      | [] => ⟨empty, .empty⟩
      | s :: ss => ⟨_, .overlay s.property (ofList ss).2⟩

    def toList' : (t : TreeUM V) → IsNF₂ t → List (Simplex V)
      | empty, _ => []
      | overlay s t, h => ⟨s, by {cases h; assumption}⟩ :: toList' t (by {cases h; assumption})

    def toList : NF₂ V → List (Simplex V) := fun ⟨t, h⟩ => toList' t h

    theorem toList_ofList (ss : List (Simplex V)) : toList (ofList ss) = ss := by
      induction ss
      case nil => simp [ofList, toList, toList']
      case cons head tail ih =>
        generalize h : ofList tail = t
        rw [h] at ih
        simp [ofList, toList]
        simp_rw [h]
        simp [toList']
        simp [toList] at ih
        split at ih
        simp
        assumption
    
    theorem ofList_toList (t : NF₂ V) : ofList (toList t) = t := by
      rcases t with ⟨val, property⟩
      induction property
      case empty => simp [ofList, toList]
      case overlay => simp_all [ofList, toList, toList']
    
    theorem overlay_ofList_eq_cons_ofList (s : Simplex V) (ss : List (Simplex V)) :
      ofList (s :: ss) = ⟨overlay s (ofList ss).val, .overlay s.property (ofList ss).2⟩ := by simp [ofList]
    
    theorem ofList_cons_cons (s : Simplex V) (ss : List (Simplex V)) :
      Rel (ofList (s :: s :: ss)).val (ofList (s :: ss)).val := by
        simp_rw [overlay_ofList_eq_cons_ofList]
        refine Rel.trans (Rel.overAssoc _ _ _).symm ?_
        refine Rel.overCongr ?_ (Rel.refl _)
        apply Rel.overIdemp

    theorem ofList_cons_swap (s₁ s₂ : Simplex V) (ss : List (Simplex V)) :
      Rel (ofList (s₁ :: s₂ :: ss)).val (ofList (s₂ :: s₁ :: ss)).val := by
        simp_rw [overlay_ofList_eq_cons_ofList]
        refine Rel.trans ?_ (Rel.overAssoc _ _ _)
        refine Rel.trans (Rel.overAssoc _ _ _).symm ?_
        refine Rel.overCongr ?_ (Rel.refl _)
        apply Rel.overComm

    theorem ofList_cons_mem (s : Simplex V) (ss : List (Simplex V)) (h : s ∈ ss) :
      Rel (ofList (s :: ss)).val (ofList ss).val := by
        induction h
        case head => apply ofList_cons_cons
        case tail ih =>
          refine Rel.trans (ofList_cons_swap _ _ _) ?_
          simp_rw [overlay_ofList_eq_cons_ofList]
          exact Rel.overCongr (Rel.refl _) ih

    theorem ofList_dedup [DecidableEq (Simplex V)] (ss : List (Simplex V)) :
      Rel (ofList ss.dedup).val (ofList ss).val := by
      induction ss
      case nil => simp [ofList, Rel.refl]
      case cons hd tl ih =>
        by_cases hd ∈ tl
        case pos =>
          rw [List.dedup_cons_of_mem h]
          refine Rel.trans ih ?_
          exact (ofList_cons_mem _ _ h).symm
        case neg =>
          rw [List.dedup_cons_of_not_mem h]
          simp_rw [overlay_ofList_eq_cons_ofList]
          exact Rel.overCongr (Rel.refl _) ih

    theorem ofList_perm (ss₁ ss₂ : List (Simplex V)) (h : ss₁ ~ ss₂) :
      Rel (ofList ss₁).val (ofList ss₂).val := by
      induction h
      case nil => simp [ofList, Rel.refl]
      case cons x l₁ l₂ h' ih =>
        simp_rw [overlay_ofList_eq_cons_ofList]
        exact Rel.overCongr (Rel.refl _) ih
      case swap x y l => exact ofList_cons_swap _ _ _
      case trans ih₁ ih₂ => exact Rel.trans ih₁ ih₂

    theorem overlay_ofList_append (ss₁ ss₂ : List (Simplex V)) :
      Rel (overlay (ofList ss₁).val (ofList ss₂).val) (ofList (ss₁ ++ ss₂)).val := by
      induction ss₁
      case nil => simp [ofList, Rel.overEmptyLeft]
      case cons hd tl ih =>
        simp_rw [List.cons_append, overlay_ofList_eq_cons_ofList]
        refine Rel.trans (Rel.overAssoc _ _ _) ?_
        exact Rel.overCongr (Rel.refl _) ih

    def bind (t : NF₂ V) (f : Simplex V → NF₂ V) : NF₂ V := ofList (t.toList.bind (toList ∘ f))

    theorem bind_rel (t : NF₂ V) (f : Simplex V → NF₂ V) (h : ∀ s, Rel s.val (f s).val) : Rel t.val (t.bind f).val := by
      generalize h₀ : t.toList = ss
      rw [←ofList_toList t, h₀]
      clear h₀ t
      induction ss
      case nil => simp [ofList, toList, bind, Rel.refl]
      case cons hd tl ih =>
        simp [bind, toList_ofList]
        simp_rw [overlay_ofList_eq_cons_ofList]
        refine Rel.trans ?_ (overlay_ofList_append _ _)
        apply Rel.overCongr
        simp [ofList_toList, h]
        simp [bind, toList_ofList] at ih
        exact ih

    def HasSimplex (s : Simplex V) (t : NF₂ V) : Prop := s ∈ t.toList

    instance : Membership (Simplex V) (NF₂ V) := ⟨HasSimplex⟩

    theorem mem_ofList_mem : s ∈ ss ↔ s ∈ ofList ss := by
      generalize h₀ : ofList ss = t
      rw [←toList_ofList ss, h₀]
      rfl

    theorem mem_bind {t : NF₂ V} : s ∈ t.bind f ↔ ∃ s' ∈ t, s ∈ f s' := by
      constructor
      · intro h
        simp [bind, ←mem_ofList_mem] at h     
        rcases h with ⟨s', h₀, h₁⟩
        use ⟨s', h₀⟩
        assumption
      · intro h
        simp [bind, ←mem_ofList_mem]
        rcases h with ⟨s', h₀, h₁⟩
        use s'.val
        use s'.property
        constructor <;> assumption

    theorem toList_overlay (s : Simplex V) (t : NF₂ V)
      : NF₂.toList ⟨overlay s.val t.val, .overlay s.property t.property⟩ = s :: t.toList := rfl

    theorem mem_overlay (s s' : Simplex V) (t : NF₂ V)
      : Membership.mem (self := instMembershipSimplexNF₂) 
      s (⟨overlay s'.val t.val, .overlay s'.property t.property⟩ : NF₂ V) ↔ s = s' ∨ s ∈ t := by
      simp_rw [Membership.mem, HasSimplex, toList_overlay]
      simp

  end NF₂

  namespace Simplex
    def ofList : List V → Simplex V
      | [] => ⟨empty, .empty⟩
      | v :: vs => ⟨_, .connect v (ofList vs).2⟩

    def toList : Simplex V → List V
      | ⟨empty, _⟩ => []
      | ⟨connect (leaf v) t, h⟩ => v :: toList ⟨t, by {cases h; assumption}⟩
  
    theorem toList_ofList (vs : List V) : toList (ofList vs) = vs := by
      induction vs
      case nil => simp [ofList, toList]
      case cons => simp [ofList, toList, *]
    
    theorem ofList_toList (t : Simplex V) : ofList (toList t) = t := by
      rcases t with ⟨val, property⟩
      induction property
      case empty => simp [ofList, toList]
      case connect => simp [ofList, toList, *]

    theorem ofList_Injective : Function.Injective (Simplex.ofList : List V → Simplex V) := by
      intro vs₁ vs₂ h
      rw [←toList_ofList vs₁, ←toList_ofList vs₂, h]

    theorem toList_Injective : Function.Injective (Simplex.toList : Simplex V → List V) := by
      intro t₁ t₂ h
      rw [←ofList_toList t₁, ←ofList_toList t₂, h]

    def subsimplices (s : Simplex V) : List (Simplex V) :=
      s.toList.sublists.map ofList

    def subsimplexAbsorption {vs₁ vs₂ : List V} (h : List.Sublist vs₁ vs₂)
      : Rel (overlay (ofList vs₁).val (ofList vs₂).val) (ofList vs₂).val := by
      induction h
      case slnil => simp [ofList, Rel.overIdemp]
      case cons vs₁ vs₂ v _ ih =>
        simp [ofList]
        have rel₁ := Rel.containRight (leaf v) (ofList vs₂)
        refine Rel.trans ?_ rel₁
        refine Rel.trans ?_ (Rel.overComm _ _)
        have rel₂ := Rel.trans (Rel.overComm _ _) rel₁
        refine Rel.trans (Rel.overCongr (Rel.refl _) rel₂.symm) ?_
        refine Rel.trans (Rel.overAssoc _ _ _).symm ?_
        exact Rel.trans (Rel.overCongr ih (Rel.refl _)) (Rel.refl _)
      case cons₂ vs₁ vs₂ v _ ih =>
        simp [ofList]
        refine Rel.trans ?_ (Rel.connCongr (Rel.refl _) ih)
        exact (Rel.connDistrLeft _ _ _).symm

    def toNF₂ (s : Simplex V) : NF₂ V :=
      NF₂.ofList s.subsimplices
  
    theorem toNF₂_rel' (s : Simplex V) : Rel s.val (overlay (toNF₂ s).val s.val) := by
      generalize h₀ : toList s = vs
      rw [←ofList_toList s, h₀]
      simp [toNF₂]
      generalize h₁ : subsimplices (ofList vs) = ss
      have h₂ : List.Sublist ss (subsimplices (ofList vs)) := by simp only [h₁, List.Sublist.refl]
      clear h₁
      induction ss
      case nil => simp [ofList, NF₂.ofList, Rel.symm, Rel.overEmptyLeft]
      case cons head tail ih =>
        specialize ih (List.sublist_of_cons_sublist h₂)
        simp [NF₂.ofList]
        refine Rel.trans ih ?_
        have h₃ := List.Sublist.subset h₂
        have h₄ : head ∈ subsimplices (ofList vs) := h₃ (by simp)
        simp [subsimplices] at h₄
        rcases h₄ with ⟨a, h₄, h₅⟩
        rw [toList_ofList] at h₄
        rw [←h₅]
        have rel₁ := subsimplexAbsorption h₄
        have rel₂ := Rel.overCongr (Rel.refl (NF₂.ofList tail).val) rel₁
        refine Rel.trans rel₂.symm ?_
        refine Rel.trans ?_ (Rel.overCongr (Rel.overComm _ _) (Rel.refl _))
        exact (Rel.overAssoc _ _ _).symm
      done

    theorem toNF₂_rel (s : Simplex V) : Rel s.val (toNF₂ s).val := by
      refine Rel.trans (toNF₂_rel' s) ?_
      refine Rel.trans (Rel.overComm _ _) ?_
      simp [toNF₂]
      have h₁ := NF₂.overlay_ofList_eq_cons_ofList s (subsimplices s)
      have h₂ := congrArg (·.val) h₁
      simp at h₂
      rw [←h₂]
      apply NF₂.ofList_cons_mem
      generalize h₃ : toList s = vs
      rw [←ofList_toList s, h₃]
      simp [subsimplices]
      use vs
      constructor
      simp [toList_ofList, List.Sublist.refl]
      rfl

    theorem sublist_mem (s₁ s₂ : Simplex V) : List.Sublist s₁.toList s₂.toList ↔ s₁ ∈ s₂.toNF₂ := by
      constructor
      · intro h
        simp [toNF₂, subsimplices, Membership.mem, NF₂.HasSimplex, NF₂.toList_ofList]
        change s₁ ∈ (List.map ofList (List.sublists (toList s₂)))
        simp
        use (toList s₁)
        constructor
        assumption
        simp [ofList_toList]
      · intro h
        simp [toNF₂, subsimplices, Membership.mem, NF₂.HasSimplex, NF₂.toList_ofList] at h
        change s₁ ∈ (List.map ofList (List.sublists (toList s₂))) at h
        simp at h
        rcases h with ⟨vs, h₁, h₂⟩
        rwa [←h₂, toList_ofList]

    instance [DecidableEq V] : DecidableEq (Simplex V) := fun s₁ s₂ =>
      match decEq s₁.toList s₂.toList with
      | isTrue h => isTrue (by rw [←ofList_toList s₁, ←ofList_toList s₂, h])
      | isFalse h => isFalse (fun h' => h (by rw [←ofList_toList s₁, ←ofList_toList s₂, h']))

    theorem toNF₁_eq (s : Simplex V) : s.val.toNF₁.val = s.val := by
      rcases s with ⟨t, prop⟩
      induction prop
      case empty => simp [toNF₁]
      case connect v t h₁ h₂ =>
        have h₃ : t.toNF₁ = ⟨t, .simp h₁⟩ := by ext; assumption
        simp [toNF₁, connect', h₃]
        cases t
        case empty => simp [lconn]
        case leaf => contradiction
        case overlay => contradiction
        case connect t₁ t₂ =>
          cases t₁
          case empty => contradiction
          case leaf => simp [lconn]
          case overlay => contradiction
          case connect => contradiction

  end Simplex

  theorem NF₂.toNF₁_eq' (t : NF₂ V) : t.val.toNF₁.val = t.val := by
    rcases t with ⟨t, prop⟩
    induction prop
    case empty => simp [toNF₁]
    case overlay s t h₁ h₂ ih => simp [toNF₁]; exact ⟨Simplex.toNF₁_eq ⟨s, h₁⟩, ih⟩ 

  theorem NF₂.isNF₁ (t : NF₂ V) : IsNF₁ t.val := by
    rw [←toNF₁_eq']
    exact (toNF₁ t.val).property
  
  theorem NF₂.toNF₁_eq (t : NF₂ V) : t.val.toNF₁ = ⟨t.val, NF₂.isNF₁ t⟩ := by ext; simp [NF₂.toNF₁_eq']
   

  def NF₁.simplices : NF₁ V → List (Simplex V)
    | ⟨.empty, _⟩ => [⟨empty, .empty⟩]
    | ⟨s@(.connect _ _), h⟩ => [⟨s, by { rename_i h'; subst h'; cases h; assumption }⟩]
    | ⟨.overlay t₁ t₂, h⟩ =>
         simplices ⟨t₁, by {cases h; next h => { cases h }; assumption }⟩
      ++ simplices ⟨t₂, by {cases h; next h => { cases h }; assumption }⟩
    
  theorem NF₂.simplices_eq (t : NF₂ V) (s : Simplex V) :
    s ∈ (NF₁.simplices ⟨t.val, NF₂.isNF₁ t⟩) ↔ (s ∈ t ∨ s = ⟨empty, .empty⟩) := by
    rcases t with ⟨t, prop⟩
    induction prop
    case empty => simp_rw [NF₁.simplices, List.mem_singleton, Membership.mem, HasSimplex, toList, toList']; simp
    case overlay s' t h₁ h₂ ih =>
      simp_rw [NF₁.simplices, List.mem_append] at *
      simp_rw [ih]
      rw [mem_overlay s ⟨s', h₁⟩ ⟨t, h₂⟩]
      cases h₁
      case empty => simp [NF₁.simplices]; aesop
      case connect => simp [NF₁.simplices]; aesop

  def simplices_rel (t : NF₁ V) : Rel t.val (NF₂.ofList t.simplices).val := by
    rcases t with ⟨val, prop⟩
    simp
    induction val
    case empty => simp [NF₂.ofList, Rel.symm, Rel.overEmptyLeft]
    case leaf => rcases prop with ⟨h⟩; cases h
    case connect t₁ t₂ _ _ =>
      simp [NF₁.simplices, NF₂.ofList]
      exact (Rel.overEmptyRight _).symm
    case overlay t₁ t₂ ih₁ ih₂ =>
      cases prop
      case simp h => cases h
      case overlay h₁ h₂ =>
        specialize ih₁ h₁
        specialize ih₂ h₂
        simp [NF₁.simplices]
        refine Rel.trans (Rel.overCongr ih₁ ih₂) ?_
        exact NF₂.overlay_ofList_append _ _
         

  def NF₁.toNF₂ (t : NF₁ V) : NF₂ V := NF₂.ofList t.simplices

  theorem NF₁.toNF₂_nonempty (t : NF₁ V) : t.toNF₂.toList ≠ [] := by
    intro h
    simp [NF₁.toNF₂, NF₁.simplices] at h
    rcases t with ⟨val, prop⟩
    induction val
    case empty => contradiction
    case leaf => contradiction
    case connect => simp [simplices] at h; contradiction
    case overlay ih =>
      simp [simplices, NF₂.toList_ofList] at h;
      apply ih
      · simp [NF₂.toList_ofList, h]
      · cases prop
        · contradiction
        · assumption 

  theorem NF₁.toNF₂_rel (t : NF₁ V) : Rel t.val t.toNF₂.val := simplices_rel t

  def IsNF₃ (t : NF₂ V) := ∀ s₁ s₂, List.Sublist s₁.toList s₂.toList → s₂ ∈ t → s₁ ∈ t
  
  def NF₂.toNF₃ (t : NF₂ V) : NF₂ V := t.bind Simplex.toNF₂

  theorem NF₂.toNF₃_nonempty (t : NF₁ V) : t.toNF₂.toNF₃.toList ≠ [] := by
    intro h
    simp_rw [toNF₃, bind, toList_ofList, List.bind_eq_nil] at h
    rcases List.exists_mem_of_ne_nil _ (NF₁.toNF₂_nonempty t) with ⟨s, h₁⟩
    specialize h s h₁
    simp [Simplex.toNF₂, toList_ofList, Simplex.subsimplices] at h
    have h₂ := List.length_sublists (Simplex.toList s) |>.symm
    rw [h] at h₂
    simp at h₂
    rw [pow_eq_zero_iff'] at h₂
    cases h₂
    contradiction

  theorem NF₂.toNF₃_rel (t : NF₂ V) : Rel t.val (t.toNF₃.val) := by simp [NF₂.toNF₃]; exact bind_rel _ _ Simplex.toNF₂_rel

  theorem NF₂.toNF₃_isNF₃ (t : NF₂ V) : IsNF₃ t.toNF₃ := by
    dsimp [NF₂.toNF₃, IsNF₃]
    intro s₁ s₂ h₁ h₂
    rw [mem_bind] at h₂ ⊢
    rcases h₂ with ⟨s₃, h₃, h₄⟩
    use s₃
    rw [←Simplex.sublist_mem] at *
    constructor
    assumption
    exact List.Sublist.trans h₁ h₄

  def IsNF₄ (t : NF₂ V) := t.toList.Nodup

  def NF₂.toNF₄ [DecidableEq (Simplex V)] (t : NF₂ V) : NF₂ V := NF₂.ofList t.toList.dedup

  theorem NF₂.toNF₃_toNF₄_nonempty [DecidableEq (Simplex V)] (t : NF₁ V) : t.toNF₂.toNF₃.toNF₄.toList ≠ [] := by
    rcases List.exists_mem_of_ne_nil _ (NF₂.toNF₃_nonempty t) with ⟨s, h₁⟩
    apply List.ne_nil_of_mem (a := s)
    simp_rw [toNF₄, toList_ofList, List.mem_dedup]
    assumption

  theorem NF₂.isNF₄_toNF₄ [DecidableEq (Simplex V)] (t : NF₂ V) : IsNF₄ t.toNF₄ := by
    dsimp [IsNF₄]
    rw [NF₂.toNF₄, toList_ofList]
    exact List.nodup_dedup _

  theorem NF₂.isNF₃_toNF₄ [DecidableEq (Simplex V)] {t : NF₂ V} (h : IsNF₃ t) : IsNF₃ t.toNF₄ := by
    generalize h₀ : t.toList = ss
    rw [←ofList_toList t, h₀] at h ⊢
    clear t h₀
    dsimp [toNF₄, IsNF₃] at *
    intro s₁ s₂ h₁ h₂
    specialize h s₁ s₂ h₁
    simp_all [toList_ofList, ←mem_ofList_mem, List.mem_dedup]

  theorem NF₂.toNF₄_rel [DecidableEq (Simplex V)] (t : NF₂ V) : Rel t.val t.toNF₄.val := by
    generalize h₀ : t.toList = ss
    dsimp [toNF₄]
    rw [←ofList_toList t, h₀]
    clear t h₀
    simp [toList_ofList]
    exact (ofList_dedup _).symm

  def NF (V : Type _) := { t : NF₂ V // IsNF₃ t ∧ IsNF₄ t ∧ t.toList ≠ [] }  

  def toNF [DecidableEq V] (t : TreeUM V) : NF V := ⟨t.toNF₁.toNF₂.toNF₃.toNF₄, by
    refine ⟨?_, ?_, ?_⟩
    · apply NF₂.isNF₃_toNF₄
      apply NF₂.toNF₃_isNF₃
    · apply NF₂.isNF₄_toNF₄
    · apply NF₂.toNF₃_toNF₄_nonempty
  ⟩

  def NF₁.toNF [DecidableEq V] (t : NF₁ V) : NF V := ⟨t.toNF₂.toNF₃.toNF₄, by
    refine ⟨?_, ?_, ?_⟩
    · apply NF₂.isNF₃_toNF₄
      apply NF₂.toNF₃_isNF₃
    · apply NF₂.isNF₄_toNF₄
    · apply NF₂.toNF₃_toNF₄_nonempty
  ⟩

  def toNF_rel [DecidableEq V] (t : TreeUM V) : Rel t (toNF t).val.val := by
    dsimp [toNF]
    refine Rel.trans ?_ (NF₂.toNF₄_rel _)
    refine Rel.trans ?_ (NF₂.toNF₃_rel _)
    refine Rel.trans ?_ (NF₁.toNF₂_rel _)
    exact toNF₁_rel _

  theorem toNF_equiv' [DecidableEq V] (s : Simplex V) (t : NF₁ V) :
    s ∈ t.toNF.val ↔ s ∈ List.bind t.simplices Simplex.subsimplices := by
    simp only [NF₁.toNF, NF₂.toNF₃, NF₂.bind, NF₁.toNF₂, NF₁.simplices._eq_2, NF₂.toList_ofList, Simplex.toNF₂,
      Function.comp, List.cons_bind, Function.comp_apply, List.nil_bind, List.append_nil, NF₂.ofList_toList, NF₂.toNF₄._eq_1,
      ←NF₂.mem_ofList_mem, List.mem_dedup]

  theorem toNF_equiv [DecidableEq V] (s : Simplex V) (t : TreeUM V) :
    s ∈ t.toNF.val ↔ s ∈ List.bind t.toNF₁.simplices Simplex.subsimplices := by 
    change s ∈ t.toNF₁.toNF.val ↔ s ∈ List.bind t.toNF₁.simplices Simplex.subsimplices
    rw [toNF_equiv']

  theorem toNF_ext_list [DecidableEq V] {t₁ t₂ : NF V} :
    (∀ s, s ∈ t₁.val ↔ s ∈ t₂.val) ↔ (∀ vs, Simplex.ofList vs ∈ t₁.val ↔ Simplex.ofList vs ∈ t₂.val) := by
    constructor
    · intro h vs
      generalize h₀ : Simplex.ofList vs = s
      have h₁ := congr_arg Simplex.toList h₀
      rw [Simplex.toList_ofList] at h₁
      subst h₁
      apply h
    · intro h s
      generalize h₀ : Simplex.toList s = vs
      have h₁ := congr_arg Simplex.ofList h₀
      rw [Simplex.ofList_toList] at h₁
      subst h₁
      apply h

  theorem toNF_mem_empty [DecidableEq V] (t : NF V) : ⟨empty, .empty⟩ ∈ t.val := by
    rcases t with ⟨t, h₁, _, h₂⟩
    rcases List.exists_mem_of_ne_nil _ h₂ with ⟨s, h₃⟩
    specialize h₁ ⟨empty, .empty⟩ s (List.nil_sublist _) h₃
    assumption

  theorem toNF_mem_of_empty [DecidableEq V] (vs : List V) (h : Simplex.ofList vs ∈ (toNF empty).val) : vs = [] := by
    simp_rw [toNF_equiv, toNF₁, NF₁.simplices, List.mem_bind, List.mem_singleton, exists_eq_left, Simplex.subsimplices,
      List.mem_map_of_injective Simplex.ofList_Injective, List.mem_sublists, Simplex.toList, List.sublist_nil] at h
    assumption
  
  theorem toNF_ext_rel [DecidableEq V] {t₁ t₂ : NF V} (h : ∀ s, s ∈ t₁.val ↔ s ∈ t₂.val) : Rel t₁.val.val t₂.val.val :=
  by
    rcases t₁ with ⟨t₁, h₁, h₂, h₇⟩
    rcases t₂ with ⟨t₂, h₃, h₄, h₈⟩
    dsimp at *
    generalize h₅ : t₁.toList = ss₁
    generalize h₆ : t₂.toList = ss₂
    rw [←NF₂.ofList_toList t₁, h₅] at h₁ h₂ h ⊢
    rw [←NF₂.ofList_toList t₂, h₆] at h₃ h₄ h ⊢
    clear t₁ t₂ h₅ h₆ h₇ h₈
    simp_rw [←NF₂.mem_ofList_mem] at h
    rw [IsNF₄, NF₂.toList_ofList] at *
    have h₅ := (List.perm_ext h₂ h₄).mpr h
    exact NF₂.ofList_perm _ _ h₅

  theorem toNF_rel_ext_overCongr [DecidableEq V] {s : Simplex V} {tl₁ tr₁ tl₂ tr₂ : TreeUM V}
    (ih₁ : s ∈ tl₁.toNF.val ↔ s ∈ tl₂.toNF.val) (ih₂ : s ∈ tr₁.toNF.val ↔ s ∈ tr₂.toNF.val)
    : s ∈ (overlay tl₁ tr₁).toNF.val ↔ s ∈ (overlay tl₂ tr₂).toNF.val := by
    rw [toNF_equiv, toNF_equiv] at *
    simp_rw [toNF₁, NF₁.simplices, List.bind_append, List.mem_append] at *
    tauto

  theorem toNF_lconn₁ [DecidableEq V] (v : V) (vs : List V) : (t : NF₁ V)
    → (Simplex.ofList vs) ∈ t.toNF.val
    → (Simplex.ofList vs) ∈ (lconn v t).toNF.val
    | ⟨empty, _⟩ => by
      intro h
      rw [toNF_equiv'] at h ⊢
      simp only [lconn, NF₁.simplices, List.mem_bind] at h ⊢
      rcases h with ⟨vs₁, h₁, h₂⟩
      simp at h₁
      subst vs₁
      simp [Simplex.toNF₂, NF₂.toList_ofList, Simplex.subsimplices] at h₂
      have h₃ := congr_arg Simplex.toList h₂
      rw [Simplex.toList_ofList, Simplex.toList_ofList] at h₃
      subst h₃
      use ⟨connect (leaf v) empty, .connect v .empty⟩
      constructor
      simp
      dsimp [Simplex.toNF₂]
      rw [Simplex.subsimplices, List.mem_map_of_injective Simplex.ofList_Injective, List.mem_sublists]
      exact List.nil_sublist _
    | ⟨connect (leaf v') t, h⟩ => by
      intro h'
      rw [toNF_equiv'] at h' ⊢
      simp only [lconn, NF₁.simplices, List.mem_bind] at h' ⊢
      rcases h' with ⟨vs₁, h₁, h₂⟩
      simp at h₁
      subst h₁
      simp [Simplex.toNF₂, NF₂.toList_ofList, Simplex.subsimplices] at h₂
      rcases h₂ with ⟨vs₂, h₂, h₃⟩
      have h₃ := congr_arg Simplex.toList h₃
      rw [Simplex.toList_ofList, Simplex.toList_ofList] at h₃
      subst h₃
      clear h₃
      simp only [List.mem_singleton, exists_eq_left, Simplex.subsimplices,
        List.mem_map_of_injective Simplex.ofList_Injective, List.mem_sublists]
      simp [Simplex.toList] at h₂ ⊢
      exact List.Sublist.trans h₂ (List.sublist_cons _ _)
    | ⟨overlay t₁ t₂, h⟩ =>
      have ih₁ := toNF_lconn₁ v vs ⟨t₁, by {cases h; next h => { cases h } ; next h => assumption }⟩
      have ih₂ := toNF_lconn₁ v vs ⟨t₂, by {cases h; next h => { cases h } ; next h => assumption }⟩
      by
        intro h
        rw [toNF_equiv', toNF_equiv'] at *
        simp_rw [lconn, NF₁.simplices, List.bind_append, List.mem_append] at *
        rcases h with h | h
        · exact Or.inl (ih₁ h)
        · exact Or.inr (ih₂ h)
        done
    
  theorem toNF_lconn₂ [DecidableEq V] (v : V) (vs : List V) : (t : NF₁ V)
    → (Simplex.ofList vs) ∈ t.toNF.val ↔ (Simplex.ofList (v :: vs)) ∈ (lconn v t).toNF.val
    | ⟨empty, _⟩ => by
      rw [toNF_equiv', toNF_equiv']
      simp only [lconn, NF₁.simplices, List.mem_bind]
      simp_rw [List.mem_singleton, exists_eq_left, Simplex.subsimplices,
        List.mem_map_of_injective Simplex.ofList_Injective, List.mem_sublists, Simplex.toList, List.cons_sublist_cons]
    | ⟨connect (leaf v') t, h⟩ => by
      rw [toNF_equiv', toNF_equiv']
      simp only [lconn, NF₁.simplices, List.mem_bind]
      simp_rw [List.mem_singleton, exists_eq_left, Simplex.subsimplices,
        List.mem_map_of_injective Simplex.ofList_Injective, List.mem_sublists, Simplex.toList, List.cons_sublist_cons]
    | ⟨overlay t₁ t₂, h⟩ =>
      have ih₁ := toNF_lconn₂ v vs ⟨t₁, by {cases h; next h => { cases h } ; next h => assumption }⟩
      have ih₂ := toNF_lconn₂ v vs ⟨t₂, by {cases h; next h => { cases h } ; next h => assumption }⟩
      by simp_rw [toNF_equiv', lconn, NF₁.simplices, List.bind_append, List.mem_append, ←toNF_equiv', ih₁, ih₂]

  theorem toNF_lconn₃ [DecidableEq V] (v : V) (vs : List V) : (t : NF₁ V)
    → (Simplex.ofList vs) ∈ (lconn v t).toNF.val →
      ((Simplex.ofList vs) ∈ t.toNF.val) ∨ (∃ vs', vs = v :: vs' ∧ (Simplex.ofList vs') ∈ t.toNF.val)
    | ⟨empty, _⟩ => by
      simp_rw [toNF_equiv', lconn, NF₁.simplices, List.mem_bind, List.mem_singleton, exists_eq_left,
        Simplex.subsimplices, List.mem_map_of_injective Simplex.ofList_Injective, Simplex.toList,
        List.mem_sublists]
      rintro (_ | ⟨_, h₁⟩ | ⟨_, h₁⟩)
      · exact Or.inl h₁
      · exact Or.inr ⟨_, rfl, h₁⟩
    | ⟨connect (leaf  v') t, h⟩ => by
      simp_rw [toNF_equiv', lconn, NF₁.simplices, List.mem_bind, List.mem_singleton, exists_eq_left,
        Simplex.subsimplices, List.mem_map_of_injective Simplex.ofList_Injective, Simplex.toList,
        List.mem_sublists]
      rintro (_ | ⟨_, h₁⟩ | ⟨_, h₁⟩)
      · exact Or.inl h₁
      · exact Or.inr ⟨_, rfl, h₁⟩
    | ⟨overlay t₁ t₂, h⟩ =>
      have ih₁ := toNF_lconn₃ v vs ⟨t₁, by {cases h; next h => { cases h } ; next h => assumption }⟩
      have ih₂ := toNF_lconn₃ v vs ⟨t₂, by {cases h; next h => { cases h } ; next h => assumption }⟩
      by
        simp_rw [toNF_equiv', lconn, NF₁.simplices, List.bind_append, List.mem_append, ←toNF_equiv']
        rintro (h₁ | h₁)
        · rcases ih₁ h₁ with h₂ | ⟨vs', h₂, h₃⟩
          · exact Or.inl (Or.inl h₂)
          · exact Or.inr ⟨vs', h₂, Or.inl h₃⟩
        · rcases ih₂ h₁ with h₂ | ⟨vs', h₂, h₃⟩
          · exact Or.inl (Or.inr h₂)
          · exact Or.inr ⟨vs', h₂, Or.inr h₃⟩
        done

  theorem lconn_simplex (v : V) (t : TreeUM V) (h : IsSimplex t) : lconn v ⟨t, .simp h⟩ = connect (leaf v) t := by
    induction t
    case empty => simp [lconn]
    case leaf => contradiction
    case overlay => contradiction
    case connect t₁ t₂ _ _ =>
      cases t₁
      case empty => contradiction
      case overlay => contradiction
      case connect => contradiction
      case leaf v' _ => simp [lconn]

  theorem lconn_simplex' (v : V) (t : TreeUM V) (h : IsSimplex t) : lconn v ⟨t, .simp h⟩ = ⟨_, .simp (.connect v h)⟩ := by
    ext
    rw [lconn_simplex]
    assumption

  theorem toNF₁_simplex (t : TreeUM V) (h : IsSimplex t) : toNF₁ t = t := by
    induction t
    case empty => simp [toNF₁]
    case leaf => contradiction
    case overlay => contradiction
    case connect t₁ t₂ _ ih =>
      cases t₁
      case empty => contradiction
      case overlay => contradiction
      case connect => contradiction
      case leaf v _ =>
        have h₁ : IsSimplex t₂ := by { cases h; assumption }
        specialize ih h₁
        simp_rw [toNF₁, connect', lconn]
        rw [←lconn_simplex]
        congr
        ext
        assumption
        assumption

  theorem toNF₁_simplex' (t : TreeUM V) (h : IsSimplex t) : toNF₁ t = ⟨t, .simp h⟩ := by
    ext
    rw [toNF₁_simplex]
    assumption

  theorem toNF₁_toNF [DecidableEq V] (vs : List V) : (t : NF₁ V) →
    Simplex.ofList vs ∈ t.val.toNF.val ↔ Simplex.ofList vs ∈ t.toNF.val
    | ⟨empty, _⟩ => by
      simp_rw [toNF_equiv, toNF_equiv', toNF₁]
    | ⟨connect (leaf v') t, h⟩ => by   
        simp_rw [toNF_equiv, toNF_equiv', toNF₁, connect', ←toNF_equiv']
        have h₁ : IsSimplex t := by {cases h; rename_i h; cases h; assumption}
        rw [toNF₁_simplex' t h₁, lconn_simplex' v' t h₁]
    | ⟨overlay t₁ t₂, h⟩ =>
      have ih₁ := toNF₁_toNF vs ⟨t₁, by {cases h; next h => { cases h } ; next h => assumption }⟩
      have ih₂ := toNF₁_toNF vs ⟨t₂, by {cases h; next h => { cases h } ; next h => assumption }⟩
      by
        simp_rw [toNF_equiv, toNF_equiv', toNF₁, NF₁.simplices, List.bind_append, List.mem_append, ←toNF_equiv']
        constructor
        · rintro (h₁ | h₁)
          · exact Or.inl (ih₁.mp h₁)
          · exact Or.inr (ih₂.mp h₁)
        · rintro (h₁ | h₁)
          · exact Or.inl (ih₁.mpr h₁)
          · exact Or.inr (ih₂.mpr h₁)
    
  theorem toNF₁_lconn_toNF [DecidableEq V] (v : V) (vs : List V) : (t : NF₁ V)
    → Simplex.ofList vs ∈ (lconn v t.val.toNF₁).toNF.val ↔ Simplex.ofList vs ∈ (lconn v t).toNF.val
    | ⟨empty, _⟩ => by simp [toNF₁]
    | ⟨connect (leaf v') t, h⟩ => by
        simp_rw [toNF₁, connect', lconn]
        have h₁ : IsSimplex t := by {cases h; rename_i h; cases h; assumption}
        rw [toNF₁_simplex' t h₁, lconn_simplex' v' t h₁, lconn]
        done
    | ⟨overlay t₁ t₂, h⟩ =>
      have ih₁ := toNF₁_lconn_toNF v vs ⟨t₁, by {cases h; next h => { cases h } ; next h => assumption }⟩
      have ih₂ := toNF₁_lconn_toNF v vs ⟨t₂, by {cases h; next h => { cases h } ; next h => assumption }⟩
      by
        simp_rw [toNF_equiv', toNF₁, lconn, NF₁.simplices, List.bind_append, List.mem_append, ←toNF_equiv']
        constructor
        · rintro (h₁ | h₁)
          · exact Or.inl (ih₁.mp h₁)
          · exact Or.inr (ih₂.mp h₁)
        · rintro (h₁ | h₁)
          · exact Or.inl (ih₁.mpr h₁)
          · exact Or.inr (ih₂.mpr h₁)
        done
  
  theorem toNF₁_lconn_congr [DecidableEq V] (v : V) (t₁ t₂ : NF₁ V) :
    (∀ vs, Simplex.ofList vs ∈ t₁.toNF.val ↔ Simplex.ofList vs ∈ t₂.toNF.val) →
    (∀ vs, Simplex.ofList vs ∈ (lconn v t₁).toNF.val ↔ Simplex.ofList vs ∈ (lconn v t₂).toNF.val) := by
    intro h vs
    constructor
    · intro h₁
      rcases toNF_lconn₃ _ _ _ h₁ with h₂ | ⟨vs', h₂, h₃⟩
      · apply toNF_lconn₁
        rwa [←h]
      · subst h₂
        apply (toNF_lconn₂ _ _ _).mp
        rwa [←h]
    · intro h₁
      rcases toNF_lconn₃ _ _ _ h₁ with h₂ | ⟨vs', h₂, h₃⟩
      · apply toNF_lconn₁
        rwa [h]
      · subst h₂
        apply (toNF_lconn₂ _ _ _).mp
        rwa [h]


  theorem toNF₁_connect'_congr_right [DecidableEq V] (t₁ : TreeUM V) :
    (∀ t₂ t₃ : NF₁ V, (∀ vs, Simplex.ofList vs ∈ t₂.toNF.val ↔ Simplex.ofList vs ∈ t₃.toNF.val) →
    (∀ vs, Simplex.ofList vs ∈ (connect' t₁ t₂).toNF.val ↔ Simplex.ofList vs ∈ (connect' t₁ t₃).toNF.val)) := by
    induction t₁
    case connect t₃ t₄ ih₁ ih₂ =>
      · intro t₅ t₆ h vs
        simp_rw [toNF_equiv, toNF_equiv', connect', toNF₁, ←toNF_equiv']
        have h₁ := ih₂ t₅ t₆ h
        have h₂ := ih₁ (connect' t₄ t₅) (connect' t₄ t₆) h₁
        rw [h₂]
    case empty =>
      · intro t₃ t₄ h vs
        simp_rw [toNF_equiv, toNF_equiv', connect', toNF₁, ←toNF_equiv', h]
    case leaf v =>
      · intro t₃ t₄ h vs
        simp_rw [toNF_equiv, toNF_equiv', connect', toNF₁, ←toNF_equiv', h]
        apply toNF₁_lconn_congr
        assumption       
    case overlay t₃ t₄ ih₁ ih₂ =>
      intro t₅ t₆ h
      simp_rw [toNF_equiv, toNF_equiv', connect', toNF₁, NF₁.simplices, List.bind_append, List.mem_append, ←toNF_equiv']
      intro vs
      constructor
      · rintro (h₁ | h₁)
        · exact Or.inl ((ih₁ t₅ t₆ h vs).mp h₁)
        · exact Or.inr ((ih₂ t₅ t₆ h vs).mp h₁)
      · rintro (h₁ | h₁)
        · exact Or.inl ((ih₁ t₅ t₆ h vs).mpr h₁)
        · exact Or.inr ((ih₂ t₅ t₆ h vs).mpr h₁)
      done
    
  theorem toNF_connect' [DecidableEq V] (t₁ : TreeUM V) (t₂ : NF₁ V) :
    (∀ (vs₁ vs₂), ((Simplex.ofList vs₁) ∈ t₁.toNF.val) ∧ ((Simplex.ofList vs₂) ∈ t₂.toNF.val)
    → Simplex.ofList (vs₁ ++ vs₂) ∈ (connect' t₁ t₂).toNF.val)
    ∧ (∀ (vs), ((Simplex.ofList vs) ∈ (connect' t₁ t₂).toNF.val) → ∃ vs₁ vs₂, vs = vs₁ ++ vs₂
      ∧ ((Simplex.ofList vs₁) ∈ t₁.toNF.val) ∧ ((Simplex.ofList vs₂) ∈ t₂.toNF.val))
    := by
    induction t₁ generalizing t₂
    case connect t₃ t₄ ih₁ ih₂ =>
      constructor
      · intro vs₁ vs₂ h
        simp_rw [toNF_equiv, toNF_equiv', connect', toNF₁, ←toNF_equiv']
        rcases h with ⟨h₁, h₂⟩
        simp_rw [toNF_equiv, toNF₁, ←toNF_equiv'] at h₁
        have h₃ := (ih₁ t₄.toNF₁).2 vs₁ h₁
        rcases h₃ with ⟨vs₃, vs₄, h₃, h₄, h₅⟩
        subst h₃
        change Simplex.ofList vs₄ ∈ t₄.toNF.val at h₅
        have h₆ := (ih₂ t₂).1 vs₄ vs₂ ⟨h₅, h₂⟩
        have h₇ := (ih₁ (connect' t₄ t₂)).1 vs₃ (vs₄ ++ vs₂) ⟨h₄, h₆⟩
        rwa [←List.append_assoc] at h₇
        done
      · intro vs₁ h
        simp_rw [toNF_equiv, toNF_equiv', connect', toNF₁, ←toNF_equiv'] at h
        have h₁ := (ih₁ (connect' t₄ t₂)).2 vs₁ h
        rcases h₁ with ⟨vs₂, vs₃, h₁, h₂, h₃⟩
        subst h₁
        have h₄ := (ih₂ t₂).2 vs₃ h₃
        rcases h₄ with ⟨vs₄, vs₅, h₄, h₅, h₆⟩
        subst h₄
        use vs₂ ++ vs₄
        use vs₅
        simp [List.append_assoc]
        constructor
        · simp_rw [toNF_equiv, toNF_equiv', connect', toNF₁, ←toNF_equiv']
          exact (ih₁ t₄.toNF₁).1 vs₂ vs₄ ⟨h₂, h₅⟩
        · assumption
    case empty =>
      constructor
      · simp_rw [connect']
        rintro vs₁ vs₂ ⟨h₁, h₂⟩
        have h₃ := toNF_mem_of_empty vs₁ h₁
        subst h₃
        simp_all
      · simp_rw [connect']
        intro vs₁ h₁
        use []
        use vs₁
        simp_all
        apply toNF_mem_empty
    case leaf v =>
      constructor
      · simp_rw [connect']
        rintro vs₁ vs₂ ⟨h₁, h₂⟩
        simp_rw [toNF_equiv, toNF₁, NF₁.simplices, List.mem_bind, List.mem_singleton, exists_eq_left,
          Simplex.subsimplices, List.mem_map_of_injective Simplex.ofList_Injective, Simplex.toList,
        List.mem_sublists] at h₁
        rcases h₁ with _ | ⟨_, h₁⟩ | ⟨_, h₁⟩
        · rw [List.sublist_nil] at h₁
          subst h₁
          simp
          apply toNF_lconn₁
          assumption
        · rw [List.sublist_nil] at h₁
          subst h₁
          simp
          rwa [←toNF_lconn₂]
      · intro vs₁ h₁
        simp_rw [connect'] at h₁
        rcases toNF_lconn₃ _ _ _ h₁ with h₂ | ⟨vs₂, h₂, _⟩
        · use []
          use vs₁
          simp_all
          apply toNF_mem_empty
        · subst h₂
          use [v]
          use vs₂
          simp
          constructor
          · simp_rw [toNF_equiv, toNF₁, NF₁.simplices, List.mem_bind, List.mem_singleton, exists_eq_left,
            Simplex.subsimplices, List.mem_map_of_injective Simplex.ofList_Injective, Simplex.toList,
            List.mem_sublists, List.Sublist.refl]
          · rwa [←toNF_lconn₂] at h₁
      done
    case overlay t₃ t₄ ih₁ ih₂ =>
      simp_rw [toNF_equiv, connect', toNF_equiv', toNF₁, NF₁.simplices, List.bind_append, List.mem_append, ←toNF_equiv']
      constructor
      · rintro vs₁ vs₂ ⟨h₁ | h₁, h₂⟩
        · rw [toNF_equiv', ←toNF_equiv] at h₁
          apply Or.inl
          apply (ih₁ t₂).1
          exact ⟨h₁, h₂⟩
        · rw [toNF_equiv', ←toNF_equiv] at h₁
          apply Or.inr
          apply (ih₂ t₂).1
          exact ⟨h₁, h₂⟩
      · rintro vs₁ (h₁ | h₁)
        · change Simplex.ofList vs₁ ∈ (connect' t₃ t₂).toNF.val at h₁
          rcases (ih₁ t₂).2 vs₁ h₁ with ⟨vs₃, vs₄, h₂, h₃, h₄⟩
          subst h₂
          use vs₃
          use vs₄
          simp
          exact ⟨Or.inl h₃, h₄⟩
        · change Simplex.ofList vs₁ ∈ (connect' t₄ t₂).toNF.val at h₁
          rcases (ih₂ t₂).2 vs₁ h₁ with ⟨vs₃, vs₄, h₂, h₃, h₄⟩
          subst h₂
          use vs₃
          use vs₄
          simp
          exact ⟨Or.inr h₃, h₄⟩
    done


  theorem toNF_rel_ext_connCongr' [DecidableEq V] {tl₁ tr₁ tl₂ tr₂ : TreeUM V}
    (ih₁ : ∀ vs, Simplex.ofList vs ∈ tl₁.toNF.val ↔ Simplex.ofList vs ∈ tl₂.toNF.val)
    (ih₂ : ∀ vs, Simplex.ofList vs ∈ tr₁.toNF.val ↔ Simplex.ofList vs ∈ tr₂.toNF.val)
    : ∀ vs, Simplex.ofList vs ∈ (connect tl₁ tr₁).toNF.val → Simplex.ofList vs ∈ (connect tl₂ tr₂).toNF.val := by
    simp_rw [toNF_equiv, toNF₁, ←toNF_equiv']
    intro vs₁ h₁
    have h₂ := (toNF_connect' tl₁ tr₁.toNF₁).2 _ h₁
    rcases h₂ with ⟨vs₂, vs₃, h₂, h₃, h₄⟩
    subst h₂
    rw [ih₁] at h₃
    change Simplex.ofList vs₃ ∈ tr₁.toNF.val at h₄
    rw [ih₂] at h₄
    apply (toNF_connect' tl₂ tr₂.toNF₁).1
    exact ⟨h₃, h₄⟩

  theorem toNF_rel_ext_connCongr [DecidableEq V] {tl₁ tr₁ tl₂ tr₂ : TreeUM V}
    (ih₁ : ∀ s, s ∈ tl₁.toNF.val ↔ s ∈ tl₂.toNF.val) (ih₂ : ∀ s, s ∈ tr₁.toNF.val ↔ s ∈ tr₂.toNF.val)
    : ∀ s, s ∈ (connect tl₁ tr₁).toNF.val ↔ s ∈ (connect tl₂ tr₂).toNF.val := by
    simp_rw [toNF_ext_list] at *
    intro vs
    constructor
    · apply toNF_rel_ext_connCongr'
      · exact ih₁
      · exact ih₂
    · apply toNF_rel_ext_connCongr'
      · simp [ih₁]
      · simp [ih₂]
    done


  theorem toNF_rel_ext_connAssoc [DecidableEq V] (t₁ t₂ t₃ : TreeUM V)
  : ∀ s, s ∈ (connect (connect t₁ t₂) t₃).toNF.val ↔ s ∈ (connect t₁ (connect t₂ t₃)).toNF.val := by
    simp_rw [toNF_ext_list]
    intro vs
    constructor <;> {
      intro h₁
      simp_rw [toNF_equiv, toNF₁, connect', ←toNF_equiv'] at h₁ ⊢
      assumption
    }

  theorem toNF_rel_ext_connEmptyRight [DecidableEq V] (t : TreeUM V)
    : ∀ s, s ∈ (connect t empty).toNF.val ↔ s ∈ t.toNF.val := by
    simp_rw [toNF_ext_list]
    intro vs
    constructor
    · intro h₁
      simp_rw [toNF_equiv, toNF₁, ←toNF_equiv'] at h₁
      have h₂ := (toNF_connect' t ⟨empty, .simp .empty⟩).2 vs h₁
      rcases h₂ with ⟨vs₁, vs₂, h₂, h₃, h₄⟩
      subst h₂
      have h₅ := toNF_mem_of_empty _ h₄
      subst h₅
      simp_all
    · intro h₁
      simp_rw [toNF_equiv, toNF₁, ←toNF_equiv']
      have h₂ := (toNF_connect' t ⟨empty, .simp .empty⟩).1 vs []
      simp_all
      apply h₂
      rw [←toNF₁_toNF]
      apply toNF_mem_empty
    done

  theorem toNF_rel_ext_connDistrLeft [DecidableEq V] (t₁ t₂ t₃ : TreeUM V)
    : ∀ s, s ∈ (connect t₁ (overlay t₂ t₃)).toNF.val ↔ s ∈ (overlay (connect t₁ t₂) (connect t₁ t₃)).toNF.val := by
    simp_rw [toNF_ext_list]
    intro vs
    simp_rw [toNF_equiv, toNF₁, NF₁.simplices, List.bind_append, List.mem_append, ←toNF_equiv']
    constructor
    · intro h₁
      have h₂ := (toNF_connect' _ _).2 vs h₁
      rcases h₂ with ⟨vs₁, vs₂, h₂, h₃, h₄⟩
      subst h₂
      simp_rw [toNF_equiv', NF₁.simplices, List.bind_append, List.mem_append, ←toNF_equiv'] at h₄
      rcases h₄ with (h₄ | h₄)
      · left
        apply (toNF_connect' _ _).1
        exact ⟨h₃, h₄⟩
      · right
        apply (toNF_connect' _ _).1
        exact ⟨h₃, h₄⟩
    · intro h₁
      rcases h₁ with (h₁ | h₁)
      · have h₂ := (toNF_connect' _ _).2 vs h₁
        rcases h₂ with ⟨vs₁, vs₂, h₂, h₃, h₄⟩
        subst h₂
        apply (toNF_connect' _ _).1
        simp_rw [toNF_equiv', NF₁.simplices, List.bind_append, List.mem_append, ←toNF_equiv']
        exact ⟨h₃, Or.inl h₄⟩
      · have h₂ := (toNF_connect' _ _).2 vs h₁
        rcases h₂ with ⟨vs₁, vs₂, h₂, h₃, h₄⟩
        subst h₂
        apply (toNF_connect' _ _).1
        simp_rw [toNF_equiv', NF₁.simplices, List.bind_append, List.mem_append, ←toNF_equiv']
        exact ⟨h₃, Or.inr h₄⟩
    done

  theorem toNF_rel_ext_connDistrRight [DecidableEq V] (t₁ t₂ t₃ : TreeUM V)
    : ∀ s, s ∈ (connect (overlay t₁ t₂) t₃).toNF.val ↔ s ∈ (overlay (connect t₁ t₃) (connect t₂ t₃)).toNF.val := by
    simp_rw [toNF_ext_list]
    intro vs
    simp_rw [toNF_equiv, toNF₁, connect']
    done
  
  theorem toNF_rel_ext_overAssoc [DecidableEq V] (t₁ t₂ t₃ : TreeUM V)
    : ∀ s, s ∈ (overlay (overlay t₁ t₂) t₃).toNF.val ↔ s ∈ (overlay t₁ (overlay t₂ t₃)).toNF.val := by
    simp_all [toNF, toNF₁, NF₁.toNF₂, NF₁.simplices, NF₂.toNF₃, NF₂.bind, NF₂.toList_ofList, List.bind_append,
        NF₂.toNF₄, List.dedup_append]

  theorem toNF_rel_ext_overComm [DecidableEq V] (t₁ t₂ : TreeUM V)
    : ∀ s, s ∈ (overlay t₁ t₂).toNF.val ↔ s ∈ (overlay t₂ t₁).toNF.val := by
    intro s
    simp_all [toNF, toNF₁, NF₁.toNF₂, NF₁.simplices, NF₂.toNF₃, NF₂.bind, NF₂.toList_ofList, List.bind_append,
      NF₂.toNF₄, List.dedup_append]
    rw [←NF₂.mem_ofList_mem, ←NF₂.mem_ofList_mem] at *
    simp_rw [List.mem_union, List.mem_dedup] at *
    tauto

  theorem toNF_rel_ext_overEmptyLeft [DecidableEq V] (t : TreeUM V)
    : ∀ s, s ∈ (overlay empty t).toNF.val ↔ s ∈ t.toNF.val := by
    simp_rw [toNF_ext_list]
    intro vs
    simp_rw [toNF_equiv, toNF₁, NF₁.simplices, List.bind_append, List.mem_append, ←toNF_equiv']
    constructor
    · rintro (h₁ | h₁)
      · change Simplex.ofList vs ∈ List.bind (NF₁.simplices (toNF₁ empty)) _ at h₁
        simp_rw [←toNF_equiv] at h₁
        have h₂ := toNF_mem_of_empty _ h₁
        subst h₂
        apply toNF_mem_empty
      · assumption
    · intro h₁
      exact Or.inr h₁
    done

  theorem toNF_rel_ext_overEmptyRight [DecidableEq V] (t : TreeUM V)
    : ∀ s, s ∈ (overlay t empty).toNF.val ↔ s ∈ t.toNF.val := by
    simp_rw [toNF_ext_list]
    intro vs
    simp_rw [toNF_equiv, toNF₁, NF₁.simplices, List.bind_append, List.mem_append, ←toNF_equiv']
    constructor
    · rintro (h₁ | h₁)
      · assumption
      · change Simplex.ofList vs ∈ List.bind (NF₁.simplices (toNF₁ empty)) _ at h₁
        simp_rw [←toNF_equiv] at h₁
        have h₂ := toNF_mem_of_empty _ h₁
        subst h₂
        apply toNF_mem_empty
    · intro h₁
      exact Or.inl h₁
    done

  theorem toNF_rel_ext [DecidableEq V] {t₁ t₂ : TreeUM V} (h : Rel t₁ t₂)
    : ∀ s, s ∈ t₁.toNF.val ↔ s ∈ t₂.toNF.val := by
    intro s
    induction h generalizing s
    case refl => simp
    case symm => simp [*]
    case trans => simp [*]
    case overCongr ih₁ ih₂ => exact toNF_rel_ext_overCongr (ih₁ s) (ih₂ s)
    case connCongr ih₁ ih₂ => exact toNF_rel_ext_connCongr ih₁ ih₂ s
    case overAssoc t₁ t₂ t₃ => exact toNF_rel_ext_overAssoc t₁ t₂ t₃ s
    case overComm t₁ t₂ => exact toNF_rel_ext_overComm t₁ t₂ s
    case overEmptyLeft t => exact toNF_rel_ext_overEmptyLeft t s
    case overEmptyRight t => exact toNF_rel_ext_overEmptyRight t s
    case connAssoc t₁ t₂ t₃ => exact toNF_rel_ext_connAssoc t₁ t₂ t₃ s
    case connEmptyLeft t => simp_all [toNF, toNF₁, connect']
    case connEmptyRight t => exact toNF_rel_ext_connEmptyRight t s
    case connDistrLeft t₁ t₂ t₃ => exact toNF_rel_ext_connDistrLeft t₁ t₂ t₃ s
    case connDistrRight t₁ t₂ t₃ => exact toNF_rel_ext_connDistrRight t₁ t₂ t₃ s

  theorem toNF_rel_ext' [DecidableEq V] {t₁ t₂ : TreeUM V} :
    Rel t₁ t₂ ↔ (∀ s, s ∈ t₁.toNF.val ↔ s ∈ t₂.toNF.val) := by
    constructor
    apply toNF_rel_ext
    intro h₁
    have h₂ := toNF_ext_rel h₁
    refine Rel.trans (toNF_rel t₁) ?_
    exact Rel.trans h₂ (toNF_rel t₂).symm

  theorem toNF_empty [DecidableEq V] : (empty : TreeUM V).toNF.val = NF₂.ofList [⟨empty, .empty⟩] := by
    simp [toNF, toNF₁, NF₁.toNF₂, NF₁.simplices, NF₂.ofList, NF₂.toNF₃, NF₂.bind, NF₂.toNF₄, Simplex.ofList]

  theorem toNF_overlay [DecidableEq V] (t₁ t₂ : TreeUM V)
    : ∀ s, s ∈ (overlay t₁ t₂).toNF.val ↔ s ∈ t₁.toNF.val ∨ s ∈ t₂.toNF.val := by
    intro s
    generalize h₀ : s.toList = vs
    have h₁ := congr_arg Simplex.ofList h₀
    rw [Simplex.ofList_toList] at h₁
    subst h₁
    simp_rw [toNF_equiv, toNF₁, NF₁.simplices, List.bind_append, List.mem_append]

  theorem toNF_connect [DecidableEq V] (t₁ t₂ : TreeUM V) :
    (∀ (vs₁ vs₂), ((Simplex.ofList vs₁) ∈ t₁.toNF.val) ∧ ((Simplex.ofList vs₂) ∈ t₂.toNF.val)
    → Simplex.ofList (vs₁ ++ vs₂) ∈ (connect t₁ t₂).toNF.val)
    ∧ (∀ (vs), ((Simplex.ofList vs) ∈ (connect t₁ t₂).toNF.val) → ∃ vs₁ vs₂, vs = vs₁ ++ vs₂
      ∧ ((Simplex.ofList vs₁) ∈ t₁.toNF.val) ∧ ((Simplex.ofList vs₂) ∈ t₂.toNF.val))
    := by
      have h := toNF_connect' t₁ t₂.toNF₁
      simp_rw [toNF_equiv, toNF_equiv', toNF₁] at *
      assumption

  theorem toNF_mem_toNF [DecidableEq V] (t : NF V) (s : Simplex V)
    : s ∈ t.val.val.toNF.val ↔ s ∈ t.val := by
    rcases t with ⟨t, h₁, h₂, h₃⟩
    simp_rw [toNF_equiv, List.mem_bind]
    simp_rw [NF₂.toNF₁_eq t, NF₂.simplices_eq]
    constructor
    · rintro ⟨s₁, h₄ | h₄, h₅⟩
      · rw [Simplex.subsimplices, ←Simplex.ofList_toList s, List.mem_map_of_injective TreeUM.Simplex.ofList_Injective,
          List.mem_sublists] at h₅
        exact h₁ s s₁ h₅ h₄
      · subst h₄
        rw [Simplex.subsimplices, ←Simplex.ofList_toList s, List.mem_map_of_injective TreeUM.Simplex.ofList_Injective,
          List.mem_sublists, Simplex.toList, List.sublist_nil] at h₅
        have h₆ := List.exists_mem_of_ne_nil _ h₃
        simp_rw [NF₂.mem_ofList_mem, NF₂.ofList_toList] at h₆
        rcases h₆ with ⟨s', h₆⟩
        apply h₁ s s'
        simp_rw [h₅, List.nil_sublist]
        assumption
    · intro h₄
      use s
      simp [h₄]
      rw [Simplex.subsimplices, ←Simplex.ofList_toList s, List.mem_map_of_injective TreeUM.Simplex.ofList_Injective,
          List.mem_sublists, Simplex.toList_ofList]
    done

end TreeUM

abbrev FreeUM (V : Type _) := Quotient (TreeUM.setoid V)

namespace FreeUM

  def mk {V : Type _} (t : TreeUM V) : FreeUM V := Quotient.mk _ t

  def empty {V : Type _} : FreeUM V := Quotient.mk _ TreeUM.empty

  def leaf {V : Type _} (v : V) : FreeUM V := Quotient.mk _ (TreeUM.leaf v)

  def overlay {V : Type _} (t₁ t₂ : FreeUM V) : FreeUM V := Quotient.liftOn₂ t₁ t₂
    (λ t₁ t₂ => Quotient.mk _ (TreeUM.overlay t₁ t₂))
    (λ _ _ _ _ h₁ h₂ => Quotient.sound (TreeUM.Rel.overCongr h₁ h₂))
  
  def connect {V : Type _} (t₁ t₂ : FreeUM V) : FreeUM V := Quotient.liftOn₂ t₁ t₂
    (λ t₁ t₂ => Quotient.mk _ (TreeUM.connect t₁ t₂))
    (λ _ _ _ _ h₁ h₂ => Quotient.sound (TreeUM.Rel.connCongr h₁ h₂))
  
  instance : Zero (FreeUM V) := ⟨empty⟩
  instance : One (FreeUM V) := ⟨empty⟩
  instance : Add (FreeUM V) := ⟨overlay⟩
  instance : Mul (FreeUM V) := ⟨connect⟩

  theorem add_assoc (t₁ t₂ t₃ : FreeUM V) : t₁ + t₂ + t₃ = t₁ + (t₂ + t₃) := by
    change overlay (overlay t₁ t₂) t₃ = overlay t₁ (overlay t₂ t₃)
    induction t₁ using Quotient.ind
    induction t₂ using Quotient.ind
    induction t₃ using Quotient.ind
    simp_rw [overlay, Quotient.liftOn₂_mk, Quotient.eq]
    apply TreeUM.Rel.overAssoc

  theorem add_zero (t : FreeUM V) : t + 0 = t := by
    change overlay t empty = t
    induction t using Quotient.ind
    simp_rw [overlay, empty, Quotient.liftOn₂_mk, Quotient.eq]
    apply TreeUM.Rel.overEmptyRight

  theorem zero_add (t : FreeUM V) : 0 + t = t := by
    change overlay empty t = t
    induction t using Quotient.ind
    simp_rw [overlay, empty, Quotient.liftOn₂_mk, Quotient.eq]
    apply TreeUM.Rel.overEmptyLeft
  
  theorem add_comm (t₁ t₂ : FreeUM V) : t₁ + t₂ = t₂ + t₁ := by
    change overlay t₁ t₂ = overlay t₂ t₁
    induction t₁ using Quotient.ind
    induction t₂ using Quotient.ind
    simp_rw [overlay, Quotient.liftOn₂_mk, Quotient.eq]
    apply TreeUM.Rel.overComm
  
  theorem mul_assoc (t₁ t₂ t₃ : FreeUM V) : t₁ * t₂ * t₃ = t₁ * (t₂ * t₃) := by
    change connect (connect t₁ t₂) t₃ = connect t₁ (connect t₂ t₃)
    induction t₁ using Quotient.ind
    induction t₂ using Quotient.ind
    induction t₃ using Quotient.ind
    simp_rw [connect, Quotient.liftOn₂_mk, Quotient.eq]
    apply TreeUM.Rel.connAssoc
  
  theorem mul_one (t : FreeUM V) : t * 1 = t := by
    change connect t empty = t
    induction t using Quotient.ind
    simp_rw [connect, empty, Quotient.liftOn₂_mk, Quotient.eq]
    apply TreeUM.Rel.connEmptyRight

  theorem one_mul (t : FreeUM V) : 1 * t = t := by
    change connect empty t = t
    induction t using Quotient.ind
    simp_rw [connect, empty, Quotient.liftOn₂_mk, Quotient.eq]
    apply TreeUM.Rel.connEmptyLeft
  
  theorem left_distrib (t₁ t₂ t₃ : FreeUM V) : t₁ * (t₂ + t₃) = t₁ * t₂ + t₁ * t₃ := by
    change connect t₁ (overlay t₂ t₃) = overlay (connect t₁ t₂) (connect t₁ t₃)
    induction t₁ using Quotient.ind
    induction t₂ using Quotient.ind
    induction t₃ using Quotient.ind
    simp_rw [connect, overlay, Quotient.liftOn₂_mk, Quotient.eq]
    apply TreeUM.Rel.connDistrLeft

  theorem right_distrib (t₁ t₂ t₃ : FreeUM V) : (t₁ + t₂) * t₃ = t₁ * t₃ + t₂ * t₃ := by
    change connect (overlay t₁ t₂) t₃ = overlay (connect t₁ t₃) (connect t₂ t₃)
    induction t₁ using Quotient.ind
    induction t₂ using Quotient.ind
    induction t₃ using Quotient.ind
    simp_rw [connect, overlay, Quotient.liftOn₂_mk, Quotient.eq]
    apply TreeUM.Rel.connDistrRight
  
  instance : UnitedMonoid (FreeUM V) := {
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

end FreeUM