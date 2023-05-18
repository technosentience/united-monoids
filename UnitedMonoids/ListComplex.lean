import UnitedMonoids.UnitedMonoid
import UnitedMonoids.Util


structure ListComplex (V : Type _) where
  simplices : Finset (List V)
  containment : List.Sublist vs₁ vs₂ → vs₂ ∈ simplices → vs₁ ∈ simplices
  contains_empty : [] ∈ simplices

namespace ListComplex

  @[ext]
  theorem ext (L₁ L₂ : ListComplex V) (h : L₁.simplices = L₂.simplices) : L₁ = L₂ := by
    cases L₁
    cases L₂
    congr

end ListComplex

namespace ListComplex

  def empty : ListComplex V := ⟨{ [] }, containment, contains_empty⟩
    where
      containment := by
        simp
        intros _ _ h₁ h₂
        subst h₂
        cases h₁
        rfl
      contains_empty := by simp
  
  def overlay [DecidableEq V] (c₁ c₂ : ListComplex V) : ListComplex V
    := ⟨c₁.simplices ∪ c₂.simplices, containment, contains_empty⟩
    where
      containment := by
        intros vs₁ vs₂ h₁
        simp
        rintro (h₂ | h₂)
        · apply Or.inl
          apply c₁.containment
          assumption
          assumption
        · apply Or.inr
          apply c₂.containment
          assumption 
          assumption
      contains_empty := by
        simp
        apply Or.inl
        apply c₁.contains_empty
        done

  def connect [DecidableEq V] (c₁ c₂ : ListComplex V) : ListComplex V
    := ⟨c₁.simplices.bunionᵢ (fun xs => c₂.simplices.bunionᵢ (fun ys => {xs ++ ys})),
      containment, contains_empty⟩
    where
      containment := by
        intros vs₁ vs₂ h₁
        simp_rw [Finset.bunionᵢ_bunionᵢ, Finset.mem_bunionᵢ, Finset.mem_singleton]
        rintro ⟨vs₃, h₂, vs₄, h₃, h₄⟩
        subst h₄
        rcases List.sublist_append h₁ with ⟨vs₅, vs₆, h₄, h₅, h₆⟩
        refine ⟨vs₅, ?_, vs₆, ?_, h₄⟩
        · apply c₁.containment
          assumption
          assumption
        · apply c₂.containment
          assumption
          assumption
      
      contains_empty := by simp; exact ⟨c₁.contains_empty, c₂.contains_empty⟩

  instance : Zero (ListComplex V) := ⟨empty⟩
  instance : One (ListComplex V) := ⟨empty⟩
  instance [DecidableEq V] : Add (ListComplex V) := ⟨overlay⟩
  instance [DecidableEq V] : Mul (ListComplex V) := ⟨connect⟩

  theorem add_assoc [DecidableEq V] (c₁ c₂ c₃ : ListComplex V) : c₁ + c₂ + c₃ = c₁ + (c₂ + c₃) := by
    change overlay (overlay c₁ c₂) c₃ = overlay c₁ (overlay c₂ c₃)
    ext1
    simp [overlay]
    
  theorem add_zero [DecidableEq V] (c : ListComplex V) : c + 0 = c := by
    change overlay c empty = c
    ext1
    simp [overlay, empty, c.contains_empty]

  theorem zero_add [DecidableEq V] (c : ListComplex V) : 0 + c = c := by
    change overlay empty c = c
    ext1
    simp [overlay, empty, c.contains_empty]
  
  theorem add_comm [DecidableEq V] (c₁ c₂ : ListComplex V) : c₁ + c₂ = c₂ + c₁ := by
    change overlay c₁ c₂ = overlay c₂ c₁
    ext1
    simp [overlay, Finset.union_comm]

  theorem mul_assoc [DecidableEq V] (c₁ c₂ c₃ : ListComplex V) : c₁ * c₂ * c₃ = c₁ * (c₂ * c₃) := by
    change connect (connect c₁ c₂) c₃ = connect c₁ (connect c₂ c₃)
    ext1
    simp [connect, Finset.bunionᵢ_bunionᵢ]
  
  theorem mul_one [DecidableEq V] (c : ListComplex V) : c * 1 = c := by
    change connect c empty = c
    ext1
    simp [connect, empty, c.contains_empty]

  theorem one_mul [DecidableEq V] (c : ListComplex V) : 1 * c = c := by
    change connect empty c = c
    ext1
    simp [connect, empty, c.contains_empty]
  
  theorem left_distrib [DecidableEq V] (c₁ c₂ c₃ : ListComplex V) : c₁ * (c₂ + c₃) = c₁ * c₂ + c₁ * c₃ := by
    change connect c₁ (overlay c₂ c₃) = overlay (connect c₁ c₂) (connect c₁ c₃)
    ext1
    simp [connect, overlay, Finset.bunionᵢ_bunionᵢ]
    ext S
    simp
    aesop

  theorem right_distrib [DecidableEq V] (c₁ c₂ c₃ : ListComplex V) : (c₁ + c₂) * c₃ = c₁ * c₃ + c₂ * c₃ := by
    change connect (overlay c₁ c₂) c₃ = overlay (connect c₁ c₃) (connect c₂ c₃)
    ext1
    simp [connect, overlay, Finset.bunionᵢ_bunionᵢ]
    ext S
    simp
    aesop

  instance [DecidableEq V] : UnitedMonoid (ListComplex V) := {
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

end ListComplex

namespace TreeUM

  def NF.toLC [DecidableEq V] (t : NF V) : ListComplex V := {
    simplices := t.val.toList.map Simplex.toList |>.toFinset,
    containment := by {
        intros vs₁ vs₂ h
        rcases t with ⟨t, h₁, h₂⟩
        dsimp [IsNF₃] at h₁
        generalize h₃ : Simplex.ofList vs₁ = s₁
        generalize h₄ : Simplex.ofList vs₂ = s₂
        have h₅ := congr_arg Simplex.toList h₃
        have h₆ := congr_arg Simplex.toList h₄
        rw [Simplex.toList_ofList] at h₅ h₆
        subst h₅ h₆
        simp_rw [List.mem_toFinset, List.mem_map_of_injective Simplex.toList_Injective]
        exact h₁ _ _ h
        done
      },
    contains_empty := by {
      change Simplex.toList ⟨empty, .empty⟩ ∈ _
      simp_rw [List.mem_toFinset, List.mem_map_of_injective Simplex.toList_Injective]
      apply toNF_mem_empty
      done
    }
  }

  theorem NF.toLC_ext [DecidableEq V] (t₁ t₂ : NF V) :
    (∀ s, s ∈ t₁.val ↔ s ∈ t₂.val) → t₁.toLC = t₂.toLC := by
      intro h
      ext vs
      rw [toNF_ext_list] at h
      simp_rw [toLC, List.mem_toFinset]
      rw [←Simplex.toList_ofList vs]
      simp_rw [List.mem_map_of_injective Simplex.toList_Injective]
      apply h

  theorem NF.toLC_mem [DecidableEq V] (t : NF V) (vs : List V) :
    Simplex.ofList vs ∈ t.val ↔ vs ∈ t.toLC.simplices := by
      simp_rw [toLC, List.mem_toFinset]
      nth_rewrite 2 [←Simplex.toList_ofList vs]
      simp_rw [List.mem_map_of_injective Simplex.toList_Injective, Membership.mem, NF₂.HasSimplex, Membership.mem]

  def toLC [DecidableEq V] (t : TreeUM V) : ListComplex V := t.toNF.toLC

  theorem toLC_rel_ext [DecidableEq V] (t₁ t₂ : TreeUM V) (h : Rel t₁ t₂) : t₁.toLC = t₂.toLC := by
    apply NF.toLC_ext
    apply toNF_rel_ext
    assumption

end TreeUM

namespace FreeUM

  def toLC [DecidableEq V] (t : FreeUM V) : ListComplex V :=
    Quotient.lift (TreeUM.toLC : TreeUM V → ListComplex V) TreeUM.toLC_rel_ext t

  theorem toLC_empty [DecidableEq V] : toLC (empty : FreeUM V) = ListComplex.empty := by
    simp [empty, toLC, TreeUM.toLC]
    ext1
    simp_rw [ListComplex.empty, TreeUM.NF.toLC, TreeUM.toNF_empty, TreeUM.NF₂.toList_ofList,
      List.map, TreeUM.Simplex.toList]
    simp

  theorem toLC_overlay [DecidableEq V] (t₁ t₂ : FreeUM V) : (overlay t₁ t₂).toLC = t₁.toLC.overlay t₂.toLC := by
    induction t₁ using Quotient.ind
    induction t₂ using Quotient.ind
    rename_i t₁ t₂
    simp [overlay, toLC, TreeUM.toLC]
    ext vs
    simp_rw [ListComplex.overlay, Finset.mem_union, ←TreeUM.NF.toLC_mem, TreeUM.toNF_overlay]

  theorem toLC_connect [DecidableEq V] (t₁ t₂ : FreeUM V) : (connect t₁ t₂).toLC = t₁.toLC.connect t₂.toLC := by
    induction t₁ using Quotient.ind
    induction t₂ using Quotient.ind
    rename_i t₁ t₂
    simp [connect, toLC, TreeUM.toLC]
    ext vs
    simp_rw [ListComplex.connect, Finset.mem_bunionᵢ, Finset.mem_singleton, ←TreeUM.NF.toLC_mem]
    have h₁ := TreeUM.toNF_connect t₁ t₂
    constructor
    · intro h₂
      rcases h₁.2 vs h₂ with ⟨vs₁, vs₂, h₃, h₄, h₅⟩
      exact ⟨vs₁, h₄, vs₂, h₅, h₃⟩
    · rintro ⟨vs₁, h₂, vs₂, h₃, h₄⟩
      subst h₄
      exact h₁.1 vs₁ vs₂ ⟨h₂, h₃⟩

  def toLC_hom [DecidableEq V] : UnitedMonoid.Hom (FreeUM V) (ListComplex V) := {
    toFun := toLC,
    preserves_empty := toLC_empty,
    preserves_overlay := @toLC_overlay V _,
    preserves_connect := @toLC_connect V _
  }

end FreeUM

namespace ListComplex

  def toFUM_aux₁ [DecidableEq V] (c : List (List V)) : TreeUM.NF₂ V :=
    TreeUM.NF₂.ofList (c.map TreeUM.Simplex.ofList)
  
  theorem toFUM_aux₂ [DecidableEq V] {c₁ c₂ : List (List V)} (h : c₁ ~ c₂)
    : TreeUM.Rel (toFUM_aux₁ c₁).val (toFUM_aux₁ c₂).val := by
    simp_rw [toFUM_aux₁]
    apply TreeUM.NF₂.ofList_perm
    rw [List.perm_iff_count] at *
    intro s
    generalize h₀ : TreeUM.Simplex.toList s = vs
    have h₁ := congr_arg TreeUM.Simplex.ofList h₀
    rw [TreeUM.Simplex.ofList_toList] at h₁
    subst h₁
    simp_rw [List.count_map_of_injective _ _ TreeUM.Simplex.ofList_Injective]
    apply h

  theorem toFUN_aux₃ [DecidableEq V] (c : List (List V)) (h : ∀ vs₁ vs₂, List.Sublist vs₁ vs₂ → vs₂ ∈ c → vs₁ ∈ c) 
    : TreeUM.IsNF₃ (toFUM_aux₁ c) := by
    simp_rw [toFUM_aux₁, TreeUM.IsNF₃]
    intros s₁ s₂
    generalize h₁ : TreeUM.Simplex.toList s₁ = vs₁
    generalize h₂ : TreeUM.Simplex.toList s₂ = vs₂
    have h₃ := congr_arg TreeUM.Simplex.ofList h₁
    have h₄ := congr_arg TreeUM.Simplex.ofList h₂
    rw [TreeUM.Simplex.ofList_toList] at h₃ h₄
    subst h₃ h₄
    clear h₁ h₂
    simp_rw [List.mem_map_of_injective TreeUM.Simplex.ofList_Injective, ←TreeUM.NF₂.mem_ofList_mem,
      List.mem_map_of_injective TreeUM.Simplex.ofList_Injective]
    apply h
    
  theorem toFUN_aux₄ [DecidableEq V] (c : List (List V)) (h : List.Nodup c) : TreeUM.IsNF₄ (toFUM_aux₁ c) := by
    simp_rw [toFUM_aux₁, TreeUM.IsNF₄, TreeUM.NF₂.toList_ofList, List.nodup_map_iff TreeUM.Simplex.ofList_Injective]
    assumption

  theorem toFUN_aux₅ [DecidableEq V] (c : List (List V)) (h : [] ∈ c) : TreeUM.NF₂.toList (toFUM_aux₁ c) ≠ [] := by
    intro h
    simp_rw [toFUM_aux₁, TreeUM.NF₂.toList_ofList, List.map_eq_nil] at h
    subst h
    contradiction

  def toFUM_aux₆ [DecidableEq V]
    (c : List (List V)) 
    (h₁ : ∀ vs₁ vs₂, List.Sublist vs₁ vs₂ → vs₂ ∈ c → vs₁ ∈ c)
    (h₂ : List.Nodup c)
    (h₃ : [] ∈ c)
    : TreeUM.NF V := 
    ⟨toFUM_aux₁ c, toFUN_aux₃ c h₁, toFUN_aux₄ c h₂, toFUN_aux₅ c h₃⟩

  theorem toFUM_aux₁_eq_aux₆ [DecidableEq V]
    (c : List (List V)) 
    (h₁ : ∀ vs₁ vs₂, List.Sublist vs₁ vs₂ → vs₂ ∈ c → vs₁ ∈ c)
    (h₂ : List.Nodup c)
    (h₃ : [] ∈ c)
    : toFUM_aux₁ c = (toFUM_aux₆ c h₁ h₂ h₃).val := rfl

  def toFUM [DecidableEq V] (c : ListComplex V) : FreeUM V :=
    Quotient.liftOn c.simplices.val (fun c => FreeUM.mk (toFUM_aux₁ c).val)
     (by
      intro c₁ c₂ h
      simp
      apply Quotient.sound
      apply toFUM_aux₂
      assumption
     )
  
  theorem toFUM_empty [DecidableEq V] : toFUM (empty : ListComplex V) = FreeUM.empty := by
    simp [toFUM, empty]
    change Quotient.liftOn (Quotient.mk _ [[]]) _ _ = _
    simp_rw [Quotient.liftOn_mk, FreeUM.empty, FreeUM.mk, toFUM_aux₁]
    simp [TreeUM.Simplex.ofList, TreeUM.NF₂.ofList]
    apply TreeUM.Rel.overEmptyLeft

  theorem toFUM_overlay [DecidableEq V] (c₁ c₂ : ListComplex V)
    : (c₁.overlay c₂).toFUM = c₁.toFUM.overlay c₂.toFUM := by
    generalize h₀ : c₁.overlay c₂ = c₃
    rcases c₁ with ⟨⟨c₁, nodup₁⟩, cont₁, cont_e₁⟩
    rcases c₂ with ⟨⟨c₂, nodup₂⟩, cont₂, cont_e₂⟩
    rcases c₃ with ⟨⟨c₃, nodup₃⟩, cont₃, cont_e₃⟩
    simp [overlay, toFUM] at h₀ ⊢
    induction c₁ using Quotient.ind
    induction c₂ using Quotient.ind
    induction c₃ using Quotient.ind
    simp at nodup₁ nodup₂ cont₁ cont₂ cont_e₁ cont_e₂
    simp_rw [Quotient.liftOn_mk]
    simp [Union.union, Multiset.union] at h₀
    change _ ∪ _ ~ _ at h₀
    simp [FreeUM.overlay, FreeUM.mk]
    apply TreeUM.toNF_rel_ext'.mpr
    simp_rw [TreeUM.toNF_overlay]
    simp_rw [toFUM_aux₁_eq_aux₆ _ @cont₁ nodup₁ cont_e₁]
    simp_rw [toFUM_aux₁_eq_aux₆ _ @cont₂ nodup₂ cont_e₂]
    simp_rw [toFUM_aux₁_eq_aux₆ _ @cont₃ nodup₃ cont_e₃]
    simp_rw [TreeUM.toNF_mem_toNF]
    simp_rw [toFUM_aux₆, toFUM_aux₁]
    intro s
    generalize h₁ : TreeUM.Simplex.toList s = vs
    have h₂ := congr_arg TreeUM.Simplex.ofList h₁
    rw [TreeUM.Simplex.ofList_toList] at h₂
    subst h₂
    simp_rw [List.mem_map_of_injective TreeUM.Simplex.ofList_Injective, ←TreeUM.NF₂.mem_ofList_mem,
      List.mem_map_of_injective TreeUM.Simplex.ofList_Injective]
    simp_rw [←List.Perm.mem_iff h₀, List.mem_union]

  
  theorem toFUM_connect [DecidableEq V] (c₁ c₂ : ListComplex V)
    : (c₁.connect c₂).toFUM = c₁.toFUM.connect c₂.toFUM := by
    generalize h₀ : c₁.connect c₂ = c₃
    rcases c₁ with ⟨⟨c₁, nodup₁⟩, cont₁, cont_e₁⟩
    rcases c₂ with ⟨⟨c₂, nodup₂⟩, cont₂, cont_e₂⟩
    rcases c₃ with ⟨⟨c₃, nodup₃⟩, cont₃, cont_e₃⟩
    simp [connect, toFUM] at h₀ ⊢
    induction c₁ using Quotient.ind
    induction c₂ using Quotient.ind
    induction c₃ using Quotient.ind
    simp at nodup₁ nodup₂ cont₁ cont₂ cont_e₁ cont_e₂
    simp_rw [Quotient.liftOn_mk]
    simp_rw [Finset.bunionᵢ] at h₀
    simp at h₀
    simp_rw [List.toFinset, Multiset.toFinset] at h₀
    simp at h₀
    simp [FreeUM.connect, FreeUM.mk]
    apply TreeUM.toNF_rel_ext'.mpr
    intro s
    generalize h₁ : TreeUM.Simplex.toList s = vs
    have h₂ := congr_arg TreeUM.Simplex.ofList h₁
    rw [TreeUM.Simplex.ofList_toList] at h₂
    subst h₂
    simp_rw [toFUM_aux₁_eq_aux₆ _ @cont₁ nodup₁ cont_e₁]
    simp_rw [toFUM_aux₁_eq_aux₆ _ @cont₂ nodup₂ cont_e₂]
    simp_rw [toFUM_aux₁_eq_aux₆ _ @cont₃ nodup₃ cont_e₃]
    nth_rewrite 1 [TreeUM.toNF_mem_toNF, toFUM_aux₆]
    simp [toFUM_aux₁]
    simp_rw [List.mem_map_of_injective TreeUM.Simplex.ofList_Injective, ←TreeUM.NF₂.mem_ofList_mem,
      List.mem_map_of_injective TreeUM.Simplex.ofList_Injective]
    simp_rw [←List.Perm.mem_iff h₀, List.mem_dedup, List.mem_bind, List.mem_dedup, List.mem_map]
    constructor
    · rintro ⟨vs₁, h₃, vs₂, h₄, h₅⟩
      subst h₅
      apply (TreeUM.toNF_connect _ _).1
      simp_rw [TreeUM.toNF_mem_toNF, toFUM_aux₆, toFUM_aux₁]
      simp_rw [List.mem_map_of_injective TreeUM.Simplex.ofList_Injective, ←TreeUM.NF₂.mem_ofList_mem,
        List.mem_map_of_injective TreeUM.Simplex.ofList_Injective]
      tauto
    · intro h₂
      rcases (TreeUM.toNF_connect _ _).2 _ h₂ with ⟨vs₁, vs₂, h₃, h₄, h₅⟩
      simp_rw [TreeUM.toNF_mem_toNF, toFUM_aux₆, toFUM_aux₁, List.mem_map_of_injective TreeUM.Simplex.ofList_Injective,
        ←TreeUM.NF₂.mem_ofList_mem, List.mem_map_of_injective TreeUM.Simplex.ofList_Injective] at h₄ h₅
      aesop
    done
      

  theorem toFUM_toLC [DecidableEq V] (c : ListComplex V) : c.toFUM.toLC = c := by
    rcases c with ⟨⟨c, nodup⟩, containment, contains_empty⟩
    induction c using Quotient.ind
    simp [toFUM, FreeUM.toLC]
    ext1
    simp_rw [FreeUM.mk, ←Multiset.quot_mk_to_coe, Quotient.liftOn_mk]
    ext1 vs
    simp_rw [TreeUM.toLC, TreeUM.NF.toLC, List.mem_toFinset, List.mem_map,
      TreeUM.NF₂.mem_ofList_mem, TreeUM.NF₂.ofList_toList, 
      toFUM_aux₁_eq_aux₆ _ @containment nodup contains_empty, TreeUM.toNF_mem_toNF,
      toFUM_aux₆, toFUM_aux₁, ←TreeUM.NF₂.mem_ofList_mem, List.mem_map]
    simp [TreeUM.Simplex.toList_ofList]

  def toNF_hom [DecidableEq V] : UnitedMonoid.Hom (ListComplex V) (FreeUM V) := {
    toFun := toFUM,
    preserves_empty := toFUM_empty,
    preserves_overlay := @toFUM_overlay V _,
    preserves_connect := @toFUM_connect V _
  }

end ListComplex

namespace FreeUM

  theorem toLC_toFUM [DecidableEq V] (t : FreeUM V) : t.toLC.toFUM = t := by
    generalize h₀ : t.toLC = c
    rcases c with ⟨⟨c, nodup⟩, containment, contains_empty⟩
    induction t using Quotient.ind
    rename_i t
    simp [toLC, TreeUM.toLC] at h₀
    simp_rw [TreeUM.NF.toLC] at h₀
    have h₁ := congr_arg (fun x => Finset.val (ListComplex.simplices x)) h₀
    clear h₀
    simp only at h₁
    simp_rw [List.toFinset, Multiset.toFinset] at h₁
    induction c using Quotient.ind
    simp_rw [Multiset.dedup, Multiset.ofList, Quot.liftOn_mk] at h₁
    change Quotient.mk _ _ = _ at h₁
    simp_rw [Quotient.eq] at h₁
    simp_rw [ListComplex.toFUM, FreeUM.mk, Quotient.liftOn_mk, Quotient.eq]
    apply TreeUM.toNF_rel_ext'.mpr
    intro s
    simp_rw [ListComplex.toFUM_aux₁_eq_aux₆ _ @containment nodup contains_empty, 
      TreeUM.toNF_mem_toNF, ListComplex.toFUM_aux₆, ListComplex.toFUM_aux₁]
    simp_rw [←TreeUM.NF₂.mem_ofList_mem, List.mem_map, ←List.Perm.mem_iff h₁, List.mem_dedup, List.mem_map]
    constructor
    · rintro ⟨vs₁, ⟨vs₂, h₂, h₃⟩, h₄⟩
      subst h₃
      subst h₄
      rw [TreeUM.Simplex.ofList_toList]
      assumption
    · intro h₁
      generalize h₂ : TreeUM.Simplex.toList s = vs
      have h₃ := congr_arg TreeUM.Simplex.ofList h₂
      rw [TreeUM.Simplex.ofList_toList] at h₃
      subst h₃
      use vs
      constructor
      use TreeUM.Simplex.ofList vs
      simp_rw [TreeUM.Simplex.toList_ofList, TreeUM.NF₂.mem_ofList_mem, TreeUM.NF₂.ofList_toList]
      constructor
      · assumption
      · simp
      rfl
    done

end FreeUM
