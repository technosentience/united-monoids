import Mathlib.Data.Nat.Basic
import UnitedMonoids.Util
import Aesop

inductive ExprTree (R α : Type _) where
  | leaf (val : α) : ExprTree R α
  | node (op : R) (left right : ExprTree R α) : ExprTree R α

namespace ExprTree
  def fold (f : α → β) (g : R → β → β → β) : ExprTree R α → β
    | .leaf x => f x
    | .node R l r => g R (fold f g l) (fold f g r)
  
  def map (f : α → β) : ExprTree R α → ExprTree R β
    | .leaf x => leaf (f x)
    | .node R l r => node R (map f l) (map f r)

  def add [Zero R] : ExprTree R α → ExprTree R α → ExprTree R α := node 0

  def bind (x : ExprTree R α) (f : α → ExprTree R β) : ExprTree R β
    := fold f node x

  instance [Inhabited α] : Inhabited (ExprTree R α) where
    default := leaf default
  
  instance [Zero R] : Add (ExprTree R α) where
    add := add

  instance Functor (R : Type _) : Functor (ExprTree R) where
    map := map

  instance Monad (R : Type _) : Monad (ExprTree R) where
    bind := bind
    pure := leaf

  inductive AssocRel : ExprTree R α → ExprTree R α → Prop
    | lift_left (x : R) (l l' r : ExprTree R α) (s : AssocRel l l') : AssocRel (node x l r) (node x l' r)
    | lift_right (x : R) (l r r' : ExprTree R α) (s : AssocRel r r') : AssocRel (node x l r) (node x l r')
    | assoc (x : R) (l m r : ExprTree R α) : AssocRel (node x (node x l m) r) (node x l (node x m r))

  theorem fold_assoc (f : α → β) (g : R → β → β → β) (h₁ : ∀ x, Associative (g x))
    : ∀ (x y : ExprTree R α), AssocRel x y → fold f g x = fold f g y
    | _, _, AssocRel.lift_left x l l' r s => by simp [fold]; rw [fold_assoc f g h₁ l l' s]
    | _, _, AssocRel.lift_right x l r r' s => by simp [fold]; rw [fold_assoc f g h₁ r r' s]
    | _, _, AssocRel.assoc x l m r => by simp [fold]; rw [h₁ x]

end ExprTree

abbrev AssocTree (R α : Type _) := Quot (α := ExprTree R α) ExprTree.AssocRel

namespace AssocTree
  def mk (x : ExprTree R α) : AssocTree R α := Quot.mk ExprTree.AssocRel x

  def fold (f : α → β) (g : R → β → β → β) (h₁ : ∀ x, Associative (g x)) : AssocTree R α → β
    := Quot.lift (ExprTree.fold f g) (ExprTree.fold_assoc f g h₁)

  instance [Inhabited α] : Inhabited (AssocTree R α) where
    default := mk default

  def add [Zero R] (x y : AssocTree R α) : AssocTree R α
    := Quot.liftOn₂ x y (fun x y => mk (ExprTree.add x y)) h₁ h₂
    where
      h₁ := by
        intros
        simp [ExprTree.add]
        apply Quot.sound
        apply ExprTree.AssocRel.lift_right
        assumption
      h₂ := by
        intros
        simp [ExprTree.add]
        apply Quot.sound
        apply ExprTree.AssocRel.lift_left
        assumption 

  instance [Zero R] : Add (AssocTree R α) where
    add := add

  theorem add_assoc [Zero R] (x y z : AssocTree R α) : x + y + z = x + (y + z)
    := by
      apply Quot.induction_on₃ (δ := fun x y z => x + y + z = x + (y + z))
      intros 
      simp [HAdd.hAdd, instHAdd, Add.add, add, mk, ExprTree.add]
      apply Quot.sound
      apply ExprTree.AssocRel.assoc


  instance [Zero R] : AddSemigroup (AssocTree R α) where
    add_assoc := add_assoc

  def mul [Zero R] [One R] (x y : AssocTree R α) : AssocTree R α
    := Quot.liftOn₂ x y (fun x y => mk (ExprTree.node 1 x y)) h₁ h₂
    where
      h₁ := by
        intros
        apply Quot.sound
        apply ExprTree.AssocRel.lift_right
        assumption
      h₂ := by
        intros
        apply Quot.sound
        apply ExprTree.AssocRel.lift_left
        assumption

  instance [Zero R] [One R] : Mul (AssocTree R α) where
    mul := mul
  
  theorem mul_assoc [Zero R] [One R] (x y z : AssocTree R α) : x * y * z = x * (y * z)
    := by
      apply Quot.induction_on₃ (δ := fun x y z => x * y * z = x * (y * z))
      intros 
      simp [HMul.hMul, instHMul, Mul.mul, mul, mk, ExprTree.node]
      apply Quot.sound
      apply ExprTree.AssocRel.assoc
  
  instance [Zero R] [One R] : Semigroup (AssocTree R α) where
    mul_assoc := mul_assoc

end AssocTree