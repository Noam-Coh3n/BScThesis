import Mathlib.Logic.Relation
import CyclicFormulas.myInstances

mutual
  inductive Formula : Type
  | prop  : Nat → Formula
  | nprop : Nat → Formula
  | or    : Formula → Formula → Formula
  | and   : Formula → Formula → Formula
  | dim   : Program → Formula → Formula
  | box   : Program → Formula → Formula

  inductive Program : Type
  | atom  : Nat → Program
  | comp  : Program → Program → Program
  | union : Program → Program → Program
  | star  : Program → Program
  | test  : Formula → Program
end

infixl:60 " ∪∪ " => Program.union
infixl:60 " ∨∨ " => Formula.or

open Formula Program

mutual
  def Program.repr : Program → Lean.Format
  | atom  n     => s!"A{n}"
  | comp  π₁ π₂ => s!"({Program.repr π₁}) ; ({Program.repr π₂})"
  | union π₁ π₂ => s!"({Program.repr π₁}) ∪ ({Program.repr π₂})"
  | star  π     => s!"({Program.repr π})*"
  | test  φ     => s!"({Formula.repr φ})?"

  def Formula.repr : Formula → Lean.Format
  | prop  n  => if n = 0 then "✓" else s!"p{n}"
  | nprop n  => if n = 0 then "¬✓" else s!"¬p{n}"
  | .or  φ ψ => s!"({Formula.repr φ}) ∨ ({Formula.repr ψ})"
  | .and φ ψ => s!"({Formula.repr φ}) ∧ ({Formula.repr ψ})"
  | dim π φ  => s!"‹{Program.repr π}›{Formula.repr φ}"
  | box π φ  => s!"[{Program.repr π}] {Formula.repr φ}"
end

instance : Repr Program := ⟨fun π _ => repr π⟩
instance : Repr Formula := ⟨fun φ _ => repr φ⟩

structure Model where
  S : Type
  V : Nat → S → Prop
  R : Nat → S → S → Prop

instance : CoeSort Model Type := ⟨Model.S⟩

mutual
  def rel {𝔐 : Model} : Program → 𝔐.S → 𝔐.S → Prop
  | .atom  n        => 𝔐.R n
  | .comp  π₁ π₂    => Relation.Comp (rel π₁) (rel π₂)
  | .union π₁ π₂    => rel π₁ ∪ rel π₂
  | .star  π        => Relation.ReflTransGen (rel π)
  | .test  φ        => (Eq . ∩ truth φ)

  def truth {𝔐 : Model} : Formula → 𝔐.S → Prop
  | .prop  n => 𝔐.V n
  | .nprop n => Not ∘ 𝔐.V n
  | .or  φ ψ => truth φ ∪ truth ψ
  | .and φ ψ => truth φ ∩ truth ψ
  | .dim π φ => (∃ t, rel π . t ∧ truth φ t)
  | .box π φ => (∀ t, rel π . t → truth φ t)
end
