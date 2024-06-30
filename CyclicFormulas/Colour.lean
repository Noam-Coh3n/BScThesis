import Mathlib.Init.Set
import Mathlib.Data.FinEnum

inductive Colour : Type
| o : Colour
| μ : Colour
| ν : Colour
deriving DecidableEq

namespace Colour

instance : FinEnum Colour := FinEnum.ofList [o, μ, ν] (by rintro ⟨⟩ <;> simp)

-- def repr : Colour → Lean.Format
-- | o => "o"
-- | μ => "μ"
-- | ν => "ν"

-- instance : Repr Colour := ⟨fun v _ => repr v⟩

instance : ToString Colour where
  toString
  | o => "black"
  | μ => "magenta"
  | ν => "navy"

@[simp]
def mono {V} (Ω : V → Colour) (s : List V) : Prop :=
  (∀ v ∈ s, Ω v = μ) ∨ (∀ v ∈ s, Ω v = ν)

end Colour