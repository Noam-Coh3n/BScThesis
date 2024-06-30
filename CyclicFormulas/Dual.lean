import CyclicFormulas.C2CF

/- Typeclass for the ∂ notation -/
class Dual (α : Type*) where
  dual : α → α

prefix:1024 "∂" => Dual.dual

open Function

namespace Colour

@[simp]
protected def dual : Colour → Colour
| o => o
| μ => ν
| ν => μ

instance : Dual Colour := ⟨.dual⟩

instance inj_dual: Injective Colour.dual := fun x y => by
  cases x <;> cases y <;> simp

instance : Bijective Colour.dual := Injective.bijective_of_finite inj_dual

@[simp]
theorem dual_involutive : Function.Involutive Colour.dual := by
  rintro ⟨⟩ <;> rfl

theorem dual_o : c = o ↔ ∂c = o := ⟨
  (congr_arg _ .),
  fun _ => match c with | o => rfl
⟩

theorem dual_not_o : c ≠ o ↔ ∂c ≠ o := not_iff_not.mpr dual_o

end Colour

namespace Label

@[simp]
protected def dual : Label → Label
| prop p     => nprop p
| nprop p    => prop p
| or         => and
| and        => or
| dim_atom A => box_atom A
| box_atom A => dim_atom A

instance : Dual Label := ⟨.dual⟩

@[simp]
theorem dual_involutive : Function.Involutive Label.dual := by
  rintro ⟨⟩ <;> rfl

theorem dual_admissible : ∀ ℓ c ,
  col_admissible ℓ c ↔ col_admissible ∂ℓ ∂c := by
    rintro ⟨⟩ ⟨⟩ <;> rfl


theorem dual_prg : ∀ ℓ, prg ℓ ↔ prg ∂ℓ := by
  rintro ⟨⟩ <;> rfl

theorem dual_lit : ∀ ℓ, lit ℓ ↔ lit ∂ℓ := by
  rintro ⟨⟩ <;> rfl

theorem dual_cm : ∀ ℓ, checkmark ℓ ↔ checkmark ∂ℓ := by
  rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩) <;> rfl

end Label

instance {α β : Type*} [Dual β] : Dual (α → β) := ⟨fun f x => ∂(f x)⟩

open Label

namespace C2CF'

protected def dual (G : C2CF') : C2CF' where
  toGraph := G
  vI      := G.vI

instance : Dual C2CF' := ⟨.dual⟩

end C2CF'

namespace C2CF

protected def dual (𝔾 : C2CF) : C2CF where
  toC2CF' := ∂𝔾
  L       := ∂𝔾.L

  no_cm v v_ne_f c := 𝔾.no_cm v v_ne_f <| (dual_cm _).mpr c

  Ω       := ∂𝔾.Ω

  colouring v := by
    repeat rw [Function.comp_apply]
    apply (dual_admissible ..).mp
    exact 𝔾.colouring v

  monochrome _ _ a b := let ⟨con, not_o⟩ := 𝔾.monochrome _ _ a  b
    ⟨congr_arg Colour.dual con, Colour.dual_not_o.mp not_o⟩

  succ v := 𝔾.succ v
  lit_succ _ _     := 𝔾.lit_succ _ _ ∘ (dual_lit (𝔾.L _)).mpr
  prg_succ _ _     := 𝔾.prg_succ _ _ ∘ (dual_prg (𝔾.L _)).mpr
  or_succ _ _  l c := 𝔾.and_succ _ _ (Label.dual_involutive (𝔾.L _) ▸ congr_arg Label.dual l) ((Colour.dual_involutive (𝔾.Ω _) ▸ congr_arg Colour.dual c))
  and_succ _ _ l c := 𝔾.or_succ _ _ (Label.dual_involutive (𝔾.L _) ▸ congr_arg Label.dual l) ((Colour.dual_involutive (𝔾.Ω _) ▸ congr_arg Colour.dual c))

instance : Dual C2CF := ⟨.dual⟩

end C2CF