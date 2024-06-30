import CyclicFormulas.Dual
import CyclicFormulas.Formula
import Mathlib.Init.Data.Subtype.Basic

open C2CP C2CF Sum Sum3

def G_p (n : Nat) : C2CF' where
  V       := Fin 1
  E _ _   := False
  vI      := 0

def 𝔾_p (n : Nat) : C2CF where
  toC2CF' := G_p n
  L _     := .prop (n + 1)
  no_cm _ _ := not_false

  Ω _     := .o
  colouring := (forall_const _).mpr trivial
  monochrome _ _ | .single a => False.elim a

  succ _           := none
  lit_succ _ _ _   := not_false
  prg_succ _ _     := False.elim
  or_succ _ _ _ _  := False.elim
  and_succ _ _ _ _ := False.elim

def G_np : Nat → C2CF' := ∂G_p

def 𝔾_np : Nat → C2CF := ∂𝔾_p

def G_or (Gφ Gψ : C2CF') : C2CF' where
  V := Fin 1 ⊕ Gφ ⊕ Gψ
  V_fin := FinEnum.sum

  E
  | in₀ _, in₁ w => w = Gφ.vI
  | in₀ _, in₂ w => w = Gψ.vI
  | in₁ v, in₁ w => Gφ.E v w
  | in₂ v, in₂ w => Gψ.E v w
  | _, _         => False

  E_dec
  | in₀ _, in₁ _ => decEq ..
  | in₀ _, in₂ _ => decEq ..
  | in₁ _, in₁ _ => Gφ.E_dec ..
  | in₂ _, in₂ _ => Gψ.E_dec ..
  | in₀ _, in₀ _ => isFalse not_false
  | in₁ _, in₀ _ => isFalse not_false
  | in₁ _, in₂ _ => isFalse not_false
  | in₂ _, in₀ _ => isFalse not_false
  | in₂ _, in₁ _ => isFalse not_false

  vI := inl default

namespace Sum3
  def is₀ : α ⊕ β ⊕ γ → Prop
  | in₀ _ => True
  | in₁ _ => False
  | in₂ _ => False

  def is₁ : α ⊕ β ⊕ γ → Prop
  | in₀ _ => False
  | in₁ _ => True
  | in₂ _ => False

  def is₂ : α ⊕ β ⊕ γ → Prop
  | in₀ _ => False
  | in₁ _ => False
  | in₂ _ => True

  def get₁ (b : α ⊕ β ⊕ γ) (_ : is₁ b) : β := (match b with | in₁ b₁ => b₁)

  def get₂ (c : α ⊕ β ⊕ γ) (_ : is₂ c) : γ := (match c with | in₂ b₂ => b₂)


  theorem in₁_get₁ : (b : α ⊕ β ⊕ γ) → (h : is₁ b) → b = in₁ (get₁ b h)
    | in₁ _, _ => rfl

end Sum3

namespace G_or
lemma ncrossl {Gφ Gψ : C2CF'} {x₁ : Gφ} {y : Fin 1 ⊕ Gφ ⊕ Gψ} (h : TC' (G_or Gφ Gψ).E (in₁ x₁) y) : Sum3.is₁ y := by
  induction h with
  | @single z => rcases z with (_ | ⟨_ | _⟩) <;> trivial
  | @tail y z r _ _ => rcases z with (_ | ⟨_ | _⟩) <;> rcases y with (_ | ⟨_ | _⟩) <;> trivial

lemma ncrossr {Gφ Gψ : C2CF'} {x₂ : Gψ} {y : Fin 1 ⊕ Gφ ⊕ Gψ} (h : TC' (G_or Gφ Gψ).E (in₂ x₂) y) : is₂ y := by
  induction h with
  | @single z => rcases z with (_ | ⟨_ | _⟩) <;> trivial
  | @tail y z r _ _ => rcases z with (_ | ⟨_ | _⟩) <;> rcases y with (_ | ⟨_ | _⟩) <;> trivial

lemma castl {Gφ Gψ : C2CF'} {y : Fin 1 ⊕ Gφ ⊕ Gψ} {x : Gφ} (h : TC' (G_or Gφ Gψ).E (in₁ x) y) (left : is₁ y) :
  TC' Gφ.E x <| get₁ y left := by
    induction h with
    | @single z a => rcases z with (_ | ⟨_ | _⟩) <;> first | trivial | exact .single a
    | @tail y' z r a ih =>
      rcases z with (z₀ | ⟨z₁ | z₂⟩) <;> rcases y' with (y₀ | ⟨y₁ | y₂⟩) <;> try trivial
      . have contra := ncrossl r; simp only [is₁] at contra
      . exact .tail (ih trivial) a

-- lemma rcastl {Gφ Gψ : C2CF'} {x y : Gφ} (h : RTC (G_or Gφ Gψ).E (in₁ x) (in₁ y)) : RTC Gφ.E x y := by
--   cases h; exact .refl
--   rename_i z p a
--   match z with
--   | in₁ z => exact Relation.ReflTransGen.tail (rcastl p) a
--   | in₀ z => sorry
-- termination_by sizeOf h

-- match h with
--   | .refl => .refl
--   | .tail p a => by
--     rename (G_or _ _).V => z
--     match z with
--     | in₀ z => sorry
--     | in₁ z => exact Relation.ReflTransGen.tail (rcastl p) a

lemma castr {Gφ Gψ : C2CF'} {y : Fin 1 ⊕ Gφ ⊕ Gψ} {x : Gψ} (h : TC' (G_or Gφ Gψ).E (in₂ x) y) (right : is₂ y):
  TC' Gψ.E x <| get₂ y right := by
    induction h with
    | @single z a => rcases z with (_ | ⟨_ | _⟩) <;> first | trivial | exact .single a
    | @tail y' z r a ih =>
      rcases z with (z₀ | ⟨z₁ | z₂⟩) <;> rcases y' with (y₀ | ⟨y₁ | y₂⟩) <;> try trivial
      . have contra := ncrossr r; simp only [is₂] at contra
      . exact .tail (ih trivial) a

lemma lift_pathl {Gφ Gψ : C2CF'} {x y : Gφ} (p : RTC Gφ.E x y) : RTC (G_or Gφ Gψ).E (in₁ x) (in₁ y) := by
  induction p with
  | refl => exact .refl
  | tail _ a p' => exact .tail p' a

lemma lift_pathr {Gφ Gψ : C2CF'} {x y : Gψ} (p : RTC Gψ.E x y) : RTC (G_or Gφ Gψ).E (in₂ x) (in₂ y) := by
  induction p with
  | refl => exact .refl
  | tail _ a p' => exact .tail p' a

end G_or

open G_or

def 𝔾_or (𝔾φ 𝔾ψ : C2CF) : C2CF where
  toC2CF' := G_or 𝔾φ.toC2CF' 𝔾ψ.toC2CF'

  L
  | in₀ _ => Label.or
  | in₁ x => 𝔾φ.L x
  | in₂ y => 𝔾ψ.L y

  no_cm := sorry

  Ω
  | in₀ _ => Colour.o
  | in₁ x => 𝔾φ.Ω x
  | in₂ y => 𝔾ψ.Ω y

  lit_succ := by
    rintro (z | ⟨vl | vr⟩) (z' | ⟨wl | wr⟩) p
    <;> simp_all [G_or]
    . apply 𝔾φ.lit_succ _ _ p
    . apply 𝔾ψ.lit_succ _ _ p

  succ
  | in₀ _ => none
  | in₁ v => .map in₁ <| 𝔾φ.succ v
  | in₂ v => .map in₂ <| 𝔾ψ.succ v

  prg_succ
  | in₁ _, in₁ _, p => fun a => (congr_arg _ (𝔾φ.prg_succ _ _ p a)).trans Option.map_coe
  | in₂ _, in₂ _, p => fun a => (congr_arg _ (𝔾ψ.prg_succ _ _ p a)).trans Option.map_coe
  | in₁ _, in₀ _, _ => False.elim
  | in₂ _, in₀ _, _ => False.elim
  | in₁ _, in₂ _, _ => False.elim
  | in₂ _, in₁ _, _ => False.elim

  or_succ v w l c a np := match v, w with
    | in₁ v, in₁ w => congr_arg (Option.map _) <| 𝔾φ.or_succ v w l c a <| sorry
    | in₂ v, in₂ w => congr_arg (Option.map _) <| 𝔾ψ.or_succ v w l c a <| sorry

  and_succ v w l c a np := match v, w with
    | in₁ v, in₁ w => congr_arg (Option.map _) <| 𝔾φ.and_succ v w l c a <| sorry
    | in₂ v, in₂ w => congr_arg (Option.map _) <| 𝔾ψ.and_succ v w l c a <| sorry

  colouring
  | in₀ _ => trivial
  | in₁ v => 𝔾φ.colouring v
  | in₂ v => 𝔾ψ.colouring v

  monochrome
    | in₀ x, in₀ y => (match . with | .single a => False.elim a)
    | in₀ x, in₁ y => fun _ => (match . with | .single a => False.elim a)
    | in₀ x, in₂ y => fun _ => (match . with | .single a => False.elim a)
    | in₁ x, in₀ y => (match . with | .single a => False.elim a)
    | in₂ x, in₀ y => (match . with | .single a => False.elim a)
    | in₁ x, in₂ y => (False.elim <| ncrossl .)
    | in₂ x, in₁ y => (False.elim <| ncrossr .)
    | in₁ x, in₁ y => fun vw wv => 𝔾φ.monochrome x y (castl vw trivial) (castl wv trivial)
    | in₂ x, in₂ y => fun vw wv => 𝔾ψ.monochrome x y (castr vw trivial) (castr wv trivial)

def G_and (Gφ Gψ : C2CF') : C2CF' := ∂(G_or ∂Gφ ∂Gψ)

def 𝔾_and (𝔾φ 𝔾ψ : C2CF) : C2CF := ∂(𝔾_or ∂𝔾φ ∂𝔾ψ)

@[simp]
def G_dim (Hα : C2CP') (Gφ : C2CF') : C2CF' where
  V := {v : Hα ⊕ Gφ // v ≠ inl Hα.vF}
  V_fin := FinEnum.Subtype.finEnum (. ≠ inl Hα.vF)

  E
  | ⟨inr v, _⟩, ⟨inr w, _⟩ => Gφ.E v w
  | ⟨inl v, _⟩, ⟨inl w, _⟩ => Hα.E v w
  | ⟨inl v, _⟩, ⟨inr w, _⟩ => Hα.E v Hα.vF ∧ w = Gφ.vI
  | ⟨inr _, _⟩, ⟨inl _, _⟩ => False

  E_dec
  | ⟨inr _, _⟩, ⟨inr _, _⟩ => Gφ.E_dec ..
  | ⟨inl _, _⟩, ⟨inl _, _⟩ => Hα.E_dec ..
  | ⟨inl _, _⟩, ⟨inr _, _⟩ => And.decidable
  | ⟨inr _, _⟩, ⟨inl _, _⟩ => decidableFalse

  vI := ⟨inl Hα.vI, Function.Injective.ne inl_injective Hα.i_ne_f⟩

def 𝔾_dim (ℍα : C2CP) (𝔾φ : C2CF) : C2CF where
  toC2CF' := G_dim ℍα 𝔾φ

  L
  | ⟨inr v, _⟩ => 𝔾φ.L v
  | ⟨inl v, _⟩ => ℍα.L v

  no_cm := sorry

  Ω
  | ⟨inr v, _⟩ => 𝔾φ.Ω v
  | ⟨inl v, _⟩ => ℍα.Ω v

  succ
  | ⟨inr v, _⟩ => (⟨inr ., inr_ne_inl⟩) <$> 𝔾φ.succ v
  | ⟨inl v, _⟩ => match ℍα.succ v with
    | none => none
    | some w => dite (w ≠ ℍα.vF)
      (some ⟨inl w, by simp [.]⟩)
      (fun _ => some ⟨inr 𝔾φ.vI, inr_ne_inl⟩)

  lit_succ
  | ⟨inr _, _⟩, ⟨inr _, _⟩, p => 𝔾φ.lit_succ _ _ p
  | ⟨inl _, _⟩, ⟨inl _, _⟩, p => ℍα.lit_succ _ _ p
  | ⟨inl _, _⟩, ⟨inr _, _⟩, p => not_and_of_not_left _ (ℍα.lit_succ _ _ p)
  | ⟨inr _, _⟩, ⟨inl _, _⟩, _ => not_false

  colouring
  | ⟨inr v, _⟩ => 𝔾φ.colouring v
  | ⟨inl v, _⟩ => ℍα.colouring v

  monochrome := sorry

  prg_succ
  | ⟨inr _, _⟩, ⟨inr _, _⟩, p => (by simp [𝔾φ.prg_succ _ _ p .])
  | ⟨inl _, _⟩, ⟨inl _, _⟩, p => have := ℍα.prg_succ _ _ p; by aesop
  | ⟨inl _, _⟩, ⟨inr _, _⟩, p => have := ℍα.prg_succ _ _ p; by aesop
  | ⟨inr _, _⟩, ⟨inl _, _⟩, _ => False.elim

  or_succ := sorry
  and_succ := sorry

def G_box (Hα : C2CP') (Gφ : C2CF') : C2CF' := ∂(G_dim Hα ∂Gφ)

def 𝔾_box (ℍα : C2CP) (𝔾φ : C2CF) : C2CF := ∂(𝔾_dim ℍα ∂𝔾φ)

@[simp]
def HA (n : Nat) : C2CP' where
  V := Bool
  E := (. && !.)
  vI := true
  vF := false
  i_ne_f := Bool.noConfusion

def ℍA (n : Nat) : C2CP where
  toC2CF' := HA n
  vF := (HA n).vF
  i_ne_f := (HA n).i_ne_f

  L := (bif . then .dim_atom n else .prop 0)
  no_cm v _ _ := nomatch v

  Ω _ := .o
  LΩf := by simp only [HA, cond_false, and_self]

  succ := (bif . then some false else none)
  lit_succ := by simp
  prg_succ := by simp
  or_succ v _ _ := nomatch v
  and_succ v _ _ := nomatch v

  colouring := by simp
  monochrome v w vw wv :=
    have h : ¬ TC' (HA n).E false true := (match . with | .single a => by simp only [HA, Bool.not_true, Bool.and_self] at a)
    match v, w with
    | true, true   => by cases vw <;> simp_all
    | true, false  => absurd wv h
    | false, true  => absurd vw h
    | false, false => by cases vw <;> simp_all [TC']

  ΩX := by simp
  LX := by simp
  andX := by simp

def H_comp (Hα Hβ : C2CP') : C2CP' := ⟨
    G_dim Hα Hβ,
    ⟨inr Hβ.vF, inr_ne_inl⟩,
    by simp only [G_dim, ne_eq, Subtype.mk.injEq, not_false_eq_true]
  ⟩

def ℍ_comp (ℍα ℍβ : C2CP) : C2CP where
  toC2CF' := H_comp ℍα ℍβ
  vF := (H_comp ℍα ℍβ).vF
  i_ne_f := (H_comp ℍα ℍβ).i_ne_f
  LΩf := LΩf _
  no_cm v ne_f := sorry

  succ := (𝔾_dim ℍα ℍβ).succ
  lit_succ := (𝔾_dim ℍα ℍβ).lit_succ
  prg_succ := (𝔾_dim ℍα ℍβ).prg_succ
  colouring := (𝔾_dim ℍα ℍβ).colouring
  monochrome := (𝔾_dim ℍα ℍβ).monochrome
  or_succ := (𝔾_dim ℍα ℍβ).or_succ
  and_succ := (𝔾_dim ℍα ℍβ).and_succ

  ΩX := sorry
  LX := sorry
  andX := sorry


--  := ⟨
--   𝔾_dim ℍα ℍβ,
--   ⟨inr ℍβ.vF, inr_ne_inl⟩,
--   by simp only [𝔾_dim, G_dim, ne_eq, Option.map_eq_map, Subtype.mk.injEq, not_false_eq_true],
--   LΩf _
-- ⟩

@[simp]
def H_union (Hα Hβ : C2CP') : C2CP' where
  V := {x : Fin 1 ⊕ Hα ⊕ Hβ // x ≠ in₂ Hβ.vF}
  V_fin := FinEnum.Subtype.finEnum (. ≠ in₂ Hβ.vF)

  E
  | ⟨in₀ _, _⟩, ⟨in₁ w, _⟩ => w = Hα.vI
  | ⟨in₀ _, _⟩, ⟨in₂ w, _⟩ => w = Hβ.vI
  | ⟨in₁ v, _⟩, ⟨in₁ w, _⟩ => Hα.E v w
  | ⟨in₂ v, _⟩, ⟨in₂ w, _⟩ => Hβ.E v w
  | ⟨in₂ v, _⟩, ⟨in₁ w, _⟩ => Hβ.E v Hβ.vF ∧ w = Hα.vF
  | _, _ => False

  E_dec
  | ⟨in₀ _, _⟩, ⟨in₀ _, _⟩ => decidableFalse
  | ⟨in₀ _, _⟩, ⟨in₁ w, _⟩ => decEq ..
  | ⟨in₀ _, _⟩, ⟨in₂ w, _⟩ => decEq ..
  | ⟨in₁ _, _⟩, ⟨in₀ _, _⟩ => decidableFalse
  | ⟨in₁ v, _⟩, ⟨in₁ w, _⟩ => Hα.E_dec ..
  | ⟨in₁ _, _⟩, ⟨in₂ _, _⟩ => decidableFalse
  | ⟨in₂ _, _⟩, ⟨in₀ _, _⟩ => decidableFalse
  | ⟨in₂ v, _⟩, ⟨in₁ w, _⟩ => @And.decidable (Hβ.E v Hβ.vF) (w = Hα.vF) (Hβ.E_dec v Hβ.vF) (decEq w Hα.vF)
  | ⟨in₂ v, _⟩, ⟨in₂ w, _⟩ => Hβ.E_dec ..

  vI := ⟨in₀ 0, inl_ne_inr⟩
  vF := ⟨in₁ Hα.vF, by simp [in₂, in₁, ne_eq, inr.injEq, not_false_eq_true]⟩
  i_ne_f := @Subtype.ne_of_val_ne _ _ ⟨_, _⟩ _ inl_ne_inr

def ℍ_union (ℍα ℍβ : C2CP) : C2CP where
  toC2CF' := H_union ℍα ℍβ
  vF := ⟨in₁ ℍα.vF, by simp only [in₁, in₂, ne_eq, inr.injEq, not_false_eq_true]⟩
  i_ne_f := @Subtype.ne_of_val_ne _ _ ⟨_, _⟩ _ inl_ne_inr

  L
  | ⟨in₀ _, _⟩ => .or
  | ⟨in₁ v, _⟩ => ℍα.L v
  | ⟨in₂ v, _⟩ => ℍβ.L v

  Ω
  | ⟨in₀ _, _⟩ => .o
  | ⟨in₁ v, _⟩ => ℍα.Ω v
  | ⟨in₂ v, _⟩ => ℍβ.Ω v

  no_cm := sorry

  succ
  | ⟨in₀ _, _⟩ => none
  | ⟨in₁ v, _⟩ => (fun x => ⟨in₁ x, by simp⟩) <$> ℍα.succ v
  | ⟨in₂ v, _⟩ => match ℍβ.succ v with
    | none => none
    | some w => dite (w ≠ ℍβ.vF)
      (some ⟨in₂ w, by simp [.]⟩)
      (fun _ => some ⟨in₁ ℍα.vF, by simp⟩)


  lit_succ
  | ⟨in₁ _, _⟩, ⟨in₁ _, _⟩, p => ℍα.lit_succ _ _ p
  | ⟨in₂ _, _⟩, ⟨in₂ _, _⟩, p => ℍβ.lit_succ _ _ p
  | ⟨in₂ _, _⟩, ⟨in₁ _, _⟩, p => not_and_of_not_left _ (ℍβ.lit_succ _ _ p)
  | ⟨in₁ _, _⟩, ⟨in₀ _, _⟩, _ => not_false
  | ⟨in₁ _, _⟩, ⟨in₂ _, _⟩, _ => not_false
  | ⟨in₂ _, _⟩, ⟨in₀ _, _⟩, _ => not_false

  LΩf := ℍα.LΩf

  colouring
  | ⟨in₀ _, _⟩ => trivial
  | ⟨in₁ v, _⟩ => ℍα.colouring v
  | ⟨in₂ v, _⟩ => ℍβ.colouring v

  monochrome := sorry

  ΩX := sorry
  LX := sorry
  andX := sorry

  prg_succ
  | ⟨in₁ _, _⟩, ⟨in₁ _, _⟩, p => (by simp [ℍα.prg_succ _ _ p .])
  | ⟨in₂ _, _⟩, ⟨in₂ _, _⟩, p => have := ℍβ.prg_succ _ _ p; by aesop
  | ⟨in₂ _, _⟩, ⟨in₁ _, _⟩, p => have := ℍβ.prg_succ _ _ p; by aesop
  | ⟨in₁ _, _⟩, ⟨in₀ _, _⟩, _ => False.elim
  | ⟨in₁ _, _⟩, ⟨in₂ _, _⟩, _ => False.elim
  | ⟨in₂ _, _⟩, ⟨in₀ _, _⟩, _ => False.elim

  or_succ := sorry
  and_succ := sorry

-- @[simp]
def H_star (Hα : C2CP') : C2CP' where
  V := Fin 1 ⊕ Hα
  V_fin := FinEnum.sum

  E
  | inl _,  _     => False
  | inr v, inl _ => v = Hα.vF
  | inr v, inr w => (v = Hα.vF ∧ w = Hα.vI) ∨ Hα.E v w

  E_dec
  | inl _,  _    => decidableFalse
  | inr _, inl _ => decEq ..
  | inr _, inr _ => Or.decidable

  vI := inr Hα.vF
  vF := inl 0
  i_ne_f := inr_ne_inl

def ℍ_star (ℍα : C2CP) : C2CP where
  toC2CF' := H_star ℍα
  vF := inl 0
  i_ne_f := inr_ne_inl

  L
  | inl _ => .prop 0
  | inr v => if v = ℍα.vF then .or else ℍα.L v

  no_cm := sorry

  Ω
  | inl _ => .o
  | inr v => if ℍα.between v then .μ else ℍα.Ω v

  LΩf := by simp only [H_star, and_self]

  lit_succ
  | inl _, _, _ => not_false
  | inr v, w, p => by
    by_contra a
    cases w
    . simp_all only [Label.lit, H_star, LΩf, ite_true]
    . simp only [H_star] at a
      apply @by_cases (v = ℍα.vF) <;> intros <;> simp_all [ℍα.lit_succ, H_star]

  succ
  | inl _ => none
  | inr v => inr <$> ℍα.succ v

  prg_succ
  | inr v, inl w, p => by intro; simp_all only [Label.prg, H_star, Option.map_eq_map,
    Option.map_eq_some', and_false, exists_const, LΩf, ite_true]
  | inr v, inr w, p => if v_eq_f : v = ℍα.vF
    then by simp_all only [Label.prg, H_star, LΩf, ite_true]
    else by simp_all [ℍα.prg_succ v w _, H_star]

  or_succ := sorry
  and_succ := sorry

  monochrome := sorry
  colouring := sorry

  ΩX := sorry
  LX := sorry
  andX := sorry


def H_test (Gφ : C2CF') : C2CP' where
  V := Bool ⊕ Gφ
  V_fin := FinEnum.sum

  E
  | inl v, inl w => v && !w
  | inl v, inr w => v && w = Gφ.vI
  | inr _, inl _ => False
  | inr v, inr w => Gφ.E v w

  E_dec
  | inl _, inl _ => decEq ..
  | inl _, inr _ => decEq ..
  | inr _, inl _ => decidableFalse
  | inr v, inr w => Gφ.E_dec v w

  vI := inl true
  vF := inl false
  i_ne_f := Function.Injective.ne inl_injective Bool.noConfusion

def ℍ_test (𝔾φ : C2CF) : C2CP where
  toC2CF' := H_test 𝔾φ
  vF := inl false
  i_ne_f := Function.Injective.ne inl_injective Bool.noConfusion

  L
  | inl true  => .and
  | inl false => .prop 0
  | inr v     => 𝔾φ.L v

  no_cm := sorry

  Ω
  | inl _ => .o
  | inr v => 𝔾φ.Ω v

  LΩf := ⟨rfl, rfl⟩

  lit_succ := by simp_all [𝔾φ.lit_succ, H_test]

  succ
  | inl true  => some <|.inl false
  | inl false => none
  | inr v     => inr <$> 𝔾φ.succ v

  prg_succ
  | inr _, inr _, p => fun a => (congr_arg _ (𝔾φ.prg_succ _ _ p a)).trans Option.map_coe
  | inr _, inl _, _ => False.elim

  or_succ := sorry
  and_succ := sorry

  colouring
  | .inl true => trivial
  | .inl false => trivial
  | .inr v => 𝔾φ.colouring v

  monochrome := sorry

  ΩX := sorry
  LX := sorry
  andX := sorry

open Program Formula

mutual
  def ToC2CP' : Program → C2CP'
  | atom  n   => HA n
  | comp  α β => H_comp  (ToC2CP' α) (ToC2CP' β)
  | union α β => H_union (ToC2CP' α) (ToC2CP' β)
  | star  α   => H_star  (ToC2CP' α)
  | test  φ   => H_test  (ToC2CF' φ)

  def ToC2CF' : Formula → C2CF'
  | prop  n  => G_p n
  | nprop n  => G_np n
  | .or  φ ψ => G_or  (ToC2CF' φ) (ToC2CF' ψ)
  | .and φ ψ => G_and (ToC2CF' φ) (ToC2CF' ψ)
  | dim  α φ => G_dim (ToC2CP' α) (ToC2CF' φ)
  | box  α φ => G_box (ToC2CP' α) (ToC2CF' φ)
end

mutual
  def ToC2CP : Program → C2CP
  | atom  n    => ℍA n
  | comp  α β  => ℍ_comp  (ToC2CP α) (ToC2CP β)
  | union α β  => ℍ_union (ToC2CP α) (ToC2CP β)
  | star  α    => ℍ_star  (ToC2CP α)
  | test  φ    => ℍ_test  (ToC2CF φ)

  def ToC2CF : Formula → C2CF
  | prop  n  => 𝔾_p n
  | nprop n  => 𝔾_np n
  | .or  φ ψ => 𝔾_or  (ToC2CF φ) (ToC2CF ψ)
  | .and φ ψ => 𝔾_and (ToC2CF φ) (ToC2CF ψ)
  | dim  α φ => 𝔾_dim (ToC2CP α) (ToC2CF φ)
  | box  α φ => 𝔾_box (ToC2CP α) (ToC2CF φ)
end

mutual
  lemma agreeP (π : Program) : (ToC2CP π).toC2CP' = ToC2CP' π := by
    cases π <;> simp only [ToC2CP, ToC2CP']
    case atom n    => rfl
    case comp α β  => simp only [← agreeP α, ← agreeP β]; rfl
    case union α β => simp only [← agreeP α, ← agreeP β]; rfl
    case star α    => simp only [← agreeP α]; rfl
    case test φ    => simp only [← agreeF φ]; rfl

  lemma agreeF (f : Formula) : (ToC2CF f).toC2CF' = ToC2CF' f := by
    cases f <;> simp only [ToC2CF, ToC2CF']
    case prop    => rfl
    case nprop   => rfl
    case or φ ψ  => simp only [← agreeF φ, ← agreeF ψ]; rfl
    case and φ ψ => simp only [← agreeF φ, ← agreeF ψ]; rfl
    case dim α φ => simp only [← agreeF φ, ← agreeP α]; rfl
    case box α φ => simp only [← agreeF φ, ← agreeP α]; rfl
end

instance {G : C2CF'} : ToString G := ⟨toString ∘ FinEnum.equiv⟩
-- instance {𝔾 : C2CF} : ToString 𝔾 := ⟨toString ∘ FinEnum.equiv⟩
-- instance : Repr C2CF := ⟨fun G _ => let l := FinEnum.toList G
--   s!"Vertices : {repr l}" ++ "\n" ++
--   s!"Labels   : {repr <| G.L <$> l}" ++ "\n" ++
--   s!"Colours  : {repr <| G.Ω <$> l}" ++ "\n" ++
--   s!"Adj      : {repr <| (fun (v, w) => decide (G.E v w)) <$> FinEnum.toList (G × G) }"⟩


-- #eval ToC2CF (Formula.dim (Program.star (Program.star (Program.atom 1))) (Formula.prop 1))