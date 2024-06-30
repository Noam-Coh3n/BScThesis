import CyclicFormulas.Graph
import CyclicFormulas.Label

open Label Colour Graph

structure C2CF' extends Graph where
  vI : V

namespace C2CF'

variable {G : C2CF'}

instance : Coe C2CF' Graph := ⟨toGraph⟩
instance : CoeSort C2CF' Type := ⟨(V .)⟩
instance : Nonempty G := ⟨G.vI⟩
instance : FinEnum G := G.V_fin

-- equivalent definitions, but decidable instances need workaround via versions
-- with compuational content:
-- def reachr' : G → G → Prop := RTC G.E
-- def reach' : G → G → Prop := TC G.E

def reachr : G → G → Prop := (∃ (n : Fin <| FinEnum.card G), RTCn G.E n . .)
def reach : G → G → Prop := (∃ (n : Fin <| FinEnum.card G + 1), n > 0 ∧ RTCn G.E n . .)

lemma reachr_iff : reachr v w ↔ RTC G.E v w  := sorry
lemma reach_iff  : reach v w ↔ TC' G.E v w := sorry

postfix:50 "*" => RTC
postfix:50 "+" => TC'

instance : DecidableRel G.reach := fun _ _ => Fintype.decidableExistsFintype

end C2CF'

open C2CF'

structure C2CF extends C2CF' where
  -- meaningless in C2CF, but useful for extending to C2CP
  vF : V := vI

  L     : V → Label
  no_cm : ∀ v ≠ vF, ¬ checkmark (L v)

  Ω          : V → Colour
  colouring  : ∀ v, col_admissible (L v) (Ω v)
  monochrome : ∀ v w, (E+) v w → TC' E w v → Ω v = Ω w ∧ Ω v ≠ o

  succ     : V → Option V
  lit_succ : ∀ v w, lit (L v) → ¬ E v w
  prg_succ : ∀ v w, prg (L v) → E v w → succ v = some w
  or_succ  : ∀ v w, L v = .or → Ω v = ν → E v w → (E*) w v → succ v = some w
  and_succ : ∀ v w, L v = .and → Ω v = μ → E v w → (E*) w v → succ v = some w

namespace C2CF

instance : Coe C2CF C2CF' := ⟨toC2CF'⟩
instance : Coe C2CF Graph := ⟨(.)⟩
instance : CoeSort C2CF Type := ⟨(toC2CF' .)⟩
instance : Nonempty (𝔾 : C2CF) := ⟨𝔾.vI⟩
instance : FinEnum (𝔾 : C2CF) := 𝔾.V_fin

end C2CF

@[ext]
structure C2CP' extends C2CF' where
  vF     : V
  i_ne_f : vI ≠ vF

namespace C2CP'

instance : Coe C2CP' C2CF' := ⟨toC2CF'⟩
instance : Coe C2CP' Graph := ⟨(.)⟩
instance : CoeSort C2CP' Type := ⟨(toC2CF' .)⟩

variable {H : C2CP'}

-- H_α.between is called X_α in the thesis
def between : H → Prop := (H.reach . H.vF)

instance : DecidablePred H.between := fun _ => Fintype.decidableExistsFintype

end C2CP'

structure C2CP extends C2CF where
  -- vF     : V
  i_ne_f : vI ≠ vF
  LΩf    : L vF = .prop 0 ∧ Ω vF = .o
  -- no_cm     : ∀ v ≠ vF, ¬ checkmark (L v)

  ΩX   : ∀ v, (E*) v vF → Ω v ≠ ν
  LX   : ∀ v, (E*) v vF → ¬ (match L v with | .box_atom _ => True | _ => False)
  andX : ∀ v, (E*) v vF → L v = .and → ∀ w, E v w →  (E*) w vF → some w = succ v


attribute [simp] C2CP.LΩf

namespace C2CP

instance : Coe C2CP C2CP' := ⟨fun ℍ => ⟨ℍ.toC2CF', ℍ.vF, ℍ.i_ne_f⟩⟩
instance : Coe C2CP C2CF := ⟨toC2CF⟩
instance : Coe C2CP Graph := ⟨(.)⟩
instance : CoeSort C2CP Type := ⟨(V .)⟩

def toC2CP' (ℍ : C2CP) : C2CP' where
  toC2CF' := ℍ
  vF := ℍ.vF
  i_ne_f := i_ne_f ℍ

def between {ℍ : C2CP} : ℍ → Prop := (ℍ.reach . ℍ.vF)

instance {ℍ : C2CP} : DecidablePred ℍ.between := fun _ => Fintype.decidableExistsFintype


@[simp]
lemma final_lit {H : C2CP} : lit (H.L H.vF) := of_eq_true (congr_arg _ H.LΩf.1)

@[simp]
lemma final_no_succ {H : C2CP} : ∀ x, ¬ H.E H.vF x := (H.lit_succ _ . final_lit)

end C2CP