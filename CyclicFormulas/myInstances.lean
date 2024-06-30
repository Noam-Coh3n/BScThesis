import Mathlib.Data.FinEnum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin

instance FinEnumBool : FinEnum Bool := FinEnum.ofList [true, false] (by simp)

instance instUnionRelation {α β : Type _}: Union (α → β → Prop) where
  union r s x y := r x y ∨ s x y

instance instUnionPredicate {α : Type _}: Union (α → Prop) where
  union p q x := p x ∨ q x

instance instInterPredicate {α : Type _}: Inter (α → Prop) where
  inter p q x := p x ∧ q x

instance instSingletonPred : Singleton α (α → Prop) := ⟨(Eq .)⟩

instance instInsertPred : Insert α (α → Prop) := ⟨fun a p => Eq a ∪ p⟩

instance instEmptyPred {α : Type} : EmptyCollection (α → Prop)
  := ⟨fun _ => False⟩

instance instEmptyRel {α β : Type} : EmptyCollection (α → β → Prop)
  := ⟨fun _ _ => False⟩

instance instDecSingletonPred {a : α} [DecidableEq α] : DecidablePred {a} := decEq a

instance instDecInsertPred {a : α} [DecidableEq α] [DecidablePred p] :
  DecidablePred (insert a p) := fun _ => Or.decidable

instance instDecEmptyPred :
  DecidablePred (∅ : α → Prop) := fun _ => decidableFalse

instance instDecPredEmptyRel :
  (a : α) → DecidablePred ((∅ : α → β → Prop) a) := fun _ _ => decidableFalse

inductive RTCn {α : Type} (r : α → α → Prop) : ℕ → α → α → Prop
| refl : RTCn r 0 a a
| tail {b c : α} : RTCn r n a b → r b c → RTCn r (n+1) a c

@[inline]
def RTC {α : Type} (r : α → α → Prop) := Relation.ReflTransGen r

@[inline]
def TC' {α : Type} (r : α → α → Prop) := Relation.TransGen r


theorem RTC_iff_RTCn {r : α → α → Prop} {a b : α} : RTC r a b ↔ ∃n, RTCn r n a b := by
  constructor
  . intro h; induction h with
    | refl => exact ⟨0, RTCn.refl⟩
    | tail _ h₁ e => match e with | ⟨n, h₂⟩ => exact ⟨n+1, RTCn.tail h₂ h₁⟩
  . rintro ⟨n, h⟩; induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ h₁ h₂ => exact Relation.ReflTransGen.tail h₂ h₁

theorem RTC_zero : RTCn r 0 a b ↔ a = b := by
  constructor
  . intro h; cases h; rfl
  . simp_all only [RTCn.refl, implies_true]

theorem RTC_succ : RTCn r (n+1) a c ↔ ∃b, RTCn r n a b ∧ r b c := by
  constructor
  . rintro (_ | @⟨_, _, b, _, h₁, h₂⟩); exact ⟨b, ⟨h₁, h₂⟩⟩
  . rintro ⟨_, ⟨h₁, h₂⟩⟩; exact RTCn.tail h₁ h₂

instance decRTCn {r : α → α → Prop} [FinEnum α] [DecidableRel r] : ∀n, DecidableRel <| RTCn r n
  | .zero => fun _ _ => decidable_of_iff' _ RTC_zero
  | .succ n => have := @decRTCn _ r _ _ n; fun _ _ => decidable_of_iff' _ RTC_succ
