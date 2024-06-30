import CyclicFormulas.myInstances

structure Graph where
  V : Type
  [V_fin : FinEnum V]

  E : V → V → Prop
  [E_dec : DecidableRel E]

instance : CoeSort Graph Type := ⟨Graph.V⟩

namespace Graph

variable {G : Graph}

def neighborSet (v : G) : Set G := {w | G.E v w}

-- Type of edges in G
def edges (G : Graph) := Subtype (Function.uncurry G.E)


section instances
  variable {G : Graph} {u v w : G}

  instance instFinEnumGraph : FinEnum G              := G.V_fin
  instance instDecRelAdj    : DecidableRel G.E       := G.E_dec
  instance instDecPredAdj   : DecidablePred <| G.E v := G.E_dec v
  instance instDecAdj       : Decidable <| G.E v w   := G.E_dec ..
  instance instDecEqGraph   : DecidableEq G.V        := G.V_fin.decEq
  instance instFinEnumEdges : FinEnum <| G.edges     := .Subtype.finEnum _
end instances

section Sum
  open Sum

  @[simp]
  protected def Sum (G₁ G₂ : Graph) : Graph where
    V := G₁.V ⊕ G₂.V
    E := LiftRel G₁.E G₂.E

  infixl:80 " ⊎ " => Graph.Sum

  unif_hint (G₁ G₂ : Graph) where
    ⊢ (G₁ ⊎ G₂).V ≟ G₁.V ⊕ G₂.V

  unif_hint (G₁ G₂ : Graph) where
    ⊢ G₁.V ⊕ G₂.V ≟ (G₁ ⊎ G₂).V

end Sum
