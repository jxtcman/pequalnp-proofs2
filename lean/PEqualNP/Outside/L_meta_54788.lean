import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54788
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [0, 3]⟩,
        ⟨GateOp.not, [5]⟩,
        ⟨GateOp.or, [0, 7]⟩,
        ⟨GateOp.or, [1, 2]⟩,
        ⟨GateOp.or, [1, 2]⟩,
        ⟨GateOp.or, [8, 10]⟩,
        ⟨GateOp.or, [4, 6]⟩,
        ⟨GateOp.and, [9, 12]⟩,
        ⟨GateOp.not, [13]⟩,
        ⟨GateOp.and, [11, 14]⟩ ],
    output := 15 }

end PEqualNP.Outside.L_meta_54788

theorem PEqualNP.Outside.L_meta_54788 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274876857 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_54788.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_54788.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
