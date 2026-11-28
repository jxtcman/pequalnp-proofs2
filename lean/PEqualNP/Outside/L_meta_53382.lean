import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53382
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 2]⟩,
        ⟨GateOp.not, [4]⟩,
        ⟨GateOp.or, [0, 3]⟩,
        ⟨GateOp.or, [0, 6]⟩,
        ⟨GateOp.or, [1, 5]⟩,
        ⟨GateOp.or, [1, 8]⟩,
        ⟨GateOp.and, [7, 9]⟩,
        ⟨GateOp.not, [10]⟩,
        ⟨GateOp.or, [11, 12]⟩,
        ⟨GateOp.not, [13]⟩ ],
    output := 14 }

end PEqualNP.Outside.L_meta_53382

theorem PEqualNP.Outside.L_meta_53382 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266969 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53382.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53382.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
