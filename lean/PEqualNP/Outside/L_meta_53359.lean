import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53359
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.and, [0, 0]⟩,
        ⟨GateOp.and, [0, 4]⟩,
        ⟨GateOp.not, [0]⟩,
        ⟨GateOp.or, [1, 2]⟩,
        ⟨GateOp.not, [4]⟩,
        ⟨GateOp.or, [3, 7]⟩,
        ⟨GateOp.or, [5, 8]⟩,
        ⟨GateOp.and, [9, 10]⟩,
        ⟨GateOp.or, [6, 12]⟩,
        ⟨GateOp.and, [11, 13]⟩ ],
    output := 14 }

end PEqualNP.Outside.L_meta_53359

theorem PEqualNP.Outside.L_meta_53359 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (12760 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53359.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53359.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
