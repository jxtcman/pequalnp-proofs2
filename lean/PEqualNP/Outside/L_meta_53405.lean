import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53405
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.and, [0, 1]⟩,
        ⟨GateOp.or, [4, 5]⟩,
        ⟨GateOp.or, [3, 6]⟩,
        ⟨GateOp.or, [2, 2]⟩,
        ⟨GateOp.or, [0, 1]⟩,
        ⟨GateOp.not, [0]⟩,
        ⟨GateOp.or, [1, 10]⟩,
        ⟨GateOp.and, [8, 9]⟩,
        ⟨GateOp.and, [7, 11]⟩,
        ⟨GateOp.or, [12, 13]⟩,
        ⟨GateOp.not, [14]⟩ ],
    output := 15 }

end PEqualNP.Outside.L_meta_53405

theorem PEqualNP.Outside.L_meta_53405 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4185 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53405.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53405.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
