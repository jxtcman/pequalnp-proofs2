import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54020
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [0, 2]⟩,
        ⟨GateOp.or, [1, 6]⟩,
        ⟨GateOp.and, [2, 0]⟩,
        ⟨GateOp.and, [6, 1]⟩,
        ⟨GateOp.or, [4, 5]⟩,
        ⟨GateOp.and, [7, 4]⟩,
        ⟨GateOp.or, [8, 9]⟩,
        ⟨GateOp.or, [10, 12]⟩,
        ⟨GateOp.not, [13]⟩,
        ⟨GateOp.or, [14, 11]⟩ ],
    output := 15 }

end PEqualNP.Outside.L_meta_54020

theorem PEqualNP.Outside.L_meta_54020 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2213529 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_54020.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_54020.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
