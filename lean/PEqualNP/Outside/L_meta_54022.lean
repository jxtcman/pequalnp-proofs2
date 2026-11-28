import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54022
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [1, 2]⟩,
        ⟨GateOp.or, [0, 4]⟩,
        ⟨GateOp.or, [5, 7]⟩,
        ⟨GateOp.and, [4, 6]⟩,
        ⟨GateOp.or, [2, 3]⟩,
        ⟨GateOp.not, [10]⟩,
        ⟨GateOp.not, [8]⟩,
        ⟨GateOp.or, [12, 9]⟩,
        ⟨GateOp.and, [11, 0]⟩,
        ⟨GateOp.or, [14, 13]⟩ ],
    output := 15 }

end PEqualNP.Outside.L_meta_54022

theorem PEqualNP.Outside.L_meta_54022 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2213811 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_54022.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_54022.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
