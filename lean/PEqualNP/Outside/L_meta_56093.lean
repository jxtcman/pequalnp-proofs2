import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56093
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 1]⟩,
        ⟨GateOp.or, [0, 3]⟩,
        ⟨GateOp.or, [6, 0]⟩,
        ⟨GateOp.or, [5, 8]⟩,
        ⟨GateOp.not, [8]⟩,
        ⟨GateOp.or, [10, 4]⟩,
        ⟨GateOp.and, [7, 6]⟩,
        ⟨GateOp.or, [11, 12]⟩,
        ⟨GateOp.and, [9, 13]⟩,
        ⟨GateOp.not, [14]⟩,
        ⟨GateOp.or, [8, 6]⟩ ],
    output := 15 }

end PEqualNP.Outside.L_meta_56093

theorem PEqualNP.Outside.L_meta_56093 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274876841 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_56093.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_56093.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
