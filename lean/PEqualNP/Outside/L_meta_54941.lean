import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54941
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [4, 3]⟩,
        ⟨GateOp.or, [4, 5]⟩,
        ⟨GateOp.and, [6, 1]⟩,
        ⟨GateOp.or, [7, 0]⟩,
        ⟨GateOp.not, [9]⟩,
        ⟨GateOp.or, [1, 6]⟩,
        ⟨GateOp.and, [10, 2]⟩,
        ⟨GateOp.or, [11, 7]⟩,
        ⟨GateOp.and, [13, 0]⟩,
        ⟨GateOp.or, [14, 8]⟩,
        ⟨GateOp.or, [15, 12]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_54941

theorem PEqualNP.Outside.L_meta_54941 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (51002 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_54941.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_54941.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
