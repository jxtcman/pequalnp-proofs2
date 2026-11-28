import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56935
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 4]⟩,
        ⟨GateOp.and, [0, 1]⟩,
        ⟨GateOp.or, [0, 1]⟩,
        ⟨GateOp.or, [5, 7]⟩,
        ⟨GateOp.or, [9, 6]⟩,
        ⟨GateOp.and, [2, 4]⟩,
        ⟨GateOp.not, [8]⟩,
        ⟨GateOp.not, [10]⟩,
        ⟨GateOp.or, [11, 8]⟩,
        ⟨GateOp.or, [14, 13]⟩,
        ⟨GateOp.or, [10, 3]⟩,
        ⟨GateOp.and, [16, 15]⟩ ],
    output := 17 }

end PEqualNP.Outside.L_meta_56935

theorem PEqualNP.Outside.L_meta_56935 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2166590 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_56935.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_56935.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
