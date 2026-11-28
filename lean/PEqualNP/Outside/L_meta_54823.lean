import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54823
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [1, 0]⟩,
        ⟨GateOp.and, [2, 3]⟩,
        ⟨GateOp.or, [2, 3]⟩,
        ⟨GateOp.and, [8, 6]⟩,
        ⟨GateOp.or, [7, 9]⟩,
        ⟨GateOp.not, [5]⟩,
        ⟨GateOp.not, [10]⟩,
        ⟨GateOp.or, [11, 8]⟩,
        ⟨GateOp.or, [6, 13]⟩,
        ⟨GateOp.and, [12, 14]⟩ ],
    output := 15 }

end PEqualNP.Outside.L_meta_54823

theorem PEqualNP.Outside.L_meta_54823 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (283331763 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_54823.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_54823.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
