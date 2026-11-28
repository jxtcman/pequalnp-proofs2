import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54918
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [5, 3]⟩,
        ⟨GateOp.or, [6, 0]⟩,
        ⟨GateOp.not, [7]⟩,
        ⟨GateOp.not, [4]⟩,
        ⟨GateOp.or, [9, 1]⟩,
        ⟨GateOp.and, [10, 8]⟩,
        ⟨GateOp.and, [6, 0]⟩,
        ⟨GateOp.and, [2, 3]⟩,
        ⟨GateOp.or, [11, 12]⟩,
        ⟨GateOp.or, [13, 14]⟩,
        ⟨GateOp.and, [12, 2]⟩ ],
    output := 15 }

end PEqualNP.Outside.L_meta_54918

theorem PEqualNP.Outside.L_meta_54918 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50600 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_54918.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_54918.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
