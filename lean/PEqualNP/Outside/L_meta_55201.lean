import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55201
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [5, 4]⟩,
        ⟨GateOp.or, [2, 6]⟩,
        ⟨GateOp.or, [3, 4]⟩,
        ⟨GateOp.or, [7, 1]⟩,
        ⟨GateOp.not, [9]⟩,
        ⟨GateOp.or, [0, 1]⟩,
        ⟨GateOp.and, [2, 8]⟩,
        ⟨GateOp.and, [11, 7]⟩,
        ⟨GateOp.or, [10, 12]⟩,
        ⟨GateOp.or, [13, 14]⟩,
        ⟨GateOp.and, [8, 5]⟩ ],
    output := 15 }

end PEqualNP.Outside.L_meta_55201

theorem PEqualNP.Outside.L_meta_55201 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2198845 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55201.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55201.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
