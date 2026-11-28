import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55548
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 0]⟩,
        ⟨GateOp.or, [5, 3]⟩,
        ⟨GateOp.and, [3, 4]⟩,
        ⟨GateOp.or, [0, 1]⟩,
        ⟨GateOp.or, [6, 3]⟩,
        ⟨GateOp.or, [2, 8]⟩,
        ⟨GateOp.and, [10, 1]⟩,
        ⟨GateOp.not, [12]⟩,
        ⟨GateOp.and, [11, 7]⟩,
        ⟨GateOp.or, [9, 14]⟩,
        ⟨GateOp.and, [13, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55548

theorem PEqualNP.Outside.L_meta_55548 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4361405 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55548.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55548.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
