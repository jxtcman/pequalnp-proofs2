import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55159
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 3]⟩,
        ⟨GateOp.or, [0, 5]⟩,
        ⟨GateOp.or, [7, 4]⟩,
        ⟨GateOp.and, [6, 8]⟩,
        ⟨GateOp.not, [9]⟩,
        ⟨GateOp.and, [2, 4]⟩,
        ⟨GateOp.or, [3, 0]⟩,
        ⟨GateOp.and, [7, 1]⟩,
        ⟨GateOp.and, [10, 12]⟩,
        ⟨GateOp.or, [13, 14]⟩,
        ⟨GateOp.or, [11, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55159

theorem PEqualNP.Outside.L_meta_55159 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2198067 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55159.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55159.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
