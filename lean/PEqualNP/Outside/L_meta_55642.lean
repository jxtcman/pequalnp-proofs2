import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55642
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [1, 0]⟩,
        ⟨GateOp.or, [6, 2]⟩,
        ⟨GateOp.and, [4, 1]⟩,
        ⟨GateOp.not, [5]⟩,
        ⟨GateOp.or, [3, 7]⟩,
        ⟨GateOp.and, [7, 3]⟩,
        ⟨GateOp.or, [11, 8]⟩,
        ⟨GateOp.not, [12]⟩,
        ⟨GateOp.or, [9, 6]⟩,
        ⟨GateOp.and, [13, 14]⟩,
        ⟨GateOp.and, [10, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55642

theorem PEqualNP.Outside.L_meta_55642 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6375863 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55642.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55642.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
