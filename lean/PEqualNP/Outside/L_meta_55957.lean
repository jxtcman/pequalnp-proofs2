import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55957
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 5]⟩,
        ⟨GateOp.and, [5, 2]⟩,
        ⟨GateOp.not, [6]⟩,
        ⟨GateOp.and, [3, 0]⟩,
        ⟨GateOp.or, [0, 1]⟩,
        ⟨GateOp.or, [1, 3]⟩,
        ⟨GateOp.or, [10, 8]⟩,
        ⟨GateOp.and, [11, 4]⟩,
        ⟨GateOp.not, [13]⟩,
        ⟨GateOp.or, [7, 12]⟩,
        ⟨GateOp.and, [14, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55957

theorem PEqualNP.Outside.L_meta_55957 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270666687 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55957.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55957.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
