import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56548
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [1, 5]⟩,
        ⟨GateOp.or, [0, 1]⟩,
        ⟨GateOp.or, [7, 4]⟩,
        ⟨GateOp.and, [6, 0]⟩,
        ⟨GateOp.or, [8, 6]⟩,
        ⟨GateOp.not, [10]⟩,
        ⟨GateOp.or, [3, 4]⟩,
        ⟨GateOp.or, [2, 6]⟩,
        ⟨GateOp.or, [9, 12]⟩,
        ⟨GateOp.and, [11, 13]⟩,
        ⟨GateOp.and, [14, 7]⟩,
        ⟨GateOp.or, [15, 16]⟩ ],
    output := 17 }

end PEqualNP.Outside.L_meta_56548

theorem PEqualNP.Outside.L_meta_56548 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50746 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_56548.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_56548.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
