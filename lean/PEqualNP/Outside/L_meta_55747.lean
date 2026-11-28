import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55747
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [3, 2]⟩,
        ⟨GateOp.or, [4, 5]⟩,
        ⟨GateOp.or, [1, 0]⟩,
        ⟨GateOp.and, [1, 0]⟩,
        ⟨GateOp.or, [7, 9]⟩,
        ⟨GateOp.or, [10, 6]⟩,
        ⟨GateOp.not, [10]⟩,
        ⟨GateOp.and, [6, 7]⟩,
        ⟨GateOp.or, [13, 11]⟩,
        ⟨GateOp.or, [13, 8]⟩,
        ⟨GateOp.and, [15, 14]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55747

theorem PEqualNP.Outside.L_meta_55747 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (12783422 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55747.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55747.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
