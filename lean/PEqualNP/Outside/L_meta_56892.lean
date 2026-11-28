import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56892
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [0, 5]⟩,
        ⟨GateOp.or, [1, 2]⟩,
        ⟨GateOp.or, [1, 4]⟩,
        ⟨GateOp.or, [0, 7]⟩,
        ⟨GateOp.or, [4, 6]⟩,
        ⟨GateOp.or, [2, 5]⟩,
        ⟨GateOp.not, [10]⟩,
        ⟨GateOp.not, [7]⟩,
        ⟨GateOp.or, [9, 12]⟩,
        ⟨GateOp.and, [8, 11]⟩,
        ⟨GateOp.or, [13, 15]⟩,
        ⟨GateOp.and, [14, 16]⟩ ],
    output := 17 }

end PEqualNP.Outside.L_meta_56892

theorem PEqualNP.Outside.L_meta_56892 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2165049 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_56892.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_56892.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
