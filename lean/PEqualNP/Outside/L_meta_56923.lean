import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56923
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.and, [2, 4]⟩,
        ⟨GateOp.or, [4, 5]⟩,
        ⟨GateOp.or, [0, 6]⟩,
        ⟨GateOp.or, [2, 7]⟩,
        ⟨GateOp.or, [0, 9]⟩,
        ⟨GateOp.and, [1, 5]⟩,
        ⟨GateOp.or, [3, 9]⟩,
        ⟨GateOp.and, [8, 12]⟩,
        ⟨GateOp.not, [10]⟩,
        ⟨GateOp.or, [13, 14]⟩,
        ⟨GateOp.or, [11, 15]⟩,
        ⟨GateOp.or, [15, 16]⟩ ],
    output := 17 }

end PEqualNP.Outside.L_meta_56923

theorem PEqualNP.Outside.L_meta_56923 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2165436 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_56923.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_56923.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
