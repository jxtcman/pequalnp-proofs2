import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56937
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [3, 5]⟩,
        ⟨GateOp.or, [1, 2]⟩,
        ⟨GateOp.or, [4, 5]⟩,
        ⟨GateOp.and, [1, 2]⟩,
        ⟨GateOp.and, [6, 8]⟩,
        ⟨GateOp.or, [0, 6]⟩,
        ⟨GateOp.or, [9, 11]⟩,
        ⟨GateOp.or, [7, 11]⟩,
        ⟨GateOp.or, [7, 10]⟩,
        ⟨GateOp.and, [12, 14]⟩,
        ⟨GateOp.not, [15]⟩,
        ⟨GateOp.and, [13, 16]⟩ ],
    output := 17 }

end PEqualNP.Outside.L_meta_56937

theorem PEqualNP.Outside.L_meta_56937 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2180249 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_56937.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_56937.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
