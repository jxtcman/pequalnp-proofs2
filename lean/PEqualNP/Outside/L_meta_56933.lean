import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56933
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 5]⟩,
        ⟨GateOp.and, [2, 4]⟩,
        ⟨GateOp.or, [7, 0]⟩,
        ⟨GateOp.or, [4, 6]⟩,
        ⟨GateOp.or, [9, 1]⟩,
        ⟨GateOp.and, [9, 1]⟩,
        ⟨GateOp.not, [10]⟩,
        ⟨GateOp.and, [12, 11]⟩,
        ⟨GateOp.or, [12, 11]⟩,
        ⟨GateOp.or, [3, 10]⟩,
        ⟨GateOp.or, [14, 8]⟩,
        ⟨GateOp.and, [16, 15]⟩ ],
    output := 17 }

end PEqualNP.Outside.L_meta_56933

theorem PEqualNP.Outside.L_meta_56933 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2166078 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_56933.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_56933.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
