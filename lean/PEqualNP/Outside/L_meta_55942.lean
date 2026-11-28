import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55942
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [3, 0]⟩,
        ⟨GateOp.or, [2, 5]⟩,
        ⟨GateOp.or, [5, 1]⟩,
        ⟨GateOp.and, [1, 7]⟩,
        ⟨GateOp.not, [2]⟩,
        ⟨GateOp.or, [9, 0]⟩,
        ⟨GateOp.and, [11, 8]⟩,
        ⟨GateOp.and, [4, 6]⟩,
        ⟨GateOp.or, [13, 8]⟩,
        ⟨GateOp.not, [14]⟩,
        ⟨GateOp.or, [15, 12]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55942

theorem PEqualNP.Outside.L_meta_55942 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270649647 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55942.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55942.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
