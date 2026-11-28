import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53423
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.and, [1, 3]⟩,
        ⟨GateOp.or, [1, 3]⟩,
        ⟨GateOp.and, [2, 6]⟩,
        ⟨GateOp.or, [4, 5]⟩,
        ⟨GateOp.or, [2, 6]⟩,
        ⟨GateOp.or, [7, 8]⟩,
        ⟨GateOp.not, [10]⟩,
        ⟨GateOp.and, [9, 11]⟩,
        ⟨GateOp.and, [0, 8]⟩,
        ⟨GateOp.or, [12, 13]⟩ ],
    output := 14 }

end PEqualNP.Outside.L_meta_53423

theorem PEqualNP.Outside.L_meta_53423 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 14 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266334 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53423.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53423.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
