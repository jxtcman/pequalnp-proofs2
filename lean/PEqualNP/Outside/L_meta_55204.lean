import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55204
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 0]⟩,
        ⟨GateOp.and, [5, 0]⟩,
        ⟨GateOp.or, [7, 1]⟩,
        ⟨GateOp.or, [4, 8]⟩,
        ⟨GateOp.or, [9, 5]⟩,
        ⟨GateOp.and, [10, 3]⟩,
        ⟨GateOp.or, [3, 1]⟩,
        ⟨GateOp.and, [9, 6]⟩,
        ⟨GateOp.or, [13, 12]⟩,
        ⟨GateOp.not, [11]⟩,
        ⟨GateOp.and, [15, 14]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55204

theorem PEqualNP.Outside.L_meta_55204 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2198970 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55204.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55204.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
