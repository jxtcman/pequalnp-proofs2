import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_57104
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 4]⟩,
        ⟨GateOp.and, [6, 3]⟩,
        ⟨GateOp.or, [7, 5]⟩,
        ⟨GateOp.not, [5]⟩,
        ⟨GateOp.or, [0, 1]⟩,
        ⟨GateOp.or, [3, 2]⟩,
        ⟨GateOp.and, [0, 1]⟩,
        ⟨GateOp.not, [8]⟩,
        ⟨GateOp.or, [11, 12]⟩,
        ⟨GateOp.and, [10, 8]⟩,
        ⟨GateOp.and, [13, 14]⟩,
        ⟨GateOp.or, [15, 16]⟩ ],
    output := 17 }

end PEqualNP.Outside.L_meta_57104

theorem PEqualNP.Outside.L_meta_57104 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2181934 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_57104.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_57104.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
