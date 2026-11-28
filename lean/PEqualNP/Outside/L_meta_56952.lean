import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56952
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [3, 4]⟩,
        ⟨GateOp.or, [4, 1]⟩,
        ⟨GateOp.not, [5]⟩,
        ⟨GateOp.and, [2, 3]⟩,
        ⟨GateOp.or, [2, 1]⟩,
        ⟨GateOp.or, [0, 8]⟩,
        ⟨GateOp.not, [9]⟩,
        ⟨GateOp.not, [7]⟩,
        ⟨GateOp.and, [6, 10]⟩,
        ⟨GateOp.and, [13, 11]⟩,
        ⟨GateOp.or, [14, 15]⟩,
        ⟨GateOp.and, [16, 12]⟩ ],
    output := 17 }

end PEqualNP.Outside.L_meta_56952

theorem PEqualNP.Outside.L_meta_56952 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2180653 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_56952.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_56952.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
