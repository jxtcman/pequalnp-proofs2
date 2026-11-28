import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55952
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [3, 1]⟩,
        ⟨GateOp.or, [5, 0]⟩,
        ⟨GateOp.or, [3, 5]⟩,
        ⟨GateOp.or, [1, 0]⟩,
        ⟨GateOp.and, [6, 4]⟩,
        ⟨GateOp.or, [7, 10]⟩,
        ⟨GateOp.not, [11]⟩,
        ⟨GateOp.and, [8, 9]⟩,
        ⟨GateOp.or, [13, 12]⟩,
        ⟨GateOp.and, [4, 0]⟩,
        ⟨GateOp.or, [15, 14]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55952

theorem PEqualNP.Outside.L_meta_55952 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270650296 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55952.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55952.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
