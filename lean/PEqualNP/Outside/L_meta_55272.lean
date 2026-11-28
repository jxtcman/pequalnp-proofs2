import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55272
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.not, [2]⟩,
        ⟨GateOp.or, [0, 1]⟩,
        ⟨GateOp.and, [4, 6]⟩,
        ⟨GateOp.or, [0, 8]⟩,
        ⟨GateOp.or, [5, 9]⟩,
        ⟨GateOp.and, [7, 6]⟩,
        ⟨GateOp.not, [10]⟩,
        ⟨GateOp.and, [3, 1]⟩,
        ⟨GateOp.or, [11, 12]⟩,
        ⟨GateOp.not, [13]⟩,
        ⟨GateOp.and, [14, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55272

theorem PEqualNP.Outside.L_meta_55272 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2215355 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55272.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55272.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
