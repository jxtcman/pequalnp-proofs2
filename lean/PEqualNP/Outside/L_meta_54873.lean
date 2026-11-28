import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54873
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.and, [1, 3]⟩,
        ⟨GateOp.or, [2, 1]⟩,
        ⟨GateOp.or, [3, 4]⟩,
        ⟨GateOp.or, [0, 8]⟩,
        ⟨GateOp.or, [0, 2]⟩,
        ⟨GateOp.and, [7, 9]⟩,
        ⟨GateOp.or, [5, 11]⟩,
        ⟨GateOp.not, [12]⟩,
        ⟨GateOp.and, [1, 5]⟩,
        ⟨GateOp.and, [13, 10]⟩,
        ⟨GateOp.or, [6, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_54873

theorem PEqualNP.Outside.L_meta_54873 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17177 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_54873.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_54873.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
