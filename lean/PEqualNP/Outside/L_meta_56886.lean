import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56886
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 5]⟩,
        ⟨GateOp.and, [1, 3]⟩,
        ⟨GateOp.and, [0, 1]⟩,
        ⟨GateOp.or, [7, 8]⟩,
        ⟨GateOp.or, [4, 6]⟩,
        ⟨GateOp.or, [9, 10]⟩,
        ⟨GateOp.and, [2, 4]⟩,
        ⟨GateOp.or, [0, 1]⟩,
        ⟨GateOp.and, [5, 13]⟩,
        ⟨GateOp.or, [12, 14]⟩,
        ⟨GateOp.not, [11]⟩,
        ⟨GateOp.or, [15, 16]⟩ ],
    output := 17 }

end PEqualNP.Outside.L_meta_56886

theorem PEqualNP.Outside.L_meta_56886 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2164905 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_56886.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_56886.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
