import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54931
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.not, [4]⟩,
        ⟨GateOp.or, [0, 2]⟩,
        ⟨GateOp.and, [2, 6]⟩,
        ⟨GateOp.or, [8, 1]⟩,
        ⟨GateOp.and, [1, 7]⟩,
        ⟨GateOp.or, [5, 10]⟩,
        ⟨GateOp.not, [11]⟩,
        ⟨GateOp.or, [4, 3]⟩,
        ⟨GateOp.and, [9, 12]⟩,
        ⟨GateOp.and, [0, 13]⟩,
        ⟨GateOp.or, [15, 14]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_54931

theorem PEqualNP.Outside.L_meta_54931 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50844 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_54931.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_54931.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
