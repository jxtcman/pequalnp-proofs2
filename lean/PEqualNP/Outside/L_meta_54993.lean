import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54993
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 5]⟩,
        ⟨GateOp.and, [0, 6]⟩,
        ⟨GateOp.and, [2, 3]⟩,
        ⟨GateOp.or, [5, 8]⟩,
        ⟨GateOp.or, [1, 4]⟩,
        ⟨GateOp.or, [9, 10]⟩,
        ⟨GateOp.not, [11]⟩,
        ⟨GateOp.or, [7, 12]⟩,
        ⟨GateOp.or, [2, 4]⟩,
        ⟨GateOp.and, [1, 14]⟩,
        ⟨GateOp.or, [13, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_54993

theorem PEqualNP.Outside.L_meta_54993 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2114861 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_54993.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_54993.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
