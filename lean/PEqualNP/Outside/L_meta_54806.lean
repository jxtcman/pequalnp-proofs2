import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54806
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [4, 3]⟩,
        ⟨GateOp.or, [5, 3]⟩,
        ⟨GateOp.and, [7, 4]⟩,
        ⟨GateOp.or, [2, 8]⟩,
        ⟨GateOp.or, [1, 9]⟩,
        ⟨GateOp.or, [0, 10]⟩,
        ⟨GateOp.and, [10, 6]⟩,
        ⟨GateOp.or, [11, 6]⟩,
        ⟨GateOp.not, [12]⟩,
        ⟨GateOp.and, [14, 13]⟩ ],
    output := 15 }

end PEqualNP.Outside.L_meta_54806

theorem PEqualNP.Outside.L_meta_54806 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (279071167 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_54806.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_54806.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
