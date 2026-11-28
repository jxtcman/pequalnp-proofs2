import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56003
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [0, 4]⟩,
        ⟨GateOp.or, [1, 2]⟩,
        ⟨GateOp.and, [7, 6]⟩,
        ⟨GateOp.not, [5]⟩,
        ⟨GateOp.or, [2, 4]⟩,
        ⟨GateOp.or, [8, 3]⟩,
        ⟨GateOp.and, [11, 10]⟩,
        ⟨GateOp.not, [12]⟩,
        ⟨GateOp.or, [0, 9]⟩,
        ⟨GateOp.or, [14, 7]⟩,
        ⟨GateOp.and, [15, 13]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_56003

theorem PEqualNP.Outside.L_meta_56003 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270683067 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_56003.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_56003.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
