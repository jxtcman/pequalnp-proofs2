import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56091
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [1, 4]⟩,
        ⟨GateOp.or, [4, 3]⟩,
        ⟨GateOp.or, [1, 5]⟩,
        ⟨GateOp.and, [7, 8]⟩,
        ⟨GateOp.or, [0, 7]⟩,
        ⟨GateOp.or, [10, 6]⟩,
        ⟨GateOp.or, [2, 9]⟩,
        ⟨GateOp.or, [11, 2]⟩,
        ⟨GateOp.and, [11, 12]⟩,
        ⟨GateOp.not, [14]⟩,
        ⟨GateOp.and, [15, 13]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_56091

theorem PEqualNP.Outside.L_meta_56091 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274876603 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_56091.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_56091.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
