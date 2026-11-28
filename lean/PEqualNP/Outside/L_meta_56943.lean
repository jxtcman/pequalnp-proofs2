import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56943
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [1, 2]⟩,
        ⟨GateOp.or, [4, 6]⟩,
        ⟨GateOp.or, [0, 5]⟩,
        ⟨GateOp.or, [7, 8]⟩,
        ⟨GateOp.and, [8, 7]⟩,
        ⟨GateOp.or, [3, 10]⟩,
        ⟨GateOp.not, [11]⟩,
        ⟨GateOp.or, [6, 3]⟩,
        ⟨GateOp.and, [11, 9]⟩,
        ⟨GateOp.not, [14]⟩,
        ⟨GateOp.or, [0, 13]⟩,
        ⟨GateOp.and, [15, 16]⟩ ],
    output := 17 }

end PEqualNP.Outside.L_meta_56943

theorem PEqualNP.Outside.L_meta_56943 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2180513 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_56943.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_56943.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
