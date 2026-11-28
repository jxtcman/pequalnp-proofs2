import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56936
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [1, 2]⟩,
        ⟨GateOp.and, [1, 2]⟩,
        ⟨GateOp.and, [6, 0]⟩,
        ⟨GateOp.not, [4]⟩,
        ⟨GateOp.or, [7, 8]⟩,
        ⟨GateOp.or, [0, 6]⟩,
        ⟨GateOp.or, [9, 11]⟩,
        ⟨GateOp.and, [11, 3]⟩,
        ⟨GateOp.or, [13, 5]⟩,
        ⟨GateOp.or, [10, 14]⟩,
        ⟨GateOp.not, [15]⟩,
        ⟨GateOp.and, [12, 16]⟩ ],
    output := 17 }

end PEqualNP.Outside.L_meta_56936

theorem PEqualNP.Outside.L_meta_56936 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2180241 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_56936.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_56936.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
