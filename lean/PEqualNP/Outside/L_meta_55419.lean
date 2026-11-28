import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55419
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [0, 4]⟩,
        ⟨GateOp.or, [3, 6]⟩,
        ⟨GateOp.and, [2, 7]⟩,
        ⟨GateOp.or, [3, 1]⟩,
        ⟨GateOp.or, [0, 1]⟩,
        ⟨GateOp.and, [6, 9]⟩,
        ⟨GateOp.and, [11, 10]⟩,
        ⟨GateOp.or, [10, 11]⟩,
        ⟨GateOp.or, [13, 8]⟩,
        ⟨GateOp.not, [12]⟩,
        ⟨GateOp.and, [14, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55419

theorem PEqualNP.Outside.L_meta_55419 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4295605 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55419.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55419.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
