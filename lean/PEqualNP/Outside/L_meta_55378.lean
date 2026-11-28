import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55378
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [4, 5]⟩,
        ⟨GateOp.and, [0, 1]⟩,
        ⟨GateOp.or, [0, 1]⟩,
        ⟨GateOp.or, [2, 7]⟩,
        ⟨GateOp.not, [6]⟩,
        ⟨GateOp.or, [10, 8]⟩,
        ⟨GateOp.and, [8, 9]⟩,
        ⟨GateOp.or, [11, 9]⟩,
        ⟨GateOp.not, [12]⟩,
        ⟨GateOp.and, [6, 4]⟩,
        ⟨GateOp.and, [13, 14]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55378

theorem PEqualNP.Outside.L_meta_55378 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2346681 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55378.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55378.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
