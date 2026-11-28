import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55036
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [1, 4]⟩,
        ⟨GateOp.or, [2, 5]⟩,
        ⟨GateOp.not, [7]⟩,
        ⟨GateOp.not, [6]⟩,
        ⟨GateOp.and, [2, 6]⟩,
        ⟨GateOp.and, [8, 9]⟩,
        ⟨GateOp.or, [0, 4]⟩,
        ⟨GateOp.or, [1, 9]⟩,
        ⟨GateOp.and, [12, 13]⟩,
        ⟨GateOp.or, [11, 14]⟩,
        ⟨GateOp.or, [10, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55036

theorem PEqualNP.Outside.L_meta_55036 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2164015 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55036.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55036.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
