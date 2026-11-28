import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55930
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.not, [5]⟩,
        ⟨GateOp.or, [1, 3]⟩,
        ⟨GateOp.or, [1, 6]⟩,
        ⟨GateOp.or, [1, 4]⟩,
        ⟨GateOp.or, [3, 2]⟩,
        ⟨GateOp.and, [7, 0]⟩,
        ⟨GateOp.and, [9, 10]⟩,
        ⟨GateOp.or, [8, 0]⟩,
        ⟨GateOp.or, [11, 12]⟩,
        ⟨GateOp.not, [14]⟩,
        ⟨GateOp.and, [15, 13]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55930

theorem PEqualNP.Outside.L_meta_55930 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270585013 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55930.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55930.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
