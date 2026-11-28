import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_57094
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [1, 0]⟩,
        ⟨GateOp.or, [3, 2]⟩,
        ⟨GateOp.or, [1, 3]⟩,
        ⟨GateOp.or, [4, 2]⟩,
        ⟨GateOp.and, [8, 9]⟩,
        ⟨GateOp.or, [6, 5]⟩,
        ⟨GateOp.and, [11, 7]⟩,
        ⟨GateOp.not, [10]⟩,
        ⟨GateOp.or, [12, 10]⟩,
        ⟨GateOp.not, [14]⟩,
        ⟨GateOp.or, [6, 7]⟩,
        ⟨GateOp.and, [15, 16]⟩ ],
    output := 17 }

end PEqualNP.Outside.L_meta_57094

theorem PEqualNP.Outside.L_meta_57094 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2181299 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_57094.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_57094.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
