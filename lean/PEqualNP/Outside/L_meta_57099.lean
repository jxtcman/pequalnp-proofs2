import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_57099
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [0, 3]⟩,
        ⟨GateOp.not, [4]⟩,
        ⟨GateOp.or, [7, 2]⟩,
        ⟨GateOp.or, [1, 2]⟩,
        ⟨GateOp.and, [6, 9]⟩,
        ⟨GateOp.not, [10]⟩,
        ⟨GateOp.not, [5]⟩,
        ⟨GateOp.or, [12, 1]⟩,
        ⟨GateOp.and, [8, 13]⟩,
        ⟨GateOp.or, [0, 14]⟩,
        ⟨GateOp.and, [15, 11]⟩,
        ⟨GateOp.not, [2]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_57099

theorem PEqualNP.Outside.L_meta_57099 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2181561 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_57099.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_57099.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
