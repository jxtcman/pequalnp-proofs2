import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53838
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [0, 1]⟩,
        ⟨GateOp.not, [2]⟩,
        ⟨GateOp.or, [4, 6]⟩,
        ⟨GateOp.or, [3, 8]⟩,
        ⟨GateOp.or, [5, 9]⟩,
        ⟨GateOp.not, [10]⟩,
        ⟨GateOp.and, [6, 7]⟩,
        ⟨GateOp.or, [11, 12]⟩ ],
    output := 13 }

end PEqualNP.Outside.L_meta_53838

theorem PEqualNP.Outside.L_meta_53838 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (20155 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53838.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53838.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
