import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53844
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.and, [2, 3]⟩,
        ⟨GateOp.or, [0, 6]⟩,
        ⟨GateOp.or, [0, 4]⟩,
        ⟨GateOp.and, [1, 8]⟩,
        ⟨GateOp.or, [5, 9]⟩,
        ⟨GateOp.not, [10]⟩,
        ⟨GateOp.or, [1, 7]⟩,
        ⟨GateOp.and, [11, 12]⟩ ],
    output := 13 }

end PEqualNP.Outside.L_meta_53844

theorem PEqualNP.Outside.L_meta_53844 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33693 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53844.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53844.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
