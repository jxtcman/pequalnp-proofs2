import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53834
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [3, 4]⟩,
        ⟨GateOp.or, [5, 6]⟩,
        ⟨GateOp.not, [7]⟩,
        ⟨GateOp.and, [2, 8]⟩,
        ⟨GateOp.and, [0, 7]⟩,
        ⟨GateOp.or, [9, 10]⟩,
        ⟨GateOp.or, [0, 6]⟩,
        ⟨GateOp.and, [1, 12]⟩,
        ⟨GateOp.or, [11, 13]⟩ ],
    output := 14 }

end PEqualNP.Outside.L_meta_53834

theorem PEqualNP.Outside.L_meta_53834 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18238 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53834.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53834.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
