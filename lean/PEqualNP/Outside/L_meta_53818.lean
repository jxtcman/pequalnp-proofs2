import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53818
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.not, [3]⟩,
        ⟨GateOp.or, [4, 5]⟩,
        ⟨GateOp.and, [2, 6]⟩,
        ⟨GateOp.not, [7]⟩,
        ⟨GateOp.or, [1, 8]⟩,
        ⟨GateOp.and, [9, 10]⟩,
        ⟨GateOp.or, [3, 4]⟩,
        ⟨GateOp.and, [0, 12]⟩,
        ⟨GateOp.or, [11, 13]⟩ ],
    output := 14 }

end PEqualNP.Outside.L_meta_53818

theorem PEqualNP.Outside.L_meta_53818 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17310 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53818.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53818.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
