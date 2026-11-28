import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53845
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [4, 5]⟩,
        ⟨GateOp.or, [2, 6]⟩,
        ⟨GateOp.and, [0, 7]⟩,
        ⟨GateOp.or, [0, 6]⟩,
        ⟨GateOp.not, [9]⟩,
        ⟨GateOp.and, [3, 7]⟩,
        ⟨GateOp.or, [1, 11]⟩,
        ⟨GateOp.and, [10, 12]⟩,
        ⟨GateOp.or, [8, 13]⟩ ],
    output := 14 }

end PEqualNP.Outside.L_meta_53845

theorem PEqualNP.Outside.L_meta_53845 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33716 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53845.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53845.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
