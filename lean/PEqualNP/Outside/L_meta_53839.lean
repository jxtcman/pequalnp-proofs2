import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53839
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.not, [0]⟩,
        ⟨GateOp.and, [1, 6]⟩,
        ⟨GateOp.or, [4, 5]⟩,
        ⟨GateOp.or, [3, 8]⟩,
        ⟨GateOp.and, [6, 9]⟩,
        ⟨GateOp.or, [1, 10]⟩,
        ⟨GateOp.not, [11]⟩,
        ⟨GateOp.or, [7, 12]⟩ ],
    output := 13 }

end PEqualNP.Outside.L_meta_53839

theorem PEqualNP.Outside.L_meta_53839 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (20413 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53839.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53839.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
