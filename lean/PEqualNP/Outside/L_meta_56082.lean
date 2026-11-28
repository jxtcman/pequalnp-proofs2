import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56082
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.and, [1, 5]⟩,
        ⟨GateOp.or, [2, 6]⟩,
        ⟨GateOp.or, [1, 5]⟩,
        ⟨GateOp.and, [0, 8]⟩,
        ⟨GateOp.not, [8]⟩,
        ⟨GateOp.or, [4, 7]⟩,
        ⟨GateOp.or, [3, 11]⟩,
        ⟨GateOp.and, [1, 7]⟩,
        ⟨GateOp.or, [10, 13]⟩,
        ⟨GateOp.and, [12, 14]⟩,
        ⟨GateOp.or, [9, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_56082

theorem PEqualNP.Outside.L_meta_56082 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274843966 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_56082.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_56082.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
