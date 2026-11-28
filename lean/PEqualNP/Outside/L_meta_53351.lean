import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53351
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [3, 4]⟩,
        ⟨GateOp.or, [0, 1]⟩,
        ⟨GateOp.not, [5]⟩,
        ⟨GateOp.and, [0, 0]⟩,
        ⟨GateOp.and, [0, 1]⟩,
        ⟨GateOp.and, [5, 6]⟩,
        ⟨GateOp.and, [2, 7]⟩,
        ⟨GateOp.and, [8, 9]⟩,
        ⟨GateOp.or, [11, 12]⟩,
        ⟨GateOp.or, [10, 13]⟩ ],
    output := 14 }

end PEqualNP.Outside.L_meta_53351

theorem PEqualNP.Outside.L_meta_53351 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (5022 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53351.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53351.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
