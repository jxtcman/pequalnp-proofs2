import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53356
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.not, [3]⟩,
        ⟨GateOp.or, [1, 5]⟩,
        ⟨GateOp.not, [4]⟩,
        ⟨GateOp.or, [2, 6]⟩,
        ⟨GateOp.or, [0, 7]⟩,
        ⟨GateOp.or, [0, 1]⟩,
        ⟨GateOp.and, [2, 10]⟩,
        ⟨GateOp.not, [11]⟩,
        ⟨GateOp.and, [8, 9]⟩,
        ⟨GateOp.and, [12, 13]⟩ ],
    output := 14 }

end PEqualNP.Outside.L_meta_53356

theorem PEqualNP.Outside.L_meta_53356 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (12627 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53356.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53356.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
