import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55849
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 5]⟩,
        ⟨GateOp.or, [4, 3]⟩,
        ⟨GateOp.and, [4, 3]⟩,
        ⟨GateOp.and, [7, 2]⟩,
        ⟨GateOp.or, [5, 8]⟩,
        ⟨GateOp.and, [6, 0]⟩,
        ⟨GateOp.or, [0, 10]⟩,
        ⟨GateOp.or, [9, 12]⟩,
        ⟨GateOp.or, [4, 9]⟩,
        ⟨GateOp.not, [13]⟩,
        ⟨GateOp.or, [15, 11]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55849

theorem PEqualNP.Outside.L_meta_55849 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270550948 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55849.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55849.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
