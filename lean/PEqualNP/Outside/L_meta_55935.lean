import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55935
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.and, [2, 1]⟩,
        ⟨GateOp.and, [3, 4]⟩,
        ⟨GateOp.or, [0, 7]⟩,
        ⟨GateOp.or, [5, 8]⟩,
        ⟨GateOp.or, [6, 9]⟩,
        ⟨GateOp.or, [5, 1]⟩,
        ⟨GateOp.not, [10]⟩,
        ⟨GateOp.or, [2, 11]⟩,
        ⟨GateOp.and, [13, 0]⟩,
        ⟨GateOp.not, [11]⟩,
        ⟨GateOp.or, [14, 12]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55935

theorem PEqualNP.Outside.L_meta_55935 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270648998 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55935.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55935.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
