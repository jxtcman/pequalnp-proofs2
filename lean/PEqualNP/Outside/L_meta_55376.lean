import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55376
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 0]⟩,
        ⟨GateOp.and, [6, 1]⟩,
        ⟨GateOp.or, [4, 5]⟩,
        ⟨GateOp.or, [1, 0]⟩,
        ⟨GateOp.not, [7]⟩,
        ⟨GateOp.not, [8]⟩,
        ⟨GateOp.or, [2, 11]⟩,
        ⟨GateOp.or, [3, 8]⟩,
        ⟨GateOp.and, [10, 9]⟩,
        ⟨GateOp.and, [13, 12]⟩,
        ⟨GateOp.or, [14, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55376

theorem PEqualNP.Outside.L_meta_55376 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2330301 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55376.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55376.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
