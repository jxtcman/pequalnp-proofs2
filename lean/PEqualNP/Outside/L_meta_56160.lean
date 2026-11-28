import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56160
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [1, 5]⟩,
        ⟨GateOp.or, [3, 4]⟩,
        ⟨GateOp.and, [2, 7]⟩,
        ⟨GateOp.or, [5, 7]⟩,
        ⟨GateOp.or, [0, 2]⟩,
        ⟨GateOp.or, [6, 8]⟩,
        ⟨GateOp.not, [11]⟩,
        ⟨GateOp.and, [10, 5]⟩,
        ⟨GateOp.and, [1, 9]⟩,
        ⟨GateOp.or, [13, 14]⟩,
        ⟨GateOp.or, [15, 12]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_56160

theorem PEqualNP.Outside.L_meta_56160 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274878013 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_56160.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_56160.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
