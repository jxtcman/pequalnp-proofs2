import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54962
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 0]⟩,
        ⟨GateOp.or, [3, 4]⟩,
        ⟨GateOp.and, [7, 6]⟩,
        ⟨GateOp.or, [6, 4]⟩,
        ⟨GateOp.not, [9]⟩,
        ⟨GateOp.or, [5, 2]⟩,
        ⟨GateOp.not, [3]⟩,
        ⟨GateOp.and, [1, 10]⟩,
        ⟨GateOp.and, [11, 0]⟩,
        ⟨GateOp.or, [14, 13]⟩,
        ⟨GateOp.or, [15, 8]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_54962

theorem PEqualNP.Outside.L_meta_54962 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (101052 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_54962.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_54962.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
