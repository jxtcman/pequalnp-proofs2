import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56200
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [3, 4]⟩,
        ⟨GateOp.or, [5, 6]⟩,
        ⟨GateOp.or, [5, 2]⟩,
        ⟨GateOp.or, [1, 2]⟩,
        ⟨GateOp.or, [7, 9]⟩,
        ⟨GateOp.not, [8]⟩,
        ⟨GateOp.and, [9, 7]⟩,
        ⟨GateOp.or, [11, 0]⟩,
        ⟨GateOp.and, [13, 10]⟩,
        ⟨GateOp.or, [12, 7]⟩,
        ⟨GateOp.or, [12, 14]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_56200

theorem PEqualNP.Outside.L_meta_56200 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274960062 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_56200.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_56200.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
