import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56178
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 5]⟩,
        ⟨GateOp.and, [1, 1]⟩,
        ⟨GateOp.not, [6]⟩,
        ⟨GateOp.or, [3, 4]⟩,
        ⟨GateOp.not, [4]⟩,
        ⟨GateOp.or, [0, 2]⟩,
        ⟨GateOp.and, [5, 7]⟩,
        ⟨GateOp.and, [8, 9]⟩,
        ⟨GateOp.and, [10, 11]⟩,
        ⟨GateOp.or, [12, 13]⟩,
        ⟨GateOp.or, [14, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_56178

theorem PEqualNP.Outside.L_meta_56178 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274911039 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_56178.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_56178.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
