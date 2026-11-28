import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54933
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [0, 2]⟩,
        ⟨GateOp.or, [3, 5]⟩,
        ⟨GateOp.or, [4, 1]⟩,
        ⟨GateOp.and, [6, 8]⟩,
        ⟨GateOp.or, [2, 1]⟩,
        ⟨GateOp.or, [5, 9]⟩,
        ⟨GateOp.and, [0, 7]⟩,
        ⟨GateOp.not, [11]⟩,
        ⟨GateOp.and, [10, 13]⟩,
        ⟨GateOp.or, [12, 14]⟩,
        ⟨GateOp.or, [8, 1]⟩ ],
    output := 15 }

end PEqualNP.Outside.L_meta_54933

theorem PEqualNP.Outside.L_meta_54933 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50860 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_54933.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_54933.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
