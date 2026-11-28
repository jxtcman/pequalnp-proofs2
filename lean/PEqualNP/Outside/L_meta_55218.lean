import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55218
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.and, [2, 1]⟩,
        ⟨GateOp.not, [4]⟩,
        ⟨GateOp.not, [5]⟩,
        ⟨GateOp.or, [8, 1]⟩,
        ⟨GateOp.or, [7, 2]⟩,
        ⟨GateOp.and, [3, 0]⟩,
        ⟨GateOp.and, [10, 9]⟩,
        ⟨GateOp.or, [12, 0]⟩,
        ⟨GateOp.or, [11, 6]⟩,
        ⟨GateOp.not, [14]⟩,
        ⟨GateOp.and, [15, 13]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55218

theorem PEqualNP.Outside.L_meta_55218 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2214583 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55218.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55218.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
