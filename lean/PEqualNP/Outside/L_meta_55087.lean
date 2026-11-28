import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55087
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 3]⟩,
        ⟨GateOp.or, [4, 2]⟩,
        ⟨GateOp.not, [6]⟩,
        ⟨GateOp.and, [7, 3]⟩,
        ⟨GateOp.or, [1, 6]⟩,
        ⟨GateOp.and, [8, 0]⟩,
        ⟨GateOp.or, [5, 9]⟩,
        ⟨GateOp.or, [0, 12]⟩,
        ⟨GateOp.not, [13]⟩,
        ⟨GateOp.and, [10, 14]⟩,
        ⟨GateOp.or, [15, 11]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55087

theorem PEqualNP.Outside.L_meta_55087 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2181043 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55087.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55087.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
