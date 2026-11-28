import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55692
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [4, 5]⟩,
        ⟨GateOp.not, [4]⟩,
        ⟨GateOp.or, [1, 3]⟩,
        ⟨GateOp.or, [1, 5]⟩,
        ⟨GateOp.and, [7, 2]⟩,
        ⟨GateOp.or, [8, 10]⟩,
        ⟨GateOp.and, [9, 3]⟩,
        ⟨GateOp.not, [12]⟩,
        ⟨GateOp.and, [0, 6]⟩,
        ⟨GateOp.or, [11, 14]⟩,
        ⟨GateOp.and, [15, 13]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55692

theorem PEqualNP.Outside.L_meta_55692 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6475198 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55692.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55692.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
