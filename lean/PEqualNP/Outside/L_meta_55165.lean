import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55165
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [1, 4]⟩,
        ⟨GateOp.or, [5, 4]⟩,
        ⟨GateOp.or, [7, 0]⟩,
        ⟨GateOp.not, [8]⟩,
        ⟨GateOp.and, [1, 5]⟩,
        ⟨GateOp.or, [10, 2]⟩,
        ⟨GateOp.and, [9, 3]⟩,
        ⟨GateOp.and, [6, 11]⟩,
        ⟨GateOp.and, [0, 7]⟩,
        ⟨GateOp.or, [14, 12]⟩,
        ⟨GateOp.or, [13, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55165

theorem PEqualNP.Outside.L_meta_55165 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2198320 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55165.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55165.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
