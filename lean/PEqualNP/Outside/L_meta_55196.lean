import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55196
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [5, 4]⟩,
        ⟨GateOp.not, [2]⟩,
        ⟨GateOp.or, [1, 6]⟩,
        ⟨GateOp.or, [3, 7]⟩,
        ⟨GateOp.or, [2, 1]⟩,
        ⟨GateOp.not, [8]⟩,
        ⟨GateOp.or, [4, 9]⟩,
        ⟨GateOp.and, [10, 6]⟩,
        ⟨GateOp.or, [0, 13]⟩,
        ⟨GateOp.or, [14, 11]⟩,
        ⟨GateOp.and, [15, 12]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55196

theorem PEqualNP.Outside.L_meta_55196 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2198587 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55196.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55196.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
