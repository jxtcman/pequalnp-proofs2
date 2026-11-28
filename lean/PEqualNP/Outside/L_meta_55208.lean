import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55208
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [5, 4]⟩,
        ⟨GateOp.not, [6]⟩,
        ⟨GateOp.not, [2]⟩,
        ⟨GateOp.and, [8, 1]⟩,
        ⟨GateOp.and, [2, 4]⟩,
        ⟨GateOp.and, [3, 7]⟩,
        ⟨GateOp.or, [6, 2]⟩,
        ⟨GateOp.and, [0, 12]⟩,
        ⟨GateOp.or, [10, 13]⟩,
        ⟨GateOp.or, [14, 11]⟩,
        ⟨GateOp.or, [15, 9]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55208

theorem PEqualNP.Outside.L_meta_55208 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2199230 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55208.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55208.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
