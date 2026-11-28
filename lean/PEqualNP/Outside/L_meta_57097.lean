import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_57097
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [1, 3]⟩,
        ⟨GateOp.or, [1, 5]⟩,
        ⟨GateOp.or, [7, 6]⟩,
        ⟨GateOp.and, [7, 3]⟩,
        ⟨GateOp.or, [4, 9]⟩,
        ⟨GateOp.or, [2, 10]⟩,
        ⟨GateOp.and, [11, 8]⟩,
        ⟨GateOp.or, [0, 2]⟩,
        ⟨GateOp.not, [12]⟩,
        ⟨GateOp.or, [6, 13]⟩,
        ⟨GateOp.and, [12, 13]⟩,
        ⟨GateOp.and, [15, 14]⟩ ],
    output := 17 }

end PEqualNP.Outside.L_meta_57097

theorem PEqualNP.Outside.L_meta_57097 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2181311 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_57097.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_57097.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
