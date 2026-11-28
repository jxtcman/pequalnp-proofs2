import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55921
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 1]⟩,
        ⟨GateOp.or, [0, 1]⟩,
        ⟨GateOp.or, [0, 4]⟩,
        ⟨GateOp.not, [7]⟩,
        ⟨GateOp.or, [3, 6]⟩,
        ⟨GateOp.and, [8, 10]⟩,
        ⟨GateOp.and, [3, 7]⟩,
        ⟨GateOp.and, [5, 9]⟩,
        ⟨GateOp.or, [11, 13]⟩,
        ⟨GateOp.or, [14, 12]⟩,
        ⟨GateOp.not, [15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55921

theorem PEqualNP.Outside.L_meta_55921 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270584241 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55921.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55921.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
