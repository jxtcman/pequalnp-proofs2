import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55936
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.and, [3, 4]⟩,
        ⟨GateOp.or, [1, 5]⟩,
        ⟨GateOp.or, [3, 7]⟩,
        ⟨GateOp.or, [0, 6]⟩,
        ⟨GateOp.and, [0, 8]⟩,
        ⟨GateOp.or, [5, 9]⟩,
        ⟨GateOp.or, [2, 11]⟩,
        ⟨GateOp.or, [7, 9]⟩,
        ⟨GateOp.and, [12, 13]⟩,
        ⟨GateOp.not, [14]⟩,
        ⟨GateOp.or, [10, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55936

theorem PEqualNP.Outside.L_meta_55936 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270649002 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55936.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55936.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
