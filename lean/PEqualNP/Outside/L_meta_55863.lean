import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55863
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [3, 2]⟩,
        ⟨GateOp.and, [4, 6]⟩,
        ⟨GateOp.and, [1, 3]⟩,
        ⟨GateOp.or, [7, 0]⟩,
        ⟨GateOp.or, [8, 9]⟩,
        ⟨GateOp.or, [10, 5]⟩,
        ⟨GateOp.not, [11]⟩,
        ⟨GateOp.and, [4, 0]⟩,
        ⟨GateOp.or, [5, 1]⟩,
        ⟨GateOp.and, [14, 0]⟩,
        ⟨GateOp.or, [12, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55863

theorem PEqualNP.Outside.L_meta_55863 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270583202 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55863.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55863.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
