import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54831
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 4]⟩,
        ⟨GateOp.or, [0, 3]⟩,
        ⟨GateOp.and, [2, 4]⟩,
        ⟨GateOp.not, [8]⟩,
        ⟨GateOp.and, [3, 6]⟩,
        ⟨GateOp.not, [10]⟩,
        ⟨GateOp.or, [1, 7]⟩,
        ⟨GateOp.and, [6, 9]⟩,
        ⟨GateOp.or, [12, 13]⟩,
        ⟨GateOp.and, [11, 14]⟩ ],
    output := 15 }

end PEqualNP.Outside.L_meta_54831

theorem PEqualNP.Outside.L_meta_54831 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (815943615 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_54831.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_54831.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
