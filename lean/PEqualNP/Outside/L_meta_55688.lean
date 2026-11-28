import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55688
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 3]⟩,
        ⟨GateOp.or, [1, 2]⟩,
        ⟨GateOp.not, [6]⟩,
        ⟨GateOp.or, [5, 8]⟩,
        ⟨GateOp.or, [0, 7]⟩,
        ⟨GateOp.and, [2, 4]⟩,
        ⟨GateOp.or, [1, 11]⟩,
        ⟨GateOp.or, [9, 12]⟩,
        ⟨GateOp.not, [13]⟩,
        ⟨GateOp.and, [9, 10]⟩,
        ⟨GateOp.or, [14, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55688

theorem PEqualNP.Outside.L_meta_55688 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6474943 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55688.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55688.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
