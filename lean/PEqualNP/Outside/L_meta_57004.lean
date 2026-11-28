import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_57004
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [3, 0]⟩,
        ⟨GateOp.and, [4, 1]⟩,
        ⟨GateOp.or, [2, 4]⟩,
        ⟨GateOp.and, [6, 8]⟩,
        ⟨GateOp.and, [4, 1]⟩,
        ⟨GateOp.or, [2, 10]⟩,
        ⟨GateOp.and, [5, 0]⟩,
        ⟨GateOp.or, [3, 11]⟩,
        ⟨GateOp.or, [5, 9]⟩,
        ⟨GateOp.not, [14]⟩,
        ⟨GateOp.and, [15, 13]⟩,
        ⟨GateOp.or, [16, 12]⟩ ],
    output := 17 }

end PEqualNP.Outside.L_meta_57004

theorem PEqualNP.Outside.L_meta_57004 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2180904 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_57004.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_57004.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
