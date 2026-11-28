import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55420
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 5]⟩,
        ⟨GateOp.not, [4]⟩,
        ⟨GateOp.and, [0, 6]⟩,
        ⟨GateOp.or, [0, 2]⟩,
        ⟨GateOp.or, [3, 7]⟩,
        ⟨GateOp.or, [9, 10]⟩,
        ⟨GateOp.or, [1, 4]⟩,
        ⟨GateOp.and, [3, 9]⟩,
        ⟨GateOp.or, [12, 13]⟩,
        ⟨GateOp.or, [8, 14]⟩,
        ⟨GateOp.and, [11, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55420

theorem PEqualNP.Outside.L_meta_55420 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4295614 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55420.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55420.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
