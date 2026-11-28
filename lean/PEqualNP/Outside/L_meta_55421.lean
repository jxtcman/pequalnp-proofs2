import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55421
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [3, 2]⟩,
        ⟨GateOp.and, [3, 2]⟩,
        ⟨GateOp.or, [7, 4]⟩,
        ⟨GateOp.not, [1]⟩,
        ⟨GateOp.and, [8, 6]⟩,
        ⟨GateOp.or, [10, 0]⟩,
        ⟨GateOp.or, [4, 9]⟩,
        ⟨GateOp.or, [11, 1]⟩,
        ⟨GateOp.or, [12, 6]⟩,
        ⟨GateOp.or, [14, 5]⟩,
        ⟨GateOp.and, [13, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55421

theorem PEqualNP.Outside.L_meta_55421 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4296509 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55421.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55421.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
