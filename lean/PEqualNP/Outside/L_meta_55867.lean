import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55867
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.and, [3, 1]⟩,
        ⟨GateOp.or, [6, 4]⟩,
        ⟨GateOp.or, [3, 5]⟩,
        ⟨GateOp.or, [2, 8]⟩,
        ⟨GateOp.and, [0, 9]⟩,
        ⟨GateOp.and, [7, 9]⟩,
        ⟨GateOp.or, [11, 5]⟩,
        ⟨GateOp.or, [0, 12]⟩,
        ⟨GateOp.and, [0, 6]⟩,
        ⟨GateOp.not, [13]⟩,
        ⟨GateOp.or, [10, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55867

theorem PEqualNP.Outside.L_meta_55867 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270583212 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55867.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55867.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
