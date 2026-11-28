import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55024
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.and, [0, 2]⟩,
        ⟨GateOp.or, [6, 1]⟩,
        ⟨GateOp.not, [4]⟩,
        ⟨GateOp.or, [3, 0]⟩,
        ⟨GateOp.or, [7, 8]⟩,
        ⟨GateOp.and, [7, 9]⟩,
        ⟨GateOp.not, [11]⟩,
        ⟨GateOp.not, [5]⟩,
        ⟨GateOp.and, [10, 13]⟩,
        ⟨GateOp.or, [14, 0]⟩,
        ⟨GateOp.and, [12, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55024

theorem PEqualNP.Outside.L_meta_55024 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2147769 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55024.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55024.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
