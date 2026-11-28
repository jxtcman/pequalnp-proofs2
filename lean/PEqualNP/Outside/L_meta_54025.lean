import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54025
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.not, [4]⟩,
        ⟨GateOp.or, [2, 3]⟩,
        ⟨GateOp.not, [5]⟩,
        ⟨GateOp.or, [6, 2]⟩,
        ⟨GateOp.or, [8, 1]⟩,
        ⟨GateOp.and, [9, 10]⟩,
        ⟨GateOp.and, [7, 0]⟩,
        ⟨GateOp.not, [12]⟩,
        ⟨GateOp.or, [11, 0]⟩,
        ⟨GateOp.and, [13, 14]⟩ ],
    output := 15 }

end PEqualNP.Outside.L_meta_54025

theorem PEqualNP.Outside.L_meta_54025 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2214835 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_54025.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_54025.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
