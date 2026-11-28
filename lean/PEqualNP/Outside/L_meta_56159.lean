import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56159
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [0, 2]⟩,
        ⟨GateOp.or, [3, 4]⟩,
        ⟨GateOp.not, [5]⟩,
        ⟨GateOp.or, [6, 4]⟩,
        ⟨GateOp.and, [7, 2]⟩,
        ⟨GateOp.or, [6, 1]⟩,
        ⟨GateOp.or, [11, 8]⟩,
        ⟨GateOp.or, [10, 1]⟩,
        ⟨GateOp.and, [13, 9]⟩,
        ⟨GateOp.not, [14]⟩,
        ⟨GateOp.and, [15, 12]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_56159

theorem PEqualNP.Outside.L_meta_56159 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274877117 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_56159.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_56159.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
