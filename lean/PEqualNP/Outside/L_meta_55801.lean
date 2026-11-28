import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55801
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 1]⟩,
        ⟨GateOp.and, [4, 6]⟩,
        ⟨GateOp.or, [3, 0]⟩,
        ⟨GateOp.or, [6, 4]⟩,
        ⟨GateOp.and, [9, 8]⟩,
        ⟨GateOp.and, [5, 0]⟩,
        ⟨GateOp.or, [10, 7]⟩,
        ⟨GateOp.or, [12, 5]⟩,
        ⟨GateOp.not, [13]⟩,
        ⟨GateOp.or, [11, 14]⟩,
        ⟨GateOp.not, [3]⟩ ],
    output := 15 }

end PEqualNP.Outside.L_meta_55801

theorem PEqualNP.Outside.L_meta_55801 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270549417 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55801.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55801.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
