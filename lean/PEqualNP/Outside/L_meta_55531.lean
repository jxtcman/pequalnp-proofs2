import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55531
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.and, [4, 3]⟩,
        ⟨GateOp.or, [0, 4]⟩,
        ⟨GateOp.or, [3, 1]⟩,
        ⟨GateOp.and, [8, 7]⟩,
        ⟨GateOp.not, [9]⟩,
        ⟨GateOp.or, [1, 0]⟩,
        ⟨GateOp.not, [5]⟩,
        ⟨GateOp.and, [12, 2]⟩,
        ⟨GateOp.or, [6, 13]⟩,
        ⟨GateOp.and, [11, 10]⟩,
        ⟨GateOp.or, [14, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55531

theorem PEqualNP.Outside.L_meta_55531 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4311989 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55531.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55531.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
