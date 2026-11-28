import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_57009
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [3, 5]⟩,
        ⟨GateOp.and, [2, 3]⟩,
        ⟨GateOp.or, [1, 2]⟩,
        ⟨GateOp.or, [0, 5]⟩,
        ⟨GateOp.and, [6, 0]⟩,
        ⟨GateOp.not, [8]⟩,
        ⟨GateOp.or, [7, 9]⟩,
        ⟨GateOp.and, [11, 4]⟩,
        ⟨GateOp.not, [13]⟩,
        ⟨GateOp.not, [12]⟩,
        ⟨GateOp.or, [10, 15]⟩,
        ⟨GateOp.and, [14, 16]⟩ ],
    output := 17 }

end PEqualNP.Outside.L_meta_57009

theorem PEqualNP.Outside.L_meta_57009 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2181032 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_57009.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_57009.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
