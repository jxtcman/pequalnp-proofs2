import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_57092
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [3, 1]⟩,
        ⟨GateOp.and, [2, 3]⟩,
        ⟨GateOp.and, [3, 4]⟩,
        ⟨GateOp.not, [6]⟩,
        ⟨GateOp.and, [0, 9]⟩,
        ⟨GateOp.or, [5, 7]⟩,
        ⟨GateOp.or, [2, 6]⟩,
        ⟨GateOp.or, [11, 8]⟩,
        ⟨GateOp.or, [0, 13]⟩,
        ⟨GateOp.not, [14]⟩,
        ⟨GateOp.and, [12, 15]⟩,
        ⟨GateOp.or, [16, 10]⟩ ],
    output := 17 }

end PEqualNP.Outside.L_meta_57092

theorem PEqualNP.Outside.L_meta_57092 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2181045 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_57092.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_57092.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
