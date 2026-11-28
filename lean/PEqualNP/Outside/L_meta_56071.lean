import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56071
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [0, 4]⟩,
        ⟨GateOp.and, [2, 6]⟩,
        ⟨GateOp.or, [1, 4]⟩,
        ⟨GateOp.not, [5]⟩,
        ⟨GateOp.or, [0, 1]⟩,
        ⟨GateOp.and, [3, 8]⟩,
        ⟨GateOp.or, [2, 9]⟩,
        ⟨GateOp.or, [7, 11]⟩,
        ⟨GateOp.not, [13]⟩,
        ⟨GateOp.or, [10, 12]⟩,
        ⟨GateOp.and, [14, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_56071

theorem PEqualNP.Outside.L_meta_56071 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270716347 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_56071.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_56071.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
