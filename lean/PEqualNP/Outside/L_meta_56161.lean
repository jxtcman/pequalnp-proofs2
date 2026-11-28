import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56161
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.and, [1, 5]⟩,
        ⟨GateOp.or, [2, 6]⟩,
        ⟨GateOp.or, [3, 4]⟩,
        ⟨GateOp.or, [2, 5]⟩,
        ⟨GateOp.not, [8]⟩,
        ⟨GateOp.or, [1, 10]⟩,
        ⟨GateOp.not, [9]⟩,
        ⟨GateOp.and, [8, 12]⟩,
        ⟨GateOp.or, [0, 13]⟩,
        ⟨GateOp.and, [7, 11]⟩,
        ⟨GateOp.or, [14, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_56161

theorem PEqualNP.Outside.L_meta_56161 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274878271 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_56161.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_56161.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
