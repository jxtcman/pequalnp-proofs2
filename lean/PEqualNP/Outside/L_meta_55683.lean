import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55683
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [0, 3]⟩,
        ⟨GateOp.not, [5]⟩,
        ⟨GateOp.or, [1, 7]⟩,
        ⟨GateOp.or, [0, 8]⟩,
        ⟨GateOp.or, [1, 6]⟩,
        ⟨GateOp.or, [2, 10]⟩,
        ⟨GateOp.and, [6, 11]⟩,
        ⟨GateOp.and, [1, 12]⟩,
        ⟨GateOp.not, [13]⟩,
        ⟨GateOp.and, [11, 14]⟩,
        ⟨GateOp.and, [9, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55683

theorem PEqualNP.Outside.L_meta_55683 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6409661 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55683.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55683.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
