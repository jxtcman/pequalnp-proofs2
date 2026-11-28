import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56945
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 1]⟩,
        ⟨GateOp.and, [5, 0]⟩,
        ⟨GateOp.or, [6, 4]⟩,
        ⟨GateOp.or, [0, 3]⟩,
        ⟨GateOp.and, [8, 9]⟩,
        ⟨GateOp.or, [6, 3]⟩,
        ⟨GateOp.not, [11]⟩,
        ⟨GateOp.or, [10, 5]⟩,
        ⟨GateOp.or, [13, 12]⟩,
        ⟨GateOp.not, [14]⟩,
        ⟨GateOp.not, [12]⟩,
        ⟨GateOp.or, [15, 7]⟩ ],
    output := 17 }

end PEqualNP.Outside.L_meta_56945

theorem PEqualNP.Outside.L_meta_56945 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2180520 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_56945.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_56945.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
