import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56078
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [1, 0]⟩,
        ⟨GateOp.and, [1, 1]⟩,
        ⟨GateOp.not, [6]⟩,
        ⟨GateOp.or, [4, 3]⟩,
        ⟨GateOp.or, [2, 0]⟩,
        ⟨GateOp.and, [6, 9]⟩,
        ⟨GateOp.and, [8, 5]⟩,
        ⟨GateOp.or, [12, 11]⟩,
        ⟨GateOp.and, [10, 7]⟩,
        ⟨GateOp.or, [14, 13]⟩,
        ⟨GateOp.not, [15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_56078

theorem PEqualNP.Outside.L_meta_56078 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274843813 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_56078.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_56078.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
