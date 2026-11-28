import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53390
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [1, 4]⟩,
        ⟨GateOp.and, [2, 4]⟩,
        ⟨GateOp.or, [2, 5]⟩,
        ⟨GateOp.and, [3, 7]⟩,
        ⟨GateOp.or, [1, 3]⟩,
        ⟨GateOp.or, [6, 9]⟩,
        ⟨GateOp.and, [10, 10]⟩,
        ⟨GateOp.not, [8]⟩,
        ⟨GateOp.and, [11, 12]⟩,
        ⟨GateOp.or, [0, 13]⟩ ],
    output := 14 }

end PEqualNP.Outside.L_meta_53390

theorem PEqualNP.Outside.L_meta_53390 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (279263 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53390.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53390.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
