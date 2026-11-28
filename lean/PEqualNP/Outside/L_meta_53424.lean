import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53424
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.and, [0, 1]⟩,
        ⟨GateOp.and, [2, 3]⟩,
        ⟨GateOp.or, [0, 1]⟩,
        ⟨GateOp.or, [6, 7]⟩,
        ⟨GateOp.or, [4, 8]⟩,
        ⟨GateOp.not, [9]⟩,
        ⟨GateOp.and, [4, 7]⟩,
        ⟨GateOp.or, [10, 11]⟩,
        ⟨GateOp.or, [5, 12]⟩ ],
    output := 13 }

end PEqualNP.Outside.L_meta_53424

theorem PEqualNP.Outside.L_meta_53424 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 14 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266770 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53424.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53424.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
