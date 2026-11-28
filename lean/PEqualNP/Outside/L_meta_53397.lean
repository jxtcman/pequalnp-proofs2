import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53397
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [1, 2]⟩,
        ⟨GateOp.not, [5]⟩,
        ⟨GateOp.and, [1, 2]⟩,
        ⟨GateOp.or, [0, 7]⟩,
        ⟨GateOp.and, [4, 6]⟩,
        ⟨GateOp.not, [8]⟩,
        ⟨GateOp.not, [9]⟩,
        ⟨GateOp.or, [6, 10]⟩,
        ⟨GateOp.or, [0, 11]⟩,
        ⟨GateOp.and, [12, 13]⟩ ],
    output := 14 }

end PEqualNP.Outside.L_meta_53397

theorem PEqualNP.Outside.L_meta_53397 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (291673 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53397.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53397.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
