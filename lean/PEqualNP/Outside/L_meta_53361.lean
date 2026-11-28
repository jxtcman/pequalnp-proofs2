import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53361
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [3, 4]⟩,
        ⟨GateOp.or, [0, 5]⟩,
        ⟨GateOp.not, [6]⟩,
        ⟨GateOp.or, [0, 7]⟩,
        ⟨GateOp.and, [2, 3]⟩,
        ⟨GateOp.or, [5, 7]⟩,
        ⟨GateOp.and, [1, 4]⟩,
        ⟨GateOp.or, [8, 11]⟩,
        ⟨GateOp.and, [10, 12]⟩,
        ⟨GateOp.or, [9, 13]⟩ ],
    output := 14 }

end PEqualNP.Outside.L_meta_53361

theorem PEqualNP.Outside.L_meta_53361 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (13016 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53361.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53361.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
