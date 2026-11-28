import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53840
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 5]⟩,
        ⟨GateOp.or, [1, 3]⟩,
        ⟨GateOp.and, [1, 3]⟩,
        ⟨GateOp.or, [6, 7]⟩,
        ⟨GateOp.not, [9]⟩,
        ⟨GateOp.and, [2, 7]⟩,
        ⟨GateOp.or, [8, 11]⟩,
        ⟨GateOp.and, [0, 10]⟩,
        ⟨GateOp.or, [12, 13]⟩ ],
    output := 14 }

end PEqualNP.Outside.L_meta_53840

theorem PEqualNP.Outside.L_meta_53840 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33553 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53840.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53840.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
