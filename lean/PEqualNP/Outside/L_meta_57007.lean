import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_57007
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [0, 3]⟩,
        ⟨GateOp.or, [2, 4]⟩,
        ⟨GateOp.or, [3, 7]⟩,
        ⟨GateOp.or, [1, 6]⟩,
        ⟨GateOp.and, [3, 7]⟩,
        ⟨GateOp.or, [5, 8]⟩,
        ⟨GateOp.or, [2, 9]⟩,
        ⟨GateOp.or, [5, 10]⟩,
        ⟨GateOp.not, [13]⟩,
        ⟨GateOp.or, [0, 14]⟩,
        ⟨GateOp.and, [11, 12]⟩,
        ⟨GateOp.and, [15, 16]⟩ ],
    output := 17 }

end PEqualNP.Outside.L_meta_57007

theorem PEqualNP.Outside.L_meta_57007 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2180924 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_57007.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_57007.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
