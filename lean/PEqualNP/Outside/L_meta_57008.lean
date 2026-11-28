import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_57008
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 4]⟩,
        ⟨GateOp.and, [6, 1]⟩,
        ⟨GateOp.and, [6, 3]⟩,
        ⟨GateOp.or, [8, 5]⟩,
        ⟨GateOp.not, [9]⟩,
        ⟨GateOp.or, [3, 7]⟩,
        ⟨GateOp.not, [1]⟩,
        ⟨GateOp.or, [10, 0]⟩,
        ⟨GateOp.and, [0, 12]⟩,
        ⟨GateOp.or, [2, 14]⟩,
        ⟨GateOp.or, [15, 11]⟩,
        ⟨GateOp.and, [16, 13]⟩ ],
    output := 17 }

end PEqualNP.Outside.L_meta_57008

theorem PEqualNP.Outside.L_meta_57008 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2180925 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_57008.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_57008.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
