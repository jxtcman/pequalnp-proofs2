import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53350
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [1, 4]⟩,
        ⟨GateOp.not, [2]⟩,
        ⟨GateOp.or, [3, 5]⟩,
        ⟨GateOp.and, [0, 7]⟩,
        ⟨GateOp.or, [8, 8]⟩,
        ⟨GateOp.or, [1, 9]⟩,
        ⟨GateOp.or, [6, 7]⟩,
        ⟨GateOp.not, [11]⟩,
        ⟨GateOp.and, [6, 10]⟩,
        ⟨GateOp.or, [12, 13]⟩ ],
    output := 14 }

end PEqualNP.Outside.L_meta_53350

theorem PEqualNP.Outside.L_meta_53350 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4958 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53350.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53350.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
