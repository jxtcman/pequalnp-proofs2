import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55007
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.and, [0, 3]⟩,
        ⟨GateOp.and, [1, 4]⟩,
        ⟨GateOp.or, [4, 6]⟩,
        ⟨GateOp.and, [0, 5]⟩,
        ⟨GateOp.or, [5, 8]⟩,
        ⟨GateOp.or, [7, 9]⟩,
        ⟨GateOp.and, [0, 2]⟩,
        ⟨GateOp.or, [1, 10]⟩,
        ⟨GateOp.or, [12, 13]⟩,
        ⟨GateOp.not, [14]⟩,
        ⟨GateOp.or, [11, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55007

theorem PEqualNP.Outside.L_meta_55007 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2147361 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55007.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55007.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
