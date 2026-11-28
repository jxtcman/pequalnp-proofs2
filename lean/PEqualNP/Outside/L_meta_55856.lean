import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55856
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [1, 3]⟩,
        ⟨GateOp.or, [4, 6]⟩,
        ⟨GateOp.or, [2, 7]⟩,
        ⟨GateOp.not, [8]⟩,
        ⟨GateOp.and, [0, 9]⟩,
        ⟨GateOp.or, [2, 6]⟩,
        ⟨GateOp.and, [4, 11]⟩,
        ⟨GateOp.or, [0, 5]⟩,
        ⟨GateOp.or, [12, 13]⟩,
        ⟨GateOp.not, [14]⟩,
        ⟨GateOp.or, [10, 15]⟩ ],
    output := 16 }

end PEqualNP.Outside.L_meta_55856

theorem PEqualNP.Outside.L_meta_55856 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270582689 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55856.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55856.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
