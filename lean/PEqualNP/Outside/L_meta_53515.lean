import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53515
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [0, 5]⟩,
        ⟨GateOp.or, [10, 6]⟩,
        ⟨GateOp.or, [7, 8]⟩,
        ⟨GateOp.or, [1, 11]⟩,
        ⟨GateOp.or, [2, 12]⟩,
        ⟨GateOp.or, [1, 9]⟩,
        ⟨GateOp.or, [3, 15]⟩,
        ⟨GateOp.and, [10, 16]⟩,
        ⟨GateOp.or, [17, 14]⟩,
        ⟨GateOp.and, [13, 18]⟩,
        ⟨GateOp.or, [19, 4]⟩ ],
    output := 20 }

end PEqualNP.Outside.L_meta_53515

theorem PEqualNP.Outside.L_meta_53515 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (816889 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_53515.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53515.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
