import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53475
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [7, 9]⟩,
        ⟨GateOp.or, [7, 8]⟩,
        ⟨GateOp.or, [10, 3]⟩,
        ⟨GateOp.or, [0, 5]⟩,
        ⟨GateOp.and, [13, 12]⟩,
        ⟨GateOp.or, [11, 2]⟩,
        ⟨GateOp.or, [14, 4]⟩,
        ⟨GateOp.or, [6, 1]⟩,
        ⟨GateOp.or, [13, 15]⟩,
        ⟨GateOp.and, [17, 18]⟩,
        ⟨GateOp.or, [16, 19]⟩ ],
    output := 20 }

end PEqualNP.Outside.L_meta_53475

theorem PEqualNP.Outside.L_meta_53475 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (808685 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_53475.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53475.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
