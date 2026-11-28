import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53460
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [0, 4]⟩,
        ⟨GateOp.or, [9, 1]⟩,
        ⟨GateOp.or, [6, 10]⟩,
        ⟨GateOp.or, [8, 3]⟩,
        ⟨GateOp.or, [2, 7]⟩,
        ⟨GateOp.or, [1, 12]⟩,
        ⟨GateOp.or, [11, 13]⟩,
        ⟨GateOp.or, [10, 5]⟩,
        ⟨GateOp.and, [17, 16]⟩,
        ⟨GateOp.and, [15, 14]⟩,
        ⟨GateOp.or, [19, 18]⟩ ],
    output := 20 }

end PEqualNP.Outside.L_meta_53460

theorem PEqualNP.Outside.L_meta_53460 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (807672 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_53460.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53460.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
