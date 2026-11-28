import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53456
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [3, 8]⟩,
        ⟨GateOp.or, [0, 5]⟩,
        ⟨GateOp.or, [9, 10]⟩,
        ⟨GateOp.or, [7, 2]⟩,
        ⟨GateOp.or, [6, 1]⟩,
        ⟨GateOp.or, [4, 11]⟩,
        ⟨GateOp.or, [11, 13]⟩,
        ⟨GateOp.or, [4, 14]⟩,
        ⟨GateOp.and, [17, 16]⟩,
        ⟨GateOp.and, [15, 12]⟩,
        ⟨GateOp.or, [18, 19]⟩ ],
    output := 20 }

end PEqualNP.Outside.L_meta_53456

theorem PEqualNP.Outside.L_meta_53456 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (807605 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_53456.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53456.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
