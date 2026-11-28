import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53497
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 7]⟩,
        ⟨GateOp.or, [10, 9]⟩,
        ⟨GateOp.or, [6, 3]⟩,
        ⟨GateOp.or, [0, 6]⟩,
        ⟨GateOp.or, [11, 8]⟩,
        ⟨GateOp.and, [14, 13]⟩,
        ⟨GateOp.or, [12, 10]⟩,
        ⟨GateOp.or, [15, 4]⟩,
        ⟨GateOp.or, [1, 5]⟩,
        ⟨GateOp.and, [18, 16]⟩,
        ⟨GateOp.or, [17, 19]⟩ ],
    output := 20 }

end PEqualNP.Outside.L_meta_53497

theorem PEqualNP.Outside.L_meta_53497 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (815993 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_53497.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53497.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
