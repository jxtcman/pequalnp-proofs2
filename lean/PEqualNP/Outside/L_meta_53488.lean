import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53488
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 9]⟩,
        ⟨GateOp.or, [5, 4]⟩,
        ⟨GateOp.or, [1, 11]⟩,
        ⟨GateOp.or, [10, 8]⟩,
        ⟨GateOp.or, [7, 2]⟩,
        ⟨GateOp.or, [0, 6]⟩,
        ⟨GateOp.or, [15, 3]⟩,
        ⟨GateOp.or, [14, 16]⟩,
        ⟨GateOp.and, [15, 13]⟩,
        ⟨GateOp.or, [18, 12]⟩,
        ⟨GateOp.and, [17, 19]⟩ ],
    output := 20 }

end PEqualNP.Outside.L_meta_53488

theorem PEqualNP.Outside.L_meta_53488 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (815923 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_53488.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53488.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
