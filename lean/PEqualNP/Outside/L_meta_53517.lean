import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53517
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [7, 2]⟩,
        ⟨GateOp.or, [8, 10]⟩,
        ⟨GateOp.or, [5, 1]⟩,
        ⟨GateOp.or, [6, 0]⟩,
        ⟨GateOp.or, [4, 12]⟩,
        ⟨GateOp.or, [11, 9]⟩,
        ⟨GateOp.and, [15, 13]⟩,
        ⟨GateOp.or, [3, 11]⟩,
        ⟨GateOp.or, [17, 6]⟩,
        ⟨GateOp.and, [14, 18]⟩,
        ⟨GateOp.or, [16, 19]⟩ ],
    output := 20 }

end PEqualNP.Outside.L_meta_53517

theorem PEqualNP.Outside.L_meta_53517 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (816952 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_53517.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53517.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
