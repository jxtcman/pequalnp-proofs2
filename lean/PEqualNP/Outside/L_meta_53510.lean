import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53510
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 7]⟩,
        ⟨GateOp.or, [6, 1]⟩,
        ⟨GateOp.or, [3, 10]⟩,
        ⟨GateOp.or, [5, 0]⟩,
        ⟨GateOp.or, [0, 8]⟩,
        ⟨GateOp.or, [10, 14]⟩,
        ⟨GateOp.and, [11, 15]⟩,
        ⟨GateOp.or, [12, 9]⟩,
        ⟨GateOp.or, [4, 16]⟩,
        ⟨GateOp.and, [17, 13]⟩,
        ⟨GateOp.or, [18, 19]⟩ ],
    output := 20 }

end PEqualNP.Outside.L_meta_53510

theorem PEqualNP.Outside.L_meta_53510 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (816749 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_53510.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53510.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
