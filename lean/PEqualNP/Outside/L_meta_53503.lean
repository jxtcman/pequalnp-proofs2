import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53503
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [3, 8]⟩,
        ⟨GateOp.or, [2, 7]⟩,
        ⟨GateOp.or, [11, 9]⟩,
        ⟨GateOp.or, [0, 6]⟩,
        ⟨GateOp.or, [4, 5]⟩,
        ⟨GateOp.or, [12, 4]⟩,
        ⟨GateOp.or, [1, 14]⟩,
        ⟨GateOp.or, [11, 10]⟩,
        ⟨GateOp.and, [15, 13]⟩,
        ⟨GateOp.and, [16, 17]⟩,
        ⟨GateOp.or, [19, 18]⟩ ],
    output := 20 }

end PEqualNP.Outside.L_meta_53503

theorem PEqualNP.Outside.L_meta_53503 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (816681 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_53503.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53503.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
