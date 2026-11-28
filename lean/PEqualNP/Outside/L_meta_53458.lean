import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53458
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [0, 4]⟩,
        ⟨GateOp.or, [5, 10]⟩,
        ⟨GateOp.or, [7, 2]⟩,
        ⟨GateOp.or, [1, 6]⟩,
        ⟨GateOp.or, [13, 4]⟩,
        ⟨GateOp.and, [12, 14]⟩,
        ⟨GateOp.or, [8, 13]⟩,
        ⟨GateOp.or, [16, 9]⟩,
        ⟨GateOp.or, [3, 17]⟩,
        ⟨GateOp.and, [11, 18]⟩,
        ⟨GateOp.or, [19, 15]⟩ ],
    output := 20 }

end PEqualNP.Outside.L_meta_53458

theorem PEqualNP.Outside.L_meta_53458 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (807668 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_53458.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53458.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
