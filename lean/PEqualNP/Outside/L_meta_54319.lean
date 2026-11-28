import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54319
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [5, 6]⟩,
        ⟨GateOp.or, [0, 4]⟩,
        ⟨GateOp.or, [11, 5]⟩,
        ⟨GateOp.or, [3, 10]⟩,
        ⟨GateOp.or, [9, 8]⟩,
        ⟨GateOp.or, [7, 12]⟩,
        ⟨GateOp.or, [1, 14]⟩,
        ⟨GateOp.or, [11, 2]⟩,
        ⟨GateOp.and, [16, 15]⟩,
        ⟨GateOp.and, [17, 13]⟩,
        ⟨GateOp.or, [18, 19]⟩ ],
    output := 20 }

end PEqualNP.Outside.L_meta_54319

theorem PEqualNP.Outside.L_meta_54319 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (287478 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_54319.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_54319.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
