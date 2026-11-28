import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53482
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [8, 7]⟩,
        ⟨GateOp.or, [4, 0]⟩,
        ⟨GateOp.or, [5, 2]⟩,
        ⟨GateOp.or, [10, 9]⟩,
        ⟨GateOp.or, [6, 3]⟩,
        ⟨GateOp.or, [11, 1]⟩,
        ⟨GateOp.or, [11, 14]⟩,
        ⟨GateOp.or, [3, 13]⟩,
        ⟨GateOp.and, [17, 15]⟩,
        ⟨GateOp.and, [12, 16]⟩,
        ⟨GateOp.or, [18, 19]⟩ ],
    output := 20 }

end PEqualNP.Outside.L_meta_53482

theorem PEqualNP.Outside.L_meta_53482 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (810554 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_53482.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53482.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
