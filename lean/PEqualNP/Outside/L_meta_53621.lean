import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53621
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [9, 3]⟩,
        ⟨GateOp.or, [1, 7]⟩,
        ⟨GateOp.or, [6, 0]⟩,
        ⟨GateOp.or, [5, 11]⟩,
        ⟨GateOp.or, [2, 8]⟩,
        ⟨GateOp.or, [14, 12]⟩,
        ⟨GateOp.or, [5, 12]⟩,
        ⟨GateOp.and, [13, 15]⟩,
        ⟨GateOp.and, [10, 16]⟩,
        ⟨GateOp.or, [17, 18]⟩,
        ⟨GateOp.or, [4, 19]⟩ ],
    output := 20 }

end PEqualNP.Outside.L_meta_53621

theorem PEqualNP.Outside.L_meta_53621 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1881451 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_53621.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53621.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
