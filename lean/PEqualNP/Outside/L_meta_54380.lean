import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54380 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (321455 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨.or, [5, 7]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [8, 0]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [12, 3]⟩, ⟨.or, [13, 11]⟩, ⟨.or, [11, 9]⟩, ⟨.and, [14, 16]⟩, ⟨.or, [17, 6]⟩, ⟨.or, [18, 10]⟩, ⟨.and, [19, 15]⟩], 20⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
