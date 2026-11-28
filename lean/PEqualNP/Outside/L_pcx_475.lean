import Mathlib
import PEqualNP.Defs

-- Lower bound: for every flip pattern on one 3 x 3 block, a table gives four permutations no two of which
-- can share a lattice piece (their oriented meet or join is not a permutation matrix); products of these give
-- 4 ^ m words in distinct pieces. Upper bound: flipping cells 01, 02, 10 splits the six permutations of a block
-- into two comparable pairs and two singletons; products of the four classes are the pieces.

namespace PEqualNP.Outside.L_pcx_475

def q0 (i j : Fin 3) : Bool := decide ((i = 0 ∧ j ≠ 0) ∨ (i = 1 ∧ j = 0))

def cls (s : Equiv.Perm (Fin 3)) : Fin 4 :=
  if s 2 = 2 then 0 else if s 2 = 1 then 1 else if s 0 = 2 then 2 else 3

theorem ub_block : ∀ x y : Equiv.Perm (Fin 3), cls x = cls y →
    ((∀ i j, (((x i = j ∧ y i = j) ∧ ¬ q0 i j = true) ∨ ((x i = j ∨ y i = j) ∧ q0 i j = true)) ↔
        x i = j) ∨
      (∀ i j, (((x i = j ∧ y i = j) ∧ ¬ q0 i j = true) ∨ ((x i = j ∨ y i = j) ∧ q0 i j = true)) ↔
        y i = j)) ∧
    ((∀ i j, (((x i = j ∨ y i = j) ∧ ¬ q0 i j = true) ∨ ((x i = j ∧ y i = j) ∧ q0 i j = true)) ↔
        x i = j) ∨
      (∀ i j, (((x i = j ∨ y i = j) ∧ ¬ q0 i j = true) ∨ ((x i = j ∧ y i = j) ∧ q0 i j = true)) ↔
        y i = j)) := by
  decide

def ex1 (f : Fin 3 → Bool) : Bool :=
  (f 0 && !f 1 && !f 2) || (!f 0 && f 1 && !f 2) || (!f 0 && !f 1 && f 2)

def any3 (f : Fin 3 → Bool) : Bool := f 0 || f 1 || f 2

def permB (g : Fin 3 → Fin 3 → Bool) : Bool :=
  ex1 (g 0) && ex1 (g 1) && ex1 (g 2) &&
    any3 (fun i => g i 0) && any3 (fun i => g i 1) && any3 (fun i => g i 2)

def meetB (q : Fin 3 → Fin 3 → Bool) (x y : Fin 3 → Fin 3) (i j : Fin 3) : Bool :=
  (decide (x i = j) && decide (y i = j) && !q i j) ||
    ((decide (x i = j) || decide (y i = j)) && q i j)

def joinB (q : Fin 3 → Fin 3 → Bool) (x y : Fin 3 → Fin 3) (i j : Fin 3) : Bool :=
  ((decide (x i = j) || decide (y i = j)) && !q i j) ||
    (decide (x i = j) && decide (y i = j) && q i j)

def pp (k : Fin 6) : Equiv.Perm (Fin 3) :=
  match k.val with
  | 0 => 1
  | 1 => Equiv.swap 0 1
  | 2 => Equiv.swap 0 2
  | 3 => Equiv.swap 1 2
  | 4 => Equiv.swap 0 1 * Equiv.swap 1 2
  | _ => Equiv.swap 1 2 * Equiv.swap 0 1

def qn (n : Nat) : Fin 4 → Fin 6 :=
  match n with
  | 0 => ![0, 1, 2, 3]
  | 1 => ![0, 1, 2, 4]
  | 2 => ![0, 1, 2, 5]
  | 3 => ![0, 1, 3, 4]
  | 4 => ![0, 1, 3, 5]
  | 5 => ![0, 1, 4, 5]
  | 6 => ![0, 2, 3, 4]
  | 7 => ![0, 2, 3, 5]
  | 8 => ![0, 2, 4, 5]
  | 9 => ![0, 3, 4, 5]
  | 10 => ![1, 2, 3, 4]
  | 11 => ![1, 2, 3, 5]
  | 12 => ![1, 2, 4, 5]
  | 13 => ![1, 3, 4, 5]
  | _ => ![2, 3, 4, 5]

def tbl : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 6, 0, 0, 6, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 6, 0, 0, 6, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 4, 0, 0, 0, 7, 0, 3, 0, 12, 0, 0, 6, 0, 0, 3, 9, 4, 0, 0, 0, 0, 0, 3, 0, 5, 0, 0, 0, 0, 0, 4, 0, 4, 0, 0, 0, 7, 0, 3, 0, 11, 0, 0, 6, 0, 0, 4, 6, 4, 0, 0, 0, 0, 0, 3, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 6, 0, 0, 7, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 13, 5, 1, 1, 10, 1, 0, 8, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 6, 0, 3, 0, 10, 0, 0, 6, 0, 0, 3, 7, 3, 0, 0, 0, 0, 0, 3, 0, 3, 0, 2, 2, 2, 2, 14, 8, 11, 2, 1, 1, 11, 2, 10, 1, 10, 1, 0, 6, 0, 0, 9, 6, 4, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 4, 6, 9, 0, 0, 6, 0, 1, 10, 1, 10, 2, 11, 1, 1, 2, 11, 8, 14, 2, 2, 2, 2, 0, 3, 0, 3, 0, 0, 0, 0, 0, 3, 7, 3, 0, 0, 6, 0, 0, 10, 0, 3, 0, 6, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 8, 0, 1, 10, 1, 1, 5, 13, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 7, 0, 0, 6, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 3, 0, 0, 0, 0, 0, 4, 6, 4, 0, 0, 6, 0, 0, 11, 0, 3, 0, 7, 0, 0, 0, 4, 0, 4, 0, 0, 0, 0, 0, 5, 0, 3, 0, 0, 0, 0, 0, 4, 9, 3, 0, 0, 6, 0, 0, 12, 0, 3, 0, 7, 0, 0, 0, 4, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 6, 0, 0, 6, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 6, 0, 0, 6, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def mkq (b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool) : Fin 3 → Fin 3 → Bool := fun i j =>
  match i.val, j.val with
  | 0, 0 => b0
  | 0, 1 => b1
  | 0, 2 => b2
  | 1, 0 => b3
  | 1, 1 => b4
  | 1, 2 => b5
  | 2, 0 => b6
  | 2, 1 => b7
  | _, _ => b8

theorem mkq_eq (q : Fin 3 → Fin 3 → Bool) :
    mkq (q 0 0) (q 0 1) (q 0 2) (q 1 0) (q 1 1) (q 1 2) (q 2 0) (q 2 1) (q 2 2) = q := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

def quadFor (b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool) : Fin 4 → Fin 6 :=
  qn (tbl.getD (b0.toNat + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat + 16 * b4.toNat +
    32 * b5.toNat + 64 * b6.toNat + 128 * b7.toNat + 256 * b8.toNat) 0)

def pairBad (q : Fin 3 → Fin 3 → Bool) (a b : Fin 6) : Bool :=
  !(permB (meetB q (fun i => pp a i) (fun i => pp b i)) &&
    permB (joinB q (fun i => pp a i) (fun i => pp b i)))

theorem tblD : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool, ∀ u v : Fin 4, u ≠ v →
    pairBad (mkq b0 b1 b2 b3 b4 b5 b6 b7 b8) (quadFor b0 b1 b2 b3 b4 b5 b6 b7 b8 u)
      (quadFor b0 b1 b2 b3 b4 b5 b6 b7 b8 v) = true := by
  decide +kernel

theorem lb_block (q : Fin 3 → Fin 3 → Bool) :
    ∃ e : Fin 4 → Fin 6, ∀ u v, u ≠ v → pairBad q (e u) (e v) = true := by
  have h := tblD (q 0 0) (q 0 1) (q 0 2) (q 1 0) (q 1 1) (q 1 2) (q 2 0) (q 2 1) (q 2 2)
  rw [mkq_eq] at h
  exact ⟨_, h⟩

theorem permB_perm : ∀ s : Equiv.Perm (Fin 3), permB (fun i j => decide (s i = j)) = true := by
  decide

theorem permB_of (g : Fin 3 → Fin 3 → Bool) (s : Equiv.Perm (Fin 3))
    (h : ∀ i j, g i j = true ↔ s i = j) : permB g = true := by
  have hg : g = fun i j => decide (s i = j) := by
    funext i j
    rw [Bool.eq_iff_iff, h i j, decide_eq_true_iff]
  rw [hg]
  exact permB_perm s

theorem main (m r : ℕ) [DecidableEq (Fin m × (Fin 3 × Fin 3))] :
    (∃ (P : Finset (Fin m × (Fin 3 × Fin 3)))
      (F : Fin r → Finset (Finset (Fin m × (Fin 3 × Fin 3)))),
      (∀ X : Finset (Fin m × (Fin 3 × Fin 3)),
        (∃ σ : Fin m → Equiv.Perm (Fin 3), ∀ b i j, (b, i, j) ∈ X ↔ σ b i = j) ↔
          ∃ a, X ∈ F a) ∧
      (∀ a, ∀ X ∈ F a, ∀ Y ∈ F a,
        ((X ∩ Y) \ P) ∪ ((X ∪ Y) ∩ P) ∈ F a ∧ ((X ∪ Y) \ P) ∪ ((X ∩ Y) ∩ P) ∈ F a)) ↔
      4 ^ m ≤ r := by
  classical
  constructor
  · rintro ⟨P, F, hcov, hclos⟩
    have hb : ∀ b : Fin m, ∃ e : Fin 4 → Fin 6, ∀ u v, u ≠ v →
        pairBad (fun i j => decide ((b, i, j) ∈ P)) (e u) (e v) = true := fun b => lb_block _
    choose e hE using hb
    have hW : ∀ c : Fin m → Fin 4, ∃ W : Finset (Fin m × (Fin 3 × Fin 3)),
        ∀ b i j, (b, i, j) ∈ W ↔ pp (e b (c b)) i = j := by
      intro c
      exact ⟨Finset.univ.filter (fun x => pp (e x.1 (c x.1)) x.2.1 = x.2.2), fun b i j => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]⟩
    choose W hWm using hW
    have hleg : ∀ c, ∃ a, W c ∈ F a := fun c => (hcov (W c)).1 ⟨fun b => pp (e b (c b)), hWm c⟩
    choose a ha using hleg
    have hinj : Function.Injective a := by
      intro c c' heq
      by_contra hne
      obtain ⟨b, hb⟩ := Function.ne_iff.1 hne
      have hc' : W c' ∈ F (a c) := by rw [heq]; exact ha c'
      obtain ⟨hm, hj⟩ := hclos (a c) (W c) (ha c) (W c') hc'
      obtain ⟨σm, hσm⟩ := (hcov _).2 ⟨_, hm⟩
      obtain ⟨σj, hσj⟩ := (hcov _).2 ⟨_, hj⟩
      have h1 : permB (meetB (fun i j => decide ((b, i, j) ∈ P)) (fun i => pp (e b (c b)) i)
          (fun i => pp (e b (c' b)) i)) = true := by
        apply permB_of _ (σm b)
        intro i j
        rw [← hσm b i j]
        simp only [meetB, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter, hWm,
          Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
          decide_eq_false_iff_not]
      have h2 : permB (joinB (fun i j => decide ((b, i, j) ∈ P)) (fun i => pp (e b (c b)) i)
          (fun i => pp (e b (c' b)) i)) = true := by
        apply permB_of _ (σj b)
        intro i j
        rw [← hσj b i j]
        simp only [joinB, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter, hWm,
          Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
          decide_eq_false_iff_not]
      have h3 := hE b (c b) (c' b) hb
      rw [pairBad, h1, h2] at h3
      exact absurd h3 (by decide)
    have hcard := Fintype.card_le_of_injective a hinj
    simpa using hcard
  · intro hr
    have hc : Fintype.card (Fin m → Fin 4) ≤ Fintype.card (Fin r) := by simpa using hr
    obtain ⟨emb⟩ := Function.Embedding.nonempty_of_card_le hc
    have hg : ∀ c, Function.invFun emb (emb c) = c := Function.leftInverse_invFun emb.injective
    have hP : ∃ P : Finset (Fin m × (Fin 3 × Fin 3)), ∀ b i j, (b, i, j) ∈ P ↔ q0 i j = true :=
      ⟨Finset.univ.filter (fun x => q0 x.2.1 x.2.2 = true), fun b i j => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]⟩
    obtain ⟨P, hP⟩ := hP
    have hF : ∃ F : Fin r → Finset (Finset (Fin m × (Fin 3 × Fin 3))), ∀ a X, X ∈ F a ↔
        ∃ σ : Fin m → Equiv.Perm (Fin 3), (∀ b i j, (b, i, j) ∈ X ↔ σ b i = j) ∧
          ∀ b, cls (σ b) = Function.invFun emb a b :=
      ⟨fun a => Finset.univ.filter (fun X => ∃ σ : Fin m → Equiv.Perm (Fin 3),
        (∀ b i j, (b, i, j) ∈ X ↔ σ b i = j) ∧ ∀ b, cls (σ b) = Function.invFun emb a b),
        fun a X => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]⟩
    obtain ⟨F, hF⟩ := hF
    refine ⟨P, F, ?_, ?_⟩
    · intro X
      constructor
      · rintro ⟨σ, hσ⟩
        exact ⟨emb (fun b => cls (σ b)), (hF _ X).2 ⟨σ, hσ, fun b => by rw [hg]⟩⟩
      · rintro ⟨a, ha⟩
        obtain ⟨σ, hσ, -⟩ := (hF a X).1 ha
        exact ⟨σ, hσ⟩
    · intro a X hX Y hY
      obtain ⟨σ, hσ, hσc⟩ := (hF a X).1 hX
      obtain ⟨τ, hτ, hτc⟩ := (hF a Y).1 hY
      have hblk := fun b => ub_block (σ b) (τ b) (by rw [hσc, hτc])
      constructor
      · have hz : ∀ b, ∃ z : Equiv.Perm (Fin 3), cls z = Function.invFun emb a b ∧
            ∀ i j, (((σ b i = j ∧ τ b i = j) ∧ ¬ q0 i j = true) ∨
              ((σ b i = j ∨ τ b i = j) ∧ q0 i j = true)) ↔ z i = j := by
          intro b
          rcases (hblk b).1 with h | h
          · exact ⟨σ b, hσc b, h⟩
          · exact ⟨τ b, hτc b, h⟩
        choose ρ hρ using hz
        refine (hF a _).2 ⟨ρ, fun b i j => ?_, fun b => (hρ b).1⟩
        rw [← (hρ b).2 i j]
        simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter, hσ, hτ, hP]
      · have hz : ∀ b, ∃ z : Equiv.Perm (Fin 3), cls z = Function.invFun emb a b ∧
            ∀ i j, (((σ b i = j ∨ τ b i = j) ∧ ¬ q0 i j = true) ∨
              ((σ b i = j ∧ τ b i = j) ∧ q0 i j = true)) ↔ z i = j := by
          intro b
          rcases (hblk b).2 with h | h
          · exact ⟨σ b, hσc b, h⟩
          · exact ⟨τ b, hτc b, h⟩
        choose ρ hρ using hz
        refine (hF a _).2 ⟨ρ, fun b i j => ?_, fun b => (hρ b).1⟩
        rw [← (hρ b).2 i j]
        simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter, hσ, hτ, hP]

end PEqualNP.Outside.L_pcx_475

theorem PEqualNP.Outside.L_pcx_475 : letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
∀ m r : Nat,
  let Cell := Fin m × (Fin 3 × Fin 3)
  let legal := fun (X : Finset Cell) =>
    ∃ σ : Fin m → Equiv.Perm (Fin 3),
      ∀ b i j, (b, i, j) ∈ X ↔ σ b i = j
  let meet := fun (P X Y : Finset Cell) => ((X ∩ Y) \ P) ∪ ((X ∪ Y) ∩ P)
  let join := fun (P X Y : Finset Cell) => ((X ∪ Y) \ P) ∪ ((X ∩ Y) ∩ P)
  (∃ (P : Finset Cell) (F : Fin r → Finset (Finset Cell)),
    (∀ X : Finset Cell, legal X ↔ ∃ a, X ∈ F a) ∧
    (∀ a, ∀ X ∈ F a, ∀ Y ∈ F a,
      meet P X Y ∈ F a ∧ join P X Y ∈ F a)) ↔
    4 ^ m ≤ r := by
  intro m r Cell legal meet join
  exact @PEqualNP.Outside.L_pcx_475.main m r (fun a b => Classical.propDecidable (a = b))
