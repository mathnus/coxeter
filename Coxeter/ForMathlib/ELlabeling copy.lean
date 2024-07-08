import Coxeter.ForMathlib.PosetChain
import Coxeter.ForMathlib.PosetGraded
import Coxeter.ForMathlib.PosetShelling

namespace PartialOrder
variable {P : Type*} [PartialOrder P] [Fintype P]
variable {A : Type*} [PartialOrder A]

instance {x y : P} : Fintype (Set.Icc x y) := sorry -- temporary

open AbstractSimplicialComplex
open List Classical

/-
Definition: Let `P` and `A` be posets. An edge labelling of `P` in `A` is a map from the set of edges of `P` to the poset `A`.
-/
@[simp]
abbrev edgeLabeling (P A : Type*) [PartialOrder P] := edges P → A

/- def replace_nth (L: List P) (x : P) (n : Fin L.length) : List P := List.modifyNth (fun _ ↦ x) n L -/

def replace_nth (L : List P) (x : P) (n : Fin L.length) : List P := L.take (n.1 - 1) ++ [x] ++ L.drop (n.1)

/-
Definition: Given any two nonempty chains in `P`, `m₁ : x_0 < ⋯ < x_n` and `m₂ : x_{n+1} < ⋯ < x_k` with
x_n < x_{n+1}, the concatenation `m : x_0 < ⋯ < x_n < x_{n+1} < ⋯ < x_k` is a chain. Note : true for empty chains but not included; look at addChain' instead
-/
lemma addChain (L L' : List P) (h₀ : chain L ∧ chain L') (h₁: L ≠ [] ∧ L' ≠ []) (h₂ : L.getLast h₁.1 < L'.head h₁.2) : chain (L ++ L') := by
  let L₀ := (L ++ L')
  have : List.Chain' (· < ·) (L₀) := by
    refine List.Chain'.append ?_ ?_ ?_
    · exact h₀.1
    · exact h₀.2
    · let x₀ := L.getLast h₁.1
      let y₀ := L'.head h₁.2
      intro x xlast y yhead
      have : x = x₀ ∧ y = y₀ := by
        constructor
        · exact (getLast_eq_of_getLast?_eq_coe h₁.1 xlast).symm
        · exact (head_eq_of_head?_eq_coe h₁.2 yhead).symm
      rw [this.1, this.2]
      exact h₂
  exact this

lemma addChain' (L L' : List P) (h₀ : chain L ∧ chain L') (h₁ : (n : L ≠ [] ∧ L' ≠ []) → (L.getLast n.1 < L'.head n.2)) : chain (L ++ L') := by
  by_cases h : L = []
  · rw [h]
    simp
    exact h₀.2
  · by_cases h1 : L' = []
    · rw [h1]
      simp
      exact h₀.1
    · have ne : L ≠ [] ∧ L' ≠ [] := by
        simp
        constructor
        · exact h
        · exact h1
      exact addChain L L' h₀ ne (h₁ ne)

/- lemma pos_sub_length (L : List P) (h₀ : n < L.length) (h₁ : n > 0) : (L.take n).length > 0 ∧ (L.drop n).length > 0 := by
  constructor
  · have len : (L.take n).length = n := by
      simp
      exact Nat.le_of_succ_le h₀
    rw [len]
    exact h₁
  · exact List.lt_length_drop L h₀

lemma split_tail (L : List P) (n : Fin L.length) (h₀ : n.1 > 2) (h : (L.take (n.1 - 2)) ≠ []) : L[n.1 - 3] = (L.take (n.1-2)).getLast h := by
  have : n.1 - 3 < (L.take (n.1-2)).length := by sorry
  have : L[n.1-3] = (L.take (n.1-2))[n.1-3] := by
    apply L.get_take
    have : n.1 - 3 < n.1 - 2 := by exact Nat.sub_succ_lt_self (n.1) 2 h₀
    exact this
  rw [this]
  sorry

lemma split_head (L: List P) (n : Fin L.length) (h₁ : n.1 > 2) (h : (L.drop (n.1 - 1)) ≠ []) : L[n.1 - 1] = (L.drop (n.1 - 1)).head h := by
  sorry

lemma nonempty_split_chain (L : List P) (n : Fin L.length) (h : n.1 > 2) : L.take (n.1 - 2) ≠ [] ∧ L.drop (n.1 - 1) ≠ [] := by
  have nle1 : n.1 - 1 < L.length := by
    refine Nat.sub_one_lt_of_le ?_ ?_
    · exact Nat.zero_lt_of_lt h
    · exact Fin.is_le'
  have nle2 : n.1 - 2 < L.length := by
    have : n.1 - 2 < n.1 - 1 := by
      refine Nat.sub_succ_lt_self n.1 1 ?_
      exact Nat.lt_of_succ_lt h
    exact Nat.lt_trans this nle1
  have ngt2 : n.1 - 2 > 0 := by exact Nat.zero_lt_sub_of_lt h
  have ngt1 : n.1 - 1 > 0 := by exact Nat.lt_of_lt_pred ngt2
  have l1 : (L.take (n.1 - 2)).length > 0 := by apply (pos_sub_length L nle2 ngt2).1
  have l2 : (L.drop (n.1 - 1)).length > 0 := by apply (pos_sub_length L nle1 ngt1).2
  constructor
  · exact List.length_pos.mp l1
  · exact List.length_pos.mp l2


Lemma : Let P be a poset and L : x_0 < x_1 < ⋯ < x_k be a chain in P with k ≥ 2.
Given some x ∈ P s.t. x_{n-1} < x < x_{n+1} where 0 < n < k, L' : x_0 < ⋯ x_{n-1} < x < x_{n+1} < ⋯ < x_k is also a chain.

lemma exchainge (L : List P) (x : P) (n : Fin L.length) (h : n.1 > 2) (h₀ : chain L) : L[n.1-3] < x ∧ x < L[n.1-1] → chain (replace_nth L x n) := by
  intro hyp
  let L' := replace_nth L x n
  have : chain L' := by
    have ne : l₁ ≠ [] ∧ l₂ ≠ [] := by apply nonempty_split_chain L n h
    have nel : l₁ ++ [x] ≠ [] := by
      refine List.append_ne_nil_of_ne_nil_right l₁ [x] ?_
      simp
    have tail : L[n.1 - 3] = l₁.getLast ne.1 := by exact split_tail L n h ne.1
    have head : L[n.1 - 1] = l₂.head ne.2 := by exact split_head L n h ne.2
    have c : L' = l₁ ++ [x] ++ l₂ := by sorry
    have : chain (l₁ ++ [x]) := by
      apply addChain
      constructor
      · exact List.Chain'.take h₀ (n.1 - 2)
      · exact chain_singleton
      · have : [x] ≠ [] := by simp
        have : List.head [x] this = x := by rfl
        rw [tail.symm, this]
        exact hyp.1
        constructor
        · exact ne.1
        · simp
    rw [c]
    apply addChain
    constructor
    · exact this
    · exact List.Chain'.drop h₀ (n.1 - 1)
    · have : List.getLast (l₁ ++ [x]) nel = x := by exact List.getLast_append l₁ nel
      rw [this, head.symm]
      exact hyp.2
      constructor
      · exact nel
      · exact ne.2
  exact this
-/

lemma chain_head_lt_chain_2nd (L : List P) (x : P) (h₁ : L ≠ []) (h₂ : chain L) : chain ([x] ++ L) ↔ x < L.head h₁ := by
  constructor
  · intro hyp
    let L' := [x] ++ L
    have l : L = L.head h₁ :: L.tail := by exact (List.head_cons_tail L h₁).symm
    have li : L' = x :: L.head h₁ :: L.tail := by exact congrArg (List.cons x) l
    have c : List.Chain' (· < ·) L' := by exact hyp
    rw [li] at c
    exact (List.chain'_cons.mp c).1
  · intro hyp
    apply addChain
    · constructor
      simp ; exact h₂
    · have last : [x].getLast (by simp) = x := by simp
      rw [last] ; exact hyp
      constructor
      simp ; exact h₁

lemma addChain_iff_last_lt_head (L L' : List P) (h₀ : chain L ∧ chain L') (h₁ : L ≠ [] ∧ L' ≠ []) : chain (L ++ L') ↔ L.getLast h₁.1 < L'.head h₁.2 := by
  constructor
  · intro hyp ; let L0 := L.getLast h₁.1 :: L'.head h₁.2 :: L'.tail
    have l : L0 = [L.getLast h₁.1] ++ [L'.head h₁.2] ++ L'.tail := by rfl
    have c' : chain ([L.getLast h₁.1] ++ [L'.head h₁.2] ++ L'.tail) := by sorry
    have c : List.Chain' (· < ·) L0 := by exact c'
    exact (List.chain'_cons.mp c).1
  · intro hyp
    apply addChain
    · constructor
      exact h₀.1 ; exact h₀.2
    · exact hyp
    · exact h₁

lemma exchainge (L : List P) (x : P) (n : Fin L.length) (h : chain L) : chain (L.take (n.1-1) ++ [x]) ∧ chain ([x] ++ L.drop n) → chain (replace_nth L x n) := by
  intro hyp
  let L' := replace_nth L x n
  let l₁ := L.take (n.1 - 1)
  let l₂ := L.drop (n.1)
  have c : L' = l₁ ++ [x] ++ l₂ := by rfl
  have : chain L' := by
    rw [c]
    by_cases c1 : l₁ = []
    · simp [c1]
      exact hyp.2
    · by_cases c2: l₂ = []
      · simp [c2] ; exact hyp.1
      · have ch : chain l₂ := by exact List.Chain'.drop h n.1
        apply addChain
        · constructor
          exact hyp.1 ; exact ch
        · have ne : l₁ ++ [x] ≠ [] := by simp
          have last : (l₁ ++ [x]).getLast ne = x := by simp
          rw [last]
          have : chain ([x] ++ l₂) := by exact hyp.2
          apply (chain_head_lt_chain_2nd l₂ x c2 ch).mp this
          constructor
          simp ; exact c2
  exact this

/-
Definition: Let `P` and `A` be posets and `l` be an edge labelling of `P` in `A`.
Then for any maximal chain `m : x_0 ⋖ x_1 ⋖ ⋯ ⋖ x_n` in `P`, we define a list in `A` by `[l(x_0 ⋖ x_1), l(x_1 ⋖ x_2), ⋯, l (x_{n-1} ⋖ x_n)]`.
-/
def mapMaxChain (l : edgeLabeling P A) (m : maximalChains P) : List A := List.map (fun e => l e) <| edgePairs m

/-
Definition: Let P and A be posets and l be an edge labelling of P in A.
Then any maximal chain m : x_0 ⋖ x_1 ⋖ ⋯ ⋖ x_n in [x,y] ⊂ P, we define a list in A by [l(x_0 ⋖ x_1),l(x_1 ⋖ x_2), ⋯ ,l(x_{n-1} ⋖ x_n)].
-/
def mapMaxChain_interval (l : edgeLabeling P A) {x y : P} (m : maximalChains <| Set.Icc x y) : List A := List.map (fun e : edges (Set.Icc x y) => l ( sorry
    -- e : edges P
    )) <| edgePairs m

/- instance poset_mapMaxChain : PartialOrder (maxAChains) where
  le := fun l₁ l₂ => sorry
  le_refl :=
  le_trans :=
  le_antisymm :=

 instance poset_maxchain [Fintype P] (l : edgeLabeling P A) : PartialOrder (maximalChains P) where
  le := fun L₁ L₂ => mapMaxChain l L₁ ≤ mapMaxChain l L₂
  le_refl := by
    intro a ; simp
    have eq : mapMaxChain l a = mapMaxChain l a := by simp
    sorry
  le_trans := by
    intro a b c aleb blec
    simp at aleb blec ; simp
    sorry
  le_antisymm := fun _ _ h1 h2 => Subtype.ext <| List.Sublist.antisymm h1 h2 -/

/-Defines the set of risingChains in an interval [x,y]-/
abbrev risingChains (l : edgeLabeling P A) (x y: P) := {m : maximalChains <| Set.Icc x y | List.Chain' (. ≤ .) <| mapMaxChain_interval l m}

/-
Definition: An edge labelling of P is called an EL-labelling if for every interval [x,y] in P,
  (1) there is a unique increasing maximal chain c in [x,y],
  (2) c <_L c' for all other maximal chains c' in [x,y].
Here <_L denotes the lexicographic ordering for the tuples in the labelling poset A.
-/
class ELLabeling (l : edgeLabeling P A) where
  unique {x y: P} (h : x<y) : Unique (risingChains l x y)
  unique_min {x y: P} (h : x<y): ∀ (m' : maximalChains <| Set.Icc x y), m' ≠ (unique h).default → (mapMaxChain_interval l (unique h).default.val < mapMaxChain_interval l m')

noncomputable def maxAChains' (l : edgeLabeling P A) : Finset (List A) := Finset.image (mapMaxChain l) (Finset.univ : Finset (maximalChains P))

/-
instance: The set of all lists in A admits a partial ordering by the lexicographic order.
-/
@[simp]
instance poset_AList {P : Type*} [PartialOrder P] [Fintype P] (l : edgeLabeling P A) : PartialOrder (maxAChains' l) where
  le := fun L₁ L₂ => L₁.val ≤ L₂.val
  le_refl := fun _ => Eq.le refl
  le_trans := by sorry
  le_antisymm := by sorry

instance poset_A {P : Type*} [PartialOrder P] [Fintype P] (l : edgeLabeling P A) : Lex (maxAChains' l) := by sorry

#check Lex (List A)
/- def maxAChains (l :edgeLabeling P A) : List (List A) := Finset.sort (· ≤ ·) (maxAChains' l) -/

def pew : Finset ℕ := {1, 3, 2, 4}
def pewz : List ℕ := Finset.sort (· ≤ ·) pew
#eval pewz

def diff_index {α : Type _} [DecidableEq α] (k m : List α) (h₀ : k ≠ m) (h₁ : k.length = m.length) : Fin m.length :=
  match k, m with
  | hd₁ :: tl₁, hd₂ :: tl₂ =>
      if h : hd₁ = hd₂ then
        have ne : tl₁ ≠ tl₂ := by
          rw [h] at h₀
          simp at h₀
          exact h₀
        .mk (1 + diff_index tl₁ tl₂ ne (by simp at h₁; assumption)) <| by
          simp_arith ; apply Fin.isLt
      else
        .mk 0 (by simp)
  | [], [] => by contradiction

lemma neq_list (k m : List A) : k < m → k ≠ m := by
  intro klem
  by_contra h
  rw [h] at klem
  sorry

lemma mem_of_maxChains (m : maximalChains P) : maximal_chain m.1 := by
  let m0 := m.2
  simp at m0 ; exact m0

lemma mapMaxChain_length [GradedPoset P] (l : edgeLabeling P A) (k m : maximalChains P) : (mapMaxChain l k).length = (mapMaxChain l m).length := by
  have max : maximal_chain m.1 ∧ maximal_chain k.1 := by
    constructor
    apply mem_of_maxChains m ; apply mem_of_maxChains k
  have len : m.1.length = k.1.length := by exact GradedPoset.pure (m.1) (k.1) max
  sorry

/-
Lemma : Let P be a graded finite poset with an EL-labelling l to a poset A.
Then for any two maximal chains s.t. k <_L m, there exists a maximal chain c s.t. c <_L m, k ∩ m ⊆ c ∩ m, and |k ∩ m| = |m| - 1
-/
lemma min_max_chain [GradedPoset P] (k m : maximalChains P) (l : edgeLabeling P A) (h : ELLabeling l): mapMaxChain l k < mapMaxChain l m →
∃ c : maximalChains P, mapMaxChain l c < mapMaxChain l m ∧ k.val ∩ m.val ⊆ c.val ∩ m.val ∧ (k.val ∩ m.val).length = m.val.length - 1 := by
  let lk := mapMaxChain l k ; let lm := mapMaxChain l m
  intro klem
  have knem : lk ≠ lm := by apply neq_list lk lm klem
  sorry
/- need to define c using exchainge, then prove it is maximal etc. -/

/-
Lemma : Let P be a graded finite poset with an EL-labelling l to a poset A. Then l defines a series of maps from Fin m ≃ Facets (Delta P), where rank (Delta P) = m.

def lex_map_chain [GradedPoset P] (l : edgeLabeling P A) (h : ELLabeling l) (m : ℕ) : Type := Fin m ≃ Facets (Delta P) -/

/-
Theorem: Let P be a graded finite poset with an EL-labelling l to a poset A. Then P is shellable.
-/
theorem shellable_of_ELLabeling [GradedPoset P] (k m : maximalChains P) (l : edgeLabeling P A) (h: ELLabeling l) (h₀ : mapMaxChain l k < mapMaxChain l m) : ShellableDelta P := by
  have : Shellable (Delta P) := by
    apply (shellable_iff_shellable').mpr
    letI : Nonempty {L // L ∈ maximalChains P} := by
      have : ∃ L : List P, maximal_chain L := by apply exist_maximal_chain
      rcases this with ⟨L, mc⟩
      use L
      simp
      exact mc
    let r := rank P
    have len : ∀ L ∈ maximalChains P, L.length = r := by
      intro L mc
      have : rank P = L.length := by
        apply GradedPoset.rank_def L
        exact mc
      exact id this.symm
    have nzr : NeZero r := by sorry
    have l' : Fin r ≃ Facets (Delta P) := by sorry
    use r ; use nzr ; use l'
    constructor
    · have : (Delta P).rank = r := by sorry
      rw [this]
      exact Fin.size_pos'
    · intro a b blea
      /- map b and a to their respective edge labellings on chain ; note b < a is directly equiv to the < relation on their respective max chains -/
      /- then use min_max_chain -/
      sorry
  exact this

#check Std.AssocList

/- have c' : ∃ c : maximalChains P, mapMaxChain l c < mapMaxChain l m ∧ k.val ∩ m.val ⊆ c.val ∩ m.val := by apply min_max_chain k m l h h₀
      rcases c' with ⟨c, hyp⟩ -/

  /- rw goal as ShellableDelta P → Shellable (Delta P) → Shellable' (Delta P) i.e. ∃ (m : ℕ+) (l : Fin m ≃ Facets Delta P), Shelling' l -/

  /- fix map l from labelling -/

  /- let k : 0 = k_0 ⋖ k_1 ⋖ ⋯ ⋖ k_r = 1, m : 0 = m_0 ⋖ m_1 ⋖ ⋯ ⋖ m_r = 1 be two maximal chains s.t. k <_L m -/

  /- let d be the greatest integer s.t. kᵢ = mᵢ for i ∈ [0, d], and g the greatest integer s.t. d < g and k_g = m_g -/

  /- then for the interval [m_g, m_d], m_d ⋖ ⋯ ⋖ m_g is not the unique max chain  -/

  /- ∃e ∈ (d, g) s.t. l(m_{e-1} ⋖ m_e) > l(m_e ⋖ m_{e+1})  -/

  /- have a unique increasing max chain in [m_{e-1}, m_{e+1}] : m_{e-1} ⋖ x ⋖ m_{e+1} -/

  /- then c : m_0 ⋖ ⋯ ⋖ m_{e-1} ⋖ x ⋖ m_{e+1} ⋖ ⋯ ⋖ m_r satisfies Shelling' l -/

  /- finite set totally ordered -> order preserving subset of nat to this poset -/

  /- map from nat to set of max chains -/


end PartialOrder
