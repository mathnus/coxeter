import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.List
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.List.Lex
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.List.Chain
import Mathlib.Order.Cover
import Mathlib.Tactic.Linarith.Frontend
import Coxeter.ForMathlib.AdjacentPair
import Mathlib.SetTheory.Cardinal.Basic

noncomputable section
namespace PartialOrder
/- Let P be a finite poset. -/
variable {P : Type*} [PartialOrder P] [Fintype P]

open List Classical
--test

/- Recall that : We say a is covered by b if x < y and there is no element z such that x < z < y. -/

/- Defintion: We define the set of edges of P as the set of all pairs (a,b) such that a is covered by b.-/
def edges (P : Type*) [PartialOrder P] : Set (P × P) := {(a, b) | a ⋖ b }

/-
Definition: A chain in the poset P is a finite sequence x₀ < x₁ < ⋯ < x_n.
-/
abbrev chain (L : List P) : Prop := List.Chain' (· < ·) L

abbrev Chains (P : Type*) [PartialOrder P] : Set (List P) := { L | chain L }

section chain

attribute [-instance] List.instLEList
attribute [-instance] List.LT'
attribute [-instance] List.instLTList

/-
instance: The set of all chains in P admits a partial ordering by set-theoretical inclusion.
-/
instance poset_chain {P : Type*} [PartialOrder P] : PartialOrder (Chains P) where
  le := fun C₁ C₂ => C₁.val.Sublist C₂.val
  le_refl := by simp
  le_trans := fun _ _ _ h1 h2 ↦ List.Sublist.trans h1 h2
  le_antisymm := fun _ _ h1 h2 => Subtype.ext <| List.Sublist.antisymm h1 h2

end chain

section maximal_chain

/-
Definition: A chain in the poset P is maximal if it is not a proper subset of any other chains.
In other words, all relations are cover relations with x_0 being a minimal element and x_n be a maximal element.
-/

abbrev maximal_chain (L: List P) : Prop := chain L ∧
  ∀ L' : List P, chain L' -> List.Sublist L L' -> L = L'

/-
We also define the notion of maximal_chain' in the sense that if for any chain L' whose head and tail are the same as that of L, then L is sublist of L' implies L = L'.
 -/
abbrev maximal_chain' (L: List P) : Prop := chain L ∧ ∀ L' : List P, chain L' → (L.head? = L'.head? ∧ L.getLast? = L'.getLast?) → List.Sublist L L' -> L = L'

/-
Lemma: If a chain L in P is maximal, then its adjacent relations are cover relations.
-/
lemma maximal_chain'_of_maximal_chain {L: List P} : maximal_chain L → maximal_chain' L := by
  intro h
  constructor
  . exact h.1
  . intro L' hL' _ h2
    exact h.2 L' hL' h2

/-
Lemma: A singleton is a chain by definition.
-/
lemma chain_singleton {a : P} : chain [a] := chain'_singleton _

lemma getLast_eq_of_getLast?_eq_coe {L : List P} (h : L ≠ []) (h' : L.getLast? = .some a) : L.getLast h = a := by
  unfold List.getLast? at *
  match L with
  | [] => simp at *
  | b :: L' =>
    simp at *
    assumption

lemma head_eq_of_head?_eq_coe {L : List P} (h : L ≠ []) (h' : L.head? = .some a) : L.head h = a := by
  unfold List.head? at *
  match L with
  | [] => simp at *
  | b :: L' =>
    simp at *
    assumption

/-Lemma: A chain has no duplicates.-/
lemma chain_nodup {L : List P} (h : chain L) : L.Nodup := by
  induction L with
  | nil => simp
  | cons a L' hl' =>
    simp [List.Nodup]
    constructor
    · intro ain
      have : a < a := by
        apply List.Chain.rel (l :=  L')
        exact h
        exact ain
      simp at this
    · have : chain L' := by
        simp [chain] at *
        rw [show L' = List.tail (a :: L') by rfl]
        apply List.Chain'.tail h
      exact hl' this


-- May not be needed, use chain_nodup
lemma chain_singleton_of_head_eq_tail  {L : List P} (a : P) (chain_l : chain L)
 (lha : L.head? = some a) (lta :  L.getLast? = some a) : L.length = 1  := by
  match L with
  | [] => simp at lha
  | [_] => simp at *
  | b :: c :: L'' =>
      simp at lta
      apply getLast_eq_of_getLast?_eq_coe at lta <;> simp at *
      subst lha
      have : b < b := by
        nth_rw 2 [← lta]
        apply List.Chain.rel (l := (c :: L''))
        simp
        exact chain_l
        exact List.getLast_mem _
      simp at this


lemma maximal_chain'_singleton {a : P}: maximal_chain' [a] := by
  constructor
  · exact chain_singleton
  · intro L' hL' h hsub
    simp at h
    have := chain_singleton_of_head_eq_tail a hL' (eq_comm.1 h.1) (eq_comm.2 h.2)
    rw [List.length_eq_one] at this
    rcases this with ⟨a',ha'⟩
    rw [ha'] at hsub
    have := (List.sublist_singleton (l:= [a])).1  hsub
    simp at this
    rw [ha',this]


lemma maximal_chain'_nil : maximal_chain' ([] : List P) := by
  constructor
  . simp
  . intro L' hL' h1 h2
    have : L'.head? = none := by simp [<-h1.1]
    cases L'
    . simp
    . simp at this


lemma maximal_chain'_head {a b: P} {tail : List P} : maximal_chain' (a :: b :: tail) → a ⋖ b := by
  apply Function.mtr
  intro h H
  have hab : a < b := (List.chain'_cons.1 H.1).1
  obtain ⟨c, hc1⟩ := (not_covBy_iff hab).1 h
  let L' := a :: c :: b :: tail
  have chainL' : chain L' := by
    rw [ (by simp : L' = [a,c] ++ b:: tail)]
    apply (List.chain'_split (a := b) (l₂ := tail)).2
    constructor
    . simp [hc1]
    . exact (List.chain'_cons.1 H.1).2
  have hL' : List.Sublist (a :: b :: tail) L' := by
    apply  List.cons_sublist_cons.2
    apply  List.sublist_cons
  have neqL' : a :: b :: tail ≠ L' := by
    intro h
    rw [List.cons_eq_cons,List.cons_eq_cons] at h
    exact List.cons_ne_self _ _ (Eq.symm h.2.2)
  exact H.2 L' chainL' ⟨rfl, rfl⟩ hL' |> neqL'


lemma maximal_chain'_tail {a : P} {tail : List P} : maximal_chain' (a :: tail) → maximal_chain' tail := by
  rintro ⟨C, MAX⟩
  cases tail with
  | nil => exact maximal_chain'_nil
  | cons b t =>
  constructor
  . exact List.Chain'.tail C
  . intros L' hL' h1 h2
    let tail := b :: t
    let L'' := a :: L'
    have chainL'' : chain L'' := by
      apply List.chain'_cons'.2
      constructor
      . intro t ht
        rw [<-h1.1] at ht
        have : b=t := by simp [List.head?_cons] at ht; exact ht
        rw [<-this]
        exact (List.chain'_cons.1 C).1
      . exact hL'
    have htL''1 : (a :: tail).head? = L''.head?  := by
      exact rfl
    have htL''2 : (a :: tail).getLast? = L''.getLast? := by
      cases L' with
      | nil => simp at h2
      | cons c d =>
        calc
          List.getLast? (a :: tail) = List.getLast? (a :: b :: t) := by exact rfl
          _ = List.getLast? (b :: t) := by simp [List.getLast?_cons_cons]
          _ = List.getLast? (c :: d) := by simp [h1.2]
          _ = List.getLast? (a :: c :: d) := by simp [List.getLast?_cons_cons]
          _ = List.getLast? L'' := by exact rfl
        -- simp only [List.getLast?_cons_cons, h1.2]
    have sublistL'' : List.Sublist (a :: tail) L'' := by
      apply List.cons_sublist_cons.2
      exact h2
    have : a :: tail = L'' := MAX L'' chainL'' ⟨htL''1, htL''2⟩ sublistL''
    exact (List.cons_eq_cons.1 this).2

lemma in_of_in_sublist {a : P} {L L' : List P} (g : List.Sublist L L') (h : a ∈ L) : a ∈ L' := by
  induction g with
  | slnil => exact h
  | cons hd _ htrans =>
    exact List.mem_cons_of_mem hd (htrans h)
  | cons₂ hd _ htrans =>
    rename_i L₁ L₂ _
    by_cases ha : a = hd
    · rw [ha]
      exact List.mem_cons_self hd _
    · have : a ∈ L₁ := by exact List.mem_of_ne_of_mem ha h
      exact List.mem_cons_of_mem hd (htrans this)




/-
Lemma: If a chain L : x₀ < x₁ < ⋯ < x_n is maximal', then we have x_0 ⋖ x_1 ⋖ x_2 ⋯ ⋖ x_n.
-/
lemma cover_chain_of_maximal_chain' {P : Type*} [PartialOrder P] {L: List P} :
  maximal_chain' L → List.Chain' (· ⋖ ·) L := by
  intro h
  induction' L with a t ih
  . simp
  . match t with
    | [] => simp
    | b :: t' =>
      apply List.chain'_cons.2
      exact ⟨maximal_chain'_head h, ih (maximal_chain'_tail h)⟩

lemma maximal_chain'_cons {a b : P} {L : List P} : maximal_chain' (b :: L) → a ⋖ b → maximal_chain' (a :: b :: L) := by
  intro maxcbL aledb
  simp [maximal_chain', aledb.1, maxcbL.1]
  intro L' chain_l' lha leq sublst
  match L' with
  | [] => simp at *
  | c :: L'' =>
      simp at lha
      subst lha
      cases sublst with
      | cons  _ h =>
          have ain : a ∈ L'' := by
            have : [a].Sublist (a :: b :: L) := by simp
            have : [a].Sublist L'' := by apply List.Sublist.trans this h
            simp at this
            assumption
          exfalso
          apply chain_nodup at chain_l'
          apply List.nodup_cons.mp at chain_l'
          exact chain_l'.1 ain
      | cons₂ _ h =>
          congr
          dsimp [maximal_chain'] at maxcbL
          by_cases h' : List.head? L'' = some b
          · rw [show L'' = List.tail (a :: L'') by simp]
            apply maxcbL.2 (L' := L'') (List.Chain'.tail chain_l')
            constructor
            · apply h'.symm
            · match L'' with
              | [] => simp at h
              | _ :: _ =>
                  simp at leq
                  assumption
            apply h
          · exfalso
            dsimp [CovBy] at aledb
            match L'' with
            | [] => simp at h
            | c :: tail =>
                simp at h'
                have bin : b ∈ tail := by
                  have : b ∈ c :: tail := by
                    have : [b].Sublist (b :: L) := by simp
                    have : [b].Sublist (c :: tail) := by apply List.Sublist.trans this h
                    simp at this ⊢
                    exact this
                  simp at this
                  rcases this with e | hi
                  · exfalso; exact h' e.symm
                  · exact hi
                have cltb : c < b := by
                  simp only [List.chain'_cons] at chain_l'
                  apply List.Chain.rel (l := tail) chain_l'.2 bin
                have altc : a < c := (List.chain'_cons.mp chain_l').1
                exact aledb.2 altc cltb




/-
Lemma: A pair of element is a maximal chain if and only if the pair is a cover relation.
-/
lemma maximal_chain'₂_iff_ledot {a b : P} : maximal_chain' [a,b] ↔ (a ⋖ b) := by
  constructor
  · simp [maximal_chain']
    intro aleb maxchain
    constructor
    · assumption
    · intro c altc cltb
      have : chain [a, c, b] := by
        rw [chain]
        simp [altc, cltb]
      have : [a, b] = [a, c, b] := by
        apply maxchain [a, c, b] this
        simp; simp
        apply List.cons_sublist_cons.mpr
        rw [show [b] = List.tail [c, b] by simp]
        apply List.tail_sublist [c, b]
      simp at this
  · intro h
    apply maximal_chain'_cons maximal_chain'_singleton h





/-
Lemma: If a chain L : x₀ < x₁ < ⋯ < x_n is maximal, then we have x_0 ⋖ x_1 ⋖ x_2 ⋯ ⋖ x_n.
-/
lemma maximal_chain_cover {P : Type*} [PartialOrder P] {L: List P} :
  maximal_chain L → List.Chain' (· ⋖ · ) L := fun h =>
  cover_chain_of_maximal_chain' <| maximal_chain'_of_maximal_chain h


/-
Lemma: Assume P is a bounded poset. Let L : x₀ < x₁ < ⋯ < x_n  be a chain of P
such that the adjacent relations are cover relations; x_0 is the minimal element and x_n is the maximal element.
Then L is a maximal chain.
-/

-- lemma ne_sublist_subset {α: Type*} {l l' : List α} (hne: l ≠ l') (hsub: l <+ l') : ∃ a : α, a ∈ l' ∧ a ∉ l := sorry

-- lemma ne_nil_of_ne_sublist {α: Type*} {l l' : List α} (hne: l ≠ l') (hsub: l <+ l') : l' ≠ [] := sorry

-- --lemma ne_nil_of_ne_sublist' {α: Type*} {l l' : List α} (hne: l ≠ l') (hsub: l <+ l') (heq : head? L = head? L')
-- --  def List.interval :

lemma maximal_chain'_of_cover_chain {P :Type*} [PartialOrder P]  {L: List P} :
  List.Chain' (· ⋖ ·) L → maximal_chain' L := by
    have aux: ∀ n (L1:List P), L1.length = n → List.Chain' (· ⋖ ·) L1 → maximal_chain' L1 := by
      intro n
      induction' n with m hn
      · intro L1 heq _
        have hnil : L1 = [] := length_eq_zero.mp heq
        rw [hnil]
        exact maximal_chain'_nil
      · intro L1 heq hc
        have hl: L1.tail.length = m := by
          rw [length_tail,heq]
          rfl
        have := hn L1.tail hl (List.Chain'.tail hc)
        cases L1 with
        | nil => exact maximal_chain'_nil
        | cons a tail =>
          cases tail with
          | nil => exact maximal_chain'_singleton
          | cons b tail' =>
            simp only [tail] at *
            have acovb: a ⋖ b := List.Chain'.rel_head hc
            exact maximal_chain'_cons this acovb
    exact aux L.length L rfl

/-
Lemma: Assume P is a bounded poset. Let L : x₀ < x₁ < ⋯ < x_n  be a chain of P
such that the adjacent relations are cover relations; x_0 is the minimal element and x_n is the maximal element.
Then L is a maximal chain.
-/
lemma maximal_chain_of_cover_chain {P :Type*} [PartialOrder P] [BoundedOrder P] {L: List P} :
  List.Chain' (· ⋖ · ) L ∧ L.head? = some ⊥ ∧ L.getLast? = some ⊤ → maximal_chain L := by
  rintro ⟨h₁, h₂, h₃⟩
  have g₁ : List.Chain' (· < ·) L := by
    apply List.Chain'.imp (R := (· ⋖ · )) (S := (· < ·))
    intro a b aleb
    exact CovBy.lt aleb
    exact h₁
  have g₂ : maximal_chain' L := by
    apply maximal_chain'_of_cover_chain h₁
  rw [maximal_chain]
  constructor
  · exact g₁
  · intro L' g₃ g₄
    apply g₂.2
    · apply g₃
    · rw [h₂]
      rw [h₃]
      have g₅ : ⊥ ∈ L' := by
        apply in_of_in_sublist _ _
        · exact L
        · exact g₄
        · exact List.mem_of_mem_head? h₂
      have g₆ : ⊤ ∈ L' := by
        apply in_of_in_sublist _ _
        · exact L
        · exact g₄
        · exact List.mem_of_mem_getLast? h₃
      have g₇ : List.Chain' (fun x x_1 => x < x_1) L' := by
        exact g₃
      constructor
      · match L' with
        | [] =>
          have : L = [] := by exact List.sublist_nil.mp g₄
          simp [this] at h₂
        | head :: tail =>
          by_contra h₄
          push_neg at h₄
          have h₅ : ⊥ ∈ tail := by
            have : ⊥ ≠ head := by exact fun a => h₄ (congrArg some a)
            simp at g₅
            simp [this] at g₅
            exact g₅
          have : head < ⊥ := by
            apply List.Chain.rel g₃ h₅
          have h₆ : ¬ head < ⊥ := by exact not_lt_bot
          exact h₆ this
      · match L' with
        | [] =>
          have : L = [] := by exact List.sublist_nil.mp g₄
          simp [this] at h₃
        | head :: tail =>
          by_contra h₄
          have h₅ : chain (head :: tail ++ [⊤]) := by
            apply List.Chain'.append
            apply g₇
            exact chain_singleton
            intro x hx y hy
            simp at hy
            rw [hy.symm]
            unfold List.getLast? at h₄
            simp at h₄
            unfold List.getLast? at hx
            simp at hx
            rw [hx.symm]
            exact Ne.lt_top' h₄
          apply chain_nodup at h₅
          apply List.disjoint_of_nodup_append at h₅
          simp [g₆] at h₅
    · apply g₄


/- Definition: We say a poset P is bounded, if it has a unique minimal and a unique maximal element. -/
/-
Lemma: Let P be a bounded finite poset. Then a maximal chain exists.
-/

lemma exist_maximal_chain {P : Type*} [PartialOrder P] [BoundedOrder P] [Fintype P] :
  ∃ L : List P, maximal_chain L := by
  let n := Fintype.card P
  by_contra h
  simp only [maximal_chain] at h
  push_neg at h
  have (m : ℕ) : ∃L : List P, chain L ∧ m ≤ L.length := by
    induction m with
    | zero =>
      use []
      simp
    | succ m' hm =>
      obtain ⟨L, ⟨hc, hlen⟩⟩ := hm
      obtain ⟨L', ⟨hc', hsub, hneq⟩⟩ := h L hc
      use L'
      refine And.intro hc' ?_
      have lell := List.length_le_of_sublist hsub
      have neqll := fun x ↦ hneq (List.Sublist.eq_of_length hsub x)
      have := lt_of_le_of_ne lell neqll
      linarith
  obtain ⟨L, hc, hlen⟩ := this (n + 1)
  have : DecidableEq P := Classical.typeDecidableEq P
  have : L.toFinset ⊆ Finset.univ :=
    fun x _ ↦ Finset.mem_univ x
  have := Finset.card_le_card this
  have g : List.Nodup L := chain_nodup hc
  have g₁ : L.toFinset.card = L.length := List.toFinset_card_of_nodup g
  rw [g₁] at this
  have g₂ : (@Finset.univ P).card = n := by
    simp only [n]
    exact rfl
  linarith

/-
(Programming) Note that the assumption that P is a BoundedOrder implies that P is nonempty, and so a maximal chain is nonempty.
-/
lemma maximal_chain_nonempty {P : Type*} [PartialOrder P] [BoundedOrder P]  [Fintype P] (L: List P) :
  maximal_chain L → L ≠ [] := by
  intro h1
  by_contra h2
  rw [h2] at h1
  simp only [maximal_chain] at h1
  have h3 : List.Sublist [] (⊥ :: []) := by
    apply List.nil_sublist ((⊥ : P) :: [])
  have h4 : chain (⊥ :: []) := by
    exact List.chain'_singleton (⊥ : P)
  have h5 : [] = (⊥ :: []) := by
    apply h1.2
    · exact h4
    · exact h3
  have h6 : 0 = 1 := by
    rw [←List.length_nil, h5, List.length_singleton]
  linarith

/-
Lemma: Let P be a bounded finite poset. Let L = [x_0, ⋯, x_m] be a list of elements in P.
Then L is a maximal chain if and only if  x_0 is the minimal element, x_n is the maximal element, and x_i ⋖ x_{i+1} for all i.
-/
lemma maximal_chain_iff_cover {P : Type*} [PartialOrder P] [BoundedOrder P]  [Fintype P] (L: List P) :
  maximal_chain L ↔ ((L.head? = (⊥ : P)) ∧ (L.getLast? = (⊤ : P)) ∧ (List.Chain' (· ⋖ · ) L)) := by
  constructor
  · intro maxchain
    constructor
    · by_contra h
      have h₁ : chain (⊥ :: L) := by
        match L with
        | [] => simp
        | a :: L' =>
            have : a ≠ ⊥ := by
              intro abot
              rw [abot] at h
              simp at h
            apply List.Chain'.cons (lt_of_le_of_ne bot_le this.symm) maxchain.1
      have h₂: L.Sublist (⊥ :: L) := by simp
      have : L = (⊥ :: L) := by apply maxchain.2 _ h₁ h₂
      have : List.length L = List.length (⊥ :: L) := by congr
      simp [(Nat.succ_ne_self (List.length L)).symm] at this
    · constructor
      · by_contra h
        have h₁ : chain (L ++ [⊤]) := by
          apply List.Chain'.append maxchain.1
          simp
          intro x hx y hy
          simp at hy
          subst hy
          apply lt_of_le_of_ne le_top
          intro e
          simp [e] at *
          exact h hx
        have h₂ : L.Sublist (L ++ [⊤]) := by simp
        have : L = L ++ [⊤] := maxchain.2 _ h₁ h₂
        simp at this
      · apply maximal_chain_cover maxchain
  · rintro ⟨h₁, h₂, h₃⟩
    constructor
    · exact (maximal_chain'_of_cover_chain h₃).1
    · intro L' chain_l' sublst
      have : maximal_chain L := maximal_chain_of_cover_chain ⟨h₃, h₁, h₂⟩
      apply this.2 L' chain_l' sublst

/-
Lemma: Let L : x_0 < x_1 < ⋯ < x_n be a maximal chain of P. Then (x_i, x_{i+1}) is an (cover) edge of P.
-/
lemma max_chain_mem_edge {P : Type*} [PartialOrder P] {L: List P} {e: P × P} :
  maximal_chain L →  e ∈ L.adjPairs → e ∈ edges P:= by
    intro maxc eadj
    have := maximal_chain_cover maxc
    simp [edges]
    rw [mem_adjPairs_iff] at eadj
    rcases eadj with ⟨l₁, l₂, h⟩
    subst h
    simp at this
    exact this.2.1

/-
We define the set of all maximal chains of P.
-/

instance : Fintype (Set.Elem { L : List P | L.Nodup }) := 
  inferInstanceAs (Fintype { L : List P // L.Nodup })

instance : Fintype { L : List P | maximal_chain L } :=
  Set.fintypeSubset { L : List P | L.Nodup} fun _ h ↦ Set.mem_setOf_eq.mpr (chain_nodup (Set.mem_setOf_eq.mp h).1)

abbrev maximalChains (P : Type*) [PartialOrder P] [Fintype P] : Finset (List P) :=
  Set.toFinset { L | maximal_chain L }

/-
(Programming)
-/
def edgePairs {P : Type*} [PartialOrder P] [Fintype P] (L : maximalChains P) : List (edges P) :=
  List.map (fun e => ⟨e.val, max_chain_mem_edge  (Set.mem_setOf_eq.mp (Set.mem_toFinset.mp L.prop))  e.prop⟩) <| L.val.adjEPairs

/- Definition: Define rank to be the Sup of the lengths of all maximal chains.

  Note that if the length is unbounded,then rank = 0.
 -/
def rank (P : Type*) [PartialOrder P] [Fintype P] : ℕ :=
  Finset.sup (maximalChains P) List.length


end maximal_chain

-- @[deprecated Set.Icc]
-- def Interval {P : Type*} [PartialOrder P] (x y : P) : Set P := {z | x ≤ z ∧ z ≤ y}

-- instance Interval.bounded {P : Type*} [PartialOrder P] {x y : P} (h : x ≤ y) : BoundedOrder (Set.Icc x y) where
--   top := ⟨y, And.intro h (le_refl y)⟩
--   bot := ⟨x, And.intro (le_refl x) h⟩
--   le_top := fun x ↦ x.2.2
--   bot_le := fun x ↦ x.2.1

-- instance Interval.poset {P : Type*} [PartialOrder P] {x y : P} :
-- PartialOrder (Set.Icc x y) := by exact Subtype.partialOrder _

-- instance Interval.edge_coe {P : Type*} [PartialOrder P] {x y : P} : CoeOut (edges (Set.Icc x y)) (edges P) where
--   coe := fun z => ⟨(z.1.1, z.1.2),sorry ⟩



end PartialOrder
