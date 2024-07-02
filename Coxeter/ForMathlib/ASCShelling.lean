import Mathlib.Data.Set.Card
import Coxeter.ForMathlib.AbstractSimplicialComplex

namespace AbstractSimplicialComplex
variable {V : Type*} [Fintype V]

/-- If `V` is of finite type, then for `F : ASC V`, every face of `F` is contained in a facet. -/
theorem exists_subset_Facet_strong {F : AbstractSimplicialComplex V} (hf : f ∈ F) : ∃ g ∈ F.Facets, f ⊆ g := by
  let s := {g ∈ F | f ⊆ g}
  have : Set.Finite s := Set.Finite.subset (s := F.faces) (Set.toFinite _) fun a ha ↦ ha.1
  rcases Set.Finite.exists_maximal_wrt (fun (a : Finset V) ↦ a) s this ⟨f, hf, by rfl⟩ with ⟨g, hg1, hg2⟩
  refine ⟨g, ⟨hg1.1, ?_⟩, hg1.2⟩
  intro a ha1 ha2
  apply hg2 a ⟨ha1, (subset_trans hg1.2 ha2)⟩ ha2

open Classical
/--
Definition: Let `F` be an abstract simplicial complex of rank `d + 1` with finite facets.
A shelling of `F` is an linear ordering `l₁`, ⋯ , `lₘ` of all (maximal) facets of F such that
 `closure {lᵢ} ⊓ (⨆ {j < i}, closure {lⱼ})` is an abstract simplicial complex pure of rank `d`.
-/
def Shelling {F : AbstractSimplicialComplex V} {m : ℕ} [NeZero m] (l : Fin m ≃ Facets F) := F.rank > 0 ∧
  ∀ k : Fin m, 0 < k.1 → IsPure' ((⨆ j : {j // j < k}, closure {(l j).1}) ⊓ (closure {(l k).1})) (F.rank - 1)

/--
Definition': Let `F` be an abstract simplicial complex of rank `d + 1`.
A shelling of `F` is an linear ordering `l₁`, ⋯ , `lₘ` of all (maximal) facets of `F` such that
for any `i < k`, there exists `j < k`, such that `lᵢ ∩ lₖ ⊆ lⱼ ∩ lₖ` and `|lⱼ ∩ lₖ| = d`.

Doesn't make sense if `m = 0`.
-/
def Shelling' {F :  AbstractSimplicialComplex V} {m : ℕ} [NeZero m] (l : Fin m ≃ Facets F) :=
  F.rank > 0 ∧
  ∀ k i : Fin m, i < k → ∃ j : Fin m, j < k ∧
    (l i).1 ∩ (l k).1 ⊆ (l j).1 ∩ (l k).1 ∧
    ((l j).1 ∩ (l k).1).card = F.rank - 1

/-- Lemma: The two definitions of shellings are equivalent, if `F` has finitely many facets and `F` has at least one facet.

No `convert` in the proof could be replaced with `apply` if we use `DecidableEq V` in the definition of `shelling'` instead of `open Classical`.
-/
lemma shelling_iff_shelling' {F : AbstractSimplicialComplex V} {m : ℕ} [NeZero m] (l : Fin m ≃ Facets F) :
    Shelling l ↔ Shelling' l := by
    constructor <;> refine fun ⟨a, h⟩ ↦ ⟨a, ?_⟩
    · intro k i ilek
      replace h := h k <| lt_of_le_of_lt (zero_le _) (Fin.lt_def.mp ilek)
      rw [iSup_inf_eq] at h
      letI : Nonempty { j // j < k } := ⟨0, lt_of_le_of_lt (Fin.zero_le' _) ilek⟩
      have : (l i).1 ∩ (l k).1 ∈ ⨆ j : {j // j < k}, closure {(l j).1} ⊓ closure {(l k).1} := by
        rw [← mem_faces, iSup_faces_of_nonempty, Set.mem_iUnion]
        use ⟨i, ilek⟩
        rw [mem_faces, ← closure_singleton_inter_eq_inf]
        apply Set.mem_of_subset_of_mem (subset_closure_faces _) (Set.mem_singleton _)
        /- If we use `DecidableEq V` instead of `open Classical`, then the following commented lines are needed-/
        -- simp only [Set.coe_setOf, Set.mem_setOf_eq, Set.mem_range, Subtype.exists, Set.singleton_subset_iff, mem_faces, exists_prop]
        -- use closure {(l i).1 ∩ (l k).1}
        -- constructor
        -- · apply Set.mem_of_subset_of_mem (subset_closure_faces _) (Set.mem_singleton _)
        -- · convert rfl
      rcases exists_subset_Facet_strong this with ⟨f, hf_mem, hf_big⟩
      rcases exits_mem_faces_of_mem_iSup hf_mem with ⟨j, hj⟩
      rw [← closure_singleton_inter_eq_inf, closure_singleton_Facets, Set.mem_singleton_iff] at hj
      subst hj
      refine ⟨j, j.2, by convert hf_big, ?_⟩
      convert h _ hf_mem
    · intro k kgt0
      letI : Nonempty { j // j < k } := ⟨0, kgt0⟩
      let aux := fun (i : {i // i < k}) ↦ h k i.1 i.2
      have : (⨆ i : {i // i < k}, closure {(l i).1}) ⊓ (closure {(l k).1}) = ⨆ i : {i // i < k}, closure {(l (choose (aux i))).1 ∩ (l k).1} := by
        rw [iSup_inf_eq]
        apply le_antisymm
        · apply iSup_mono
          intro i
          rw [← closure_singleton_inter_eq_inf]
          apply closure_singleton_mono
          convert (choose_spec (aux i)).2.1
        · apply iSup_le
          intro i
          apply le_iSup_of_le ⟨choose (aux i), (choose_spec (aux i)).1⟩
          rw [← closure_singleton_inter_eq_inf]
          /- Don't know how to continue if we use `DecidableEq V` instead of `open Classical`. -/
      rw [this]
      apply isPure'_iSup_isPure' fun i ↦ isPure'_closure_singleton (choose_spec (aux i)).2.2

/-- Definition: An abstract simplicial complex `F` is called shellable, if it admits a shelling. -/
def Shellable (F : AbstractSimplicialComplex F) := ∃ (m : ℕ) (h : NeZero m) (l : Fin m ≃ Facets F), Shelling l

-- lemma cone_Shellabe_iff {F G : AbstractSimplicialComplex V} {r : ℕ} [Pure F] [Pure G] (x : V) (hcone: Cone F G x) :
--   Shellable F ↔ Shellable G  := by sorry

/-- Definition: An abstract simplicial complex `F` is shellable, if it admits a shelling using the second definition. -/
def Shellable' (F: AbstractSimplicialComplex F) := ∃ (m : ℕ) (h : NeZero m) (l : Fin m ≃ Facets F), Shelling' l

/-- Lemma: The two definitions of shellability are equivalent. -/
lemma shellable_iff_shellable' {F : AbstractSimplicialComplex V} :
  Shellable F ↔ Shellable' F := by
    constructor
    · intro h
      rcases h with ⟨m, nzm, l, sl⟩
      use m ; use nzm ; use l
      apply (shelling_iff_shelling' l).mp
      exact sl
    · intro h
      rcases h with ⟨m, nzm, l, sl⟩
      use m ; use nzm ; use l
      apply (shelling_iff_shelling' l).mpr
      exact sl

end AbstractSimplicialComplex
