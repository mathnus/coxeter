import Coxeter.CoxeterMatrix.CoxeterMatrix
import Coxeter.CoxeterMatrix.Palindrome
import Coxeter.AlternatingWord
import Coxeter.CoxeterMatrix.CoxeterSystem
import Mathlib.GroupTheory.Perm.Support

/-!
# Strong Exchange Property
This file proves strong exchange property for an `OrderTwoGen` group generated by `CoxeterMatrix`,
thus giving a `CoxeterGroup` and `CoxeterSystem` instance.

## Main Definition
Let `m` be a Coxeter matrix on type `α`.
Let `G` be the Coxeter group associated with the Coxeter matirx `m`.
Let `S` be the set of simple reflections/
Let `T` be the set of reflections.
Let `ℓ` be the length function on `G`, viewing `G` as a group generated by order 2 elements.

## Content
1. We establish basic properties of length functions.
2. We prove the strong exchange property of the presented group `G`.

-/


open Classical
open BigOperators
open OrderTwoGen
open TestGroup

namespace CoxeterMatrix

variable {α} {m : Matrix α α ℕ} [hm : CoxeterMatrix m]

local notation "G" => toGroup m
local notation "S" => SimpleRefl m
local notation "T" => Refl (SimpleRefl m)

local notation : max "ℓ(" g ")" => (OrderTwoGen.length S g)


lemma epsilon_mul {a b : G} : epsilon m (a * b) = epsilon m a * epsilon m b :=
  MonoidHom.map_mul (epsilon m) a b

lemma epsilon_list_length {L : List S} : epsilon m L = μ₂.gen ^ L.length := by
  induction' L with a L0 ih
  · rw [gprod_nil, List.length_nil, pow_zero]; rfl
  · have h1 : (a :: L0).length = L0.length + 1 :=
      List.length_cons a L0
    rw [h1]
    have h2 : epsilon m (a :: L0) = μ₂.gen * epsilon m L0 :=
      calc
        epsilon m (a :: L0) = epsilon m (a * L0) := by
          rw [gprod_cons]
        _ = epsilon m a * epsilon m L0 := by
          rw [epsilon_mul]
        _ = μ₂.gen * epsilon m L0 := by
          rw [epsilon_S]
    rw [h2, ih, pow_succ μ₂.gen L0.length]
    nth_rw 1 [ ←pow_one (μ₂.gen)]
    rw [pow_mul_comm, pow_one μ₂.gen]

lemma epsilon_length {g : G} : epsilon m g = μ₂.gen ^ ℓ(g) := by
  let ⟨L, h1, h2⟩ := Nat.find_spec (@length_aux G _ S _ g)
  simp only [length]
  nth_rw 1 [h2]
  rw [epsilon_list_length, h1]

lemma length_smul_neq {g : G} {s : S} : ℓ(g) ≠ ℓ(s * g) := by
  intro h
  have h1 : epsilon m g = epsilon m (s * g) := by
    rw [epsilon_length, epsilon_length, ← h]
  have h2 : epsilon m g = μ₂.gen * epsilon m g := by
    calc
      epsilon m g = epsilon m (s * g) := h1
      _ = epsilon m s * epsilon m g := by
        rw [epsilon_mul]
      _ = μ₂.gen * epsilon m g := by
        rw [epsilon_S]
  have h3 : μ₂.gen = 1 := by
    calc
      μ₂.gen = μ₂.gen * epsilon m g * (epsilon m g)⁻¹ := by group
      _ = epsilon m g * (epsilon m g)⁻¹ := by rw [← h2]
      _ = 1 := by group
  exact μ₂.gen_ne_one h3

lemma length_muls_neq {g : G} {s : S} : ℓ(g) ≠ ℓ(g * s) := by
  intro h
  have h1 : epsilon m g = epsilon m (g * s) := by
    rw [epsilon_length, epsilon_length, ← h]
  have h2 : epsilon m g = epsilon m g * μ₂.gen := by
    calc
      epsilon m g = epsilon m (g * s) := h1
      _ = epsilon m g * epsilon m s := by
        rw [epsilon_mul]
      _ = epsilon m g * μ₂.gen := by
        rw [epsilon_S]
  have h3 : μ₂.gen = 1 := by
    calc
      μ₂.gen = (epsilon m g)⁻¹ * (epsilon m g * μ₂.gen) := by group
      _ = (epsilon m g)⁻¹ * epsilon m g := by rw [← h2]
      _ = 1 := by group
  exact μ₂.gen_ne_one h3

-- DLevel 1
lemma length_diff_one {g : G} {s : S} : ℓ(s * g) = ℓ(g) + 1 ∨ ℓ(g) = ℓ(s * g) + 1 := by
  by_cases h : ℓ(s * g) > ℓ(g)
  . left
    have : ℓ(s * g) ≤ ℓ(g) + 1 := length_smul_le_length_add_one
    linarith
  . right
    have h1 : ℓ(g) ≤ ℓ(s * g) + 1 := length_le_length_smul_add_one
    have : ℓ(g) ≠ ℓ(s * g) := length_smul_neq
    apply le_antisymm h1
    apply Nat.add_one_le_iff.2
    apply Nat.lt_iff_le_and_ne.2
    constructor
    · exact le_of_not_gt h
    · exact Ne.symm this

-- DLevel 1
lemma length_smul_lt_of_le {g : G} {s : S} (hlen : ℓ(s * g) ≤ ℓ(g)) : ℓ(s * g) < ℓ(g) :=
  Ne.lt_of_le' length_smul_neq hlen


-- In the following subsection, we prove the strong exchange property for the presented group G.
section ReflRepresentation

open Palindrome



noncomputable def eta_aux (s : α) (t : T) : μ₂ := if s = t.val then μ₂.gen else 1

noncomputable def eta_aux' (s : S) (t : T) : μ₂ := if s.val = t.val then μ₂.gen else 1

@[simp]
lemma eta_aux_aux' (s : α) (t : T) : eta_aux s t = eta_aux' s t := by congr

noncomputable def nn (L : List S) (t : T) : ℕ := List.count (t : G) <| List.map (fun i ↦ (toPalindrome_i L i : G)) (List.range L.length)

lemma Refl_palindrome_in_Refl {i : ℕ} (L : List S) (t : T) : ((L.take i).reverse : G) * t * L.take i ∈ T := by
  induction i with
  | zero =>
    rw [List.take, List.reverse_nil]
    rcases t with ⟨_, ht⟩
    rw [gprod_nil]
    group
    exact ht
  | succ j hi =>
    by_cases hj : j < L.length
    · set jf : Fin L.length := ⟨j, hj⟩
      have h : ((L.take (Nat.succ j)).reverse : G) * t * L.take (Nat.succ j) =
          L.get jf * (((L.take j).reverse : G) * t * L.take j) * L.get jf := by
        rw [List.take_succ, List.get?_eq_get hj]
        simp only [Option.toList]
        rw [List.reverse_append, List.reverse_singleton, gprod_append, gprod_append, gprod_singleton]
        group
      rw [h]
      exact Refl.mul_SimpleRefl_in_Refl (L.get jf) ⟨_, hi⟩
    · push_neg at hj
      have h : ((L.take (Nat.succ j)).reverse : G) * t * L.take (Nat.succ j) =
          ((L.take j).reverse : G) * t * L.take j := by
        rw [List.take_succ, List.get?_eq_none.mpr hj]
        simp only [Option.toList]
        rw [List.append_nil]
      rw [h]
      exact hi

lemma nn_cons (L : List S) (s : S) (t : T) : nn (s :: L) t = (if (s : G) = t then 1 else 0) +
    nn L ⟨(s : G) * t * s, Refl.mul_SimpleRefl_in_Refl s t⟩ := by
  simp only [nn]
  let ti1 := fun i ↦ (t((s :: L), (i + 1)) : G)
  calc
    _ = (((fun i ↦ (t((s :: L), i) : G)) 0) :: (List.range L.length).map ti1).count (t : G) := by
      congr 1
      have : ∀(i : Fin L.length), ti1 i.1
        = (fun i ↦ (t((s :: L), i) : G)) (i.1 + 1) := by intro i; rfl
      exact List.range_map_insert_zero this
    _ = ([(fun i ↦ (t((s :: L), i) : G)) 0].count (t : G) +
        ((List.range L.length).map ti1).count (t : G)) := by
      rw [List.count_cons, add_comm]
      congr
      simp only [toPalindrome_i, toPalindrome, List.take, List.reverse_singleton, List.tail,
        gprod_simps, List.count_singleton']
    _ = ([(fun i ↦ (t((s :: L), i) : G)) 0].count (t : G) +
        ((List.range L.length).map (fun i ↦ (t(L, i) : G))).count ((s : G) * t * s)) := by
      congr 1
      let hxh : G → G := fun (x : G) ↦ (s : G) * x * s
      have : Function.Injective hxh := by
        intro a b hab
        simp only [hxh] at hab
        exact mul_left_cancel (mul_right_cancel hab)
      have : ((List.range L.length).map ti1).count (t : G)
          = (((List.range L.length).map ti1).map hxh).count ((s : G) * t * s) := by
        rw [List.count_map_of_injective _ hxh this]
      rw [this, List.map_map]
      congr 1
      rcases L with (_ | ⟨th, ttail⟩)
      · rw [List.length_nil, List.range_zero, List.map_nil, List.map_nil]
      · congr 1
        ext i
        simp only [hxh, ti1, Function.comp_apply, toPalindrome_i,
          toPalindrome, List.take_cons, List.reverse_cons]
        rw [List.tail_append_of_ne_nil _ _]
        simp only [gprod_simps]
        repeat rw [← mul_assoc]
        rw [mul_assoc _ s.1 s.1, gen_square_eq_one s.1 s.2, one_mul, mul_one]
        exact (List.append_singleton_ne_nil (ttail.take i).reverse th)
    _ = _ := by
      congr
      rw [List.count_singleton']
      simp only [toPalindrome_i, toPalindrome, List.reverse_cons, List.take_cons, List.take,
        List.reverse_nil, List.nil_append, List.tail, List.append_nil, gprod_singleton]
      congr 1
      exact propext (Iff.intro Eq.symm Eq.symm)

lemma nn_prod_eta_aux [CoxeterMatrix m] (L : List S) (t : T) : μ₂.gen ^ (nn L t) = ∏ i : Fin L.length,
    eta_aux' (L.get i) ⟨((L.take i.1).reverse : G) * t * L.take i.1, by apply Refl_palindrome_in_Refl⟩ := by
  induction L generalizing t with
  | nil =>
    rw [nn]
    norm_num
  | cons hd tail ih =>
    let sts : T := ⟨hd * t * hd, Refl.mul_SimpleRefl_in_Refl hd t⟩
    rw [nn_cons, pow_add, ih sts]
    let f : Fin (Nat.succ tail.length) → μ₂ := fun i ↦ eta_aux' ((hd :: tail).get i)
      ⟨((hd :: tail).take i.1).reverse * t * ((hd :: tail).take i.1), by apply Refl_palindrome_in_Refl⟩
    calc
      _ = f 0 * ∏ i : Fin tail.length, eta_aux' (tail.get i)
          ⟨((tail.take i.1).reverse : G) * sts * tail.take i.1, by apply Refl_palindrome_in_Refl⟩ := by
        congr
        simp only [f, eta_aux', toPalindrome_i, toPalindrome, List.take, List.reverse_singleton, List.reverse_nil,
          List.tail, List.count_singleton', List.get, gprod_simps]
        rw [pow_ite, pow_one, pow_zero]
      _ = ∏ i : Fin (Nat.succ tail.length), f i := by
        let g : Fin tail.length → μ₂ := fun i ↦ eta_aux' (tail.get i)
          ⟨((tail.take i.1).reverse : G) * sts * tail.take i.1, by apply Refl_palindrome_in_Refl⟩
        have h : ∀(i : Fin tail.length), g i = f ⟨i.val + 1, add_lt_add_right i.prop 1⟩ := by
          intro x
          simp only [g, f, List.get_cons_succ, Fin.eta, List.take_cons_succ,
            eta_aux', List.reverse_cons, gprod_simps]
        exact (prod_insert_zero_fin h).symm

lemma exists_of_nn_ne_zero [CoxeterMatrix m] (L : List S) (t : T) : nn L t > 0 →
    ∃ i : Fin L.length, (toPalindrome_i L i : G) = t := by
  intro h
  unfold nn at h
  obtain ⟨⟨w, hw⟩, h⟩ := List.mem_iff_get.mp (List.count_pos_iff_mem.mp h)
  rw [List.get_map, List.get_range] at h
  rw [List.length_map, List.length_range] at hw
  exact ⟨⟨w, hw⟩, h⟩

local notation "R" => T × μ₂

namespace ReflRepn
noncomputable def pi_aux (s : α) (r : R) : R :=
  ⟨⟨(s : G) * r.1 * (s : G)⁻¹, OrderTwoGen.Refl.conjugate_closed⟩, r.2 * eta_aux s r.1⟩

lemma eta_aux_mul_eta_aux [CoxeterMatrix m] (s : α) (r : R) :
    (eta_aux' s r.1) * (eta_aux' s (pi_aux s r).1) = 1 := by
  simp only [eta_aux', toSimpleRefl, pi_aux]
  let f : G → G := fun x ↦ of m s * x * (of m s)⁻¹
  have : Function.Injective f := by
    intro a b hab
    exact mul_left_cancel (mul_right_cancel hab)
  have : (f (of m s) = f r.1) = (of m s = r.1) := by
    exact propext (Function.Injective.eq_iff this)
  --dsimp only at this
  simp only [f, ← mul_assoc, mul_inv_cancel_right, mul_one] at this
  apply this.symm.subst
    (motive := fun x ↦ ((if of m s = r.1 then μ₂.gen else 1) * if x then μ₂.gen else 1) = 1)
  have (p : Prop) (a1 a2 b1 b2 : μ₂) :
    ite p a1 a2 * ite p b1 b2 = ite p (a1 * b1) (a2 * b2) := by
    by_cases h : p
    · repeat rw [if_pos h]
    · repeat rw [if_neg h]
  rw [this]
  simp only [mul_one, ite_eq_right_iff]
  exact fun _ ↦ μ₂.gen_square

lemma pi_aux_square_identity [CoxeterMatrix m] (s : α) (r : R) : pi_aux s (pi_aux s r) = r := by
  have comp1 : (pi_aux s (pi_aux s r)).1 = r.1 := by
    have : (pi_aux s (pi_aux s r)).1.val = r.1.val := by
      rw [pi_aux, pi_aux]
      simp only [Set.coe_setOf, Set.mem_setOf_eq]
      rw [mul_assoc, mul_assoc, ← mul_inv_rev, of_square_eq_one, inv_one, mul_one,
        ← mul_assoc, of_square_eq_one, one_mul]
    exact SetCoe.ext this
  have comp2 : (pi_aux s (pi_aux s r)).2 = r.2 := by
    have : (pi_aux s (pi_aux s r)).2.val = r.2.val := by
      rw [pi_aux, pi_aux]
      simp only [Set.coe_setOf, eta_aux_aux', toSimpleRefl, Set.mem_setOf_eq]
      have : (eta_aux' s r.1) * (eta_aux' s (pi_aux s r).1) = 1 := by
        exact eta_aux_mul_eta_aux s r
      rw [toSimpleRefl, pi_aux] at this
      rw [mul_assoc, this, mul_one]
    exact SetCoe.ext this
  exact Prod.ext comp1 comp2

noncomputable def pi_aux' [CoxeterMatrix m] (s : α) : Equiv.Perm R where
  toFun r := pi_aux s r
  invFun r := pi_aux s r
  left_inv := by intro r; simp [pi_aux_square_identity]
  right_inv := by intro r; simp [pi_aux_square_identity]

/-noncomputable def alternating_word (s t : α) (n : ℕ) : List α :=
  (List.range n).map (fun x ↦ if x % 2 = 0 then s else t)-/

open AlternatingWord
-- DLevel 2
lemma alternating_word_power (s t : α) (n : ℕ) : (alternating_word s t (2 * n) : List S).gprod
    = (of m s * of m t) ^ n := by
  induction n with
  | zero => simp only [alternating_word, Nat.zero_eq, mul_zero,
    List.range_zero, List.map_nil, pow_zero, gprod_nil]
  | succ k ih =>
    rw [Nat.succ_eq_add_one, pow_add, pow_one, mul_add, mul_one,
      alternating_word_append_even (toSimpleRefl m s) (toSimpleRefl m t) (2 * k) 2 (by simp),
      gprod_append, ih, mul_right_inj]
    repeat rw [alternating_word]
    rfl

lemma alternating_word_relation (s t : α) : (alternating_word s t (2 * m s t) : List S).gprod = 1 := by
  rw [alternating_word_power s t (m s t), of_relation]

-- DLevel 3
lemma alternating_word_palindrome (s t : α) (n : ℕ) (i : Fin n) :
    toPalindrome_i (alternating_word s t n : List S) i.1 = (alternating_word s t (2 * i.1 + 1) : List S) := by
  rw [toPalindrome_i, toPalindrome,
      alternating_word_take (toSimpleRefl m s) (toSimpleRefl m t) _ _ (by linarith [i.2] : _)]
  set s' := toSimpleRefl m s
  set t' := toSimpleRefl m t
  by_cases h : (Even (i.1 + 1))
  . rw [even_alternating_word_reverse _ _ _ h]
    nth_rw 2 [alternating_word]
    rw [List.tail_cons, two_mul, add_assoc, add_comm, ← add_assoc,
      alternating_word_append_even s' t' (i.1 + 1) i.1 h, add_comm]
  . rw [odd_alternating_word_reverse _ _ _ (Nat.odd_iff_not_even.mpr h)]
    nth_rw 2 [alternating_word]
    rw [List.tail_cons, two_mul, add_assoc, add_comm, ← add_assoc,
      alternating_word_append_odd s' t' (i.1 + 1) i.1 (Nat.odd_iff_not_even.mpr h),
      add_comm]

lemma alternating_word_palindrome_periodic (s t : α) (i : ℕ) :
    ((alternating_word s t (2 * (i + m s t) + 1) : List S) : G)
    = ((alternating_word s t (2 * i + 1) : List S) : G) := by
  rw [mul_add, add_assoc, add_comm _ 1, ← add_assoc,
    alternating_word_append_odd (s : S) t (2 * i + 1) (2 * m s t) (by use i : Odd (2 * i + 1)),
    gprod_append, @symmetric _ m _ s t, alternating_word_relation, mul_one]

lemma pi_relation_word_nn_even (s s' : α) (t : T) : Even (nn (alternating_word (s : S) s' (2 * m s s')) t) := by
  use ((List.range (m s s')).map fun i ↦ (alternating_word (s : S) s' (2 * i + 1)).gprod).count (t : G)
  rw [nn, alternating_word_length]
  let f := fun i ↦ (alternating_word s s' (2 * i + 1) : List S).gprod
  calc
    _ = ((List.range (2 * m s s')).map f).count (t : G) := by
      rw [← List.map_coe_finRange, List.map_map, List.map_map]
      congr
      ext x
      dsimp only [Function.comp_apply]
      rw [alternating_word_palindrome s s' (2 * m s s') x]
    _ = ((List.range' 0 (m s s') 1).map f).count (t : G) +
        ((List.range' (0 + 1 * m s s') (m s s') 1).map f).count (t : G) := by
      rw [List.range_eq_range', ← List.count_append, ← List.map_append, List.range'_append 0 (m s s') (m s s') 1]
      congr
      ring
    _ = ((List.range (m s s')).map f).count (t : G) +
        ((List.range' (m s s') (m s s') 1).map f).count (t : G) := by
      congr
      exact (List.range_eq_range' (m s s')).symm
      ring
    _ = ((List.range (m s s')).map f).count (t : G) +
        ((List.range (m s s')).map f).count (t : G) := by
      congr 2
      rw [List.range'_eq_map_range]
      repeat rw [List.map_map]
      congr
      ext x
      simp only [Function.comp_apply]
      rw [add_comm (m s s') x]
      exact alternating_word_palindrome_periodic s s' x
    _ = _ := by rfl

lemma pi_aux_list_in_T (L : List α) (t : T) :
    (L.map (toSimpleRefl m) : G) * t * (L.reverse.map (toSimpleRefl m)) ∈ T := by
  rw [← List.reverse_map, gprod_reverse]
  exact Refl.conjugate_closed

-- DLevel 4
lemma pi_aux_list (L : List α) (r : R) : (L.map pi_aux').prod r =
    ((⟨(L.map (toSimpleRefl m)) * r.1 * (L.reverse.map (toSimpleRefl m)), pi_aux_list_in_T L r.1⟩,
    r.2 * μ₂.gen ^ nn (L.reverse.map (toSimpleRefl m)) r.1) : R) := by
  induction L with
  | nil => simp only [nn, List.map_nil, List.prod_nil, Equiv.Perm.coe_one, id_eq,
    Set.mem_setOf_eq, List.reverse_nil, List.length_nil, List.range_zero, List.nodup_nil,
    List.count_nil, pow_zero, mul_one, gprod_nil, one_mul]
  | cons hd tail ih =>
    rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply, ih, pi_aux']
    ext
    . simp only [List.map_cons, toSimpleRefl, List.reverse_cons,
        List.map_append, List.map_nil, gprod_append, pi_aux]
      dsimp only [SimpleRefl, Set.mem_setOf_eq, Set.coe_setOf, id_eq, μ₂.gen, Equiv.coe_fn_mk]
      rw [gprod_cons, gprod_singleton]
      repeat rw [mul_assoc]
      simp only [mul_right_inj]
      exact of_inv_eq_of m
    . simp only [List.map_cons, pi_aux]
      dsimp only [id_eq, Set.mem_setOf_eq, Equiv.coe_fn_mk]
      simp only [eta_aux_aux', List.reverse_cons, List.map_append, List.map_cons, List.map_nil]
      rw [mul_assoc]
      congr
      simp only [nn_prod_eta_aux, gprod_reverse, List.length_cons]
      set t := tail.reverse.map (toSimpleRefl m)
      set th := t ++ [toSimpleRefl m hd]
      set n := t.length
      set g := fun x : Fin n ↦ eta_aux' (t.get x)
        ⟨(t.take x : G)⁻¹ * r.1 * t.take x, (_ : (fun x => x ∈ Refl S) ((t.take x : G)⁻¹ * r.1 * t.take x))⟩
      set g' := fun x : Fin th.length ↦ eta_aux' (th.get x)
        ⟨(th.take x : G)⁻¹ * r.1 * th.take x, (_ : (fun x => x ∈ Refl S) ((th.take x : G)⁻¹ * r.1 * th.take x))⟩
      have len : n + 1 = th.length := (List.length_append_singleton t (toSimpleRefl m hd)).symm
      let f : Fin (n + 1) → μ₂ := fun x ↦ eta_aux' (th.get ⟨x, by rw [← len]; exact x.2⟩)
        ⟨(th.take x : G)⁻¹ * r.1 * th.take x, by nth_rw 2 [← inv_inv (th.take x : G)]; apply Refl.conjugate_closed⟩
      have heqf : HEq g' f := by
        apply (Fin.heq_fun_iff len.symm).2
        have (i : Fin (th.length)) (j : Fin (n + 1)) : i.1 = j.1 → g' i = f j := by
          intro ieqj
          rw [Fin.eq_mk_iff_val_eq.mpr ieqj]
        exact fun i => this i { val := i.1, isLt := len.symm ▸ i.isLt } rfl
      have replace_prod : ∏ i : Fin (th.length), g' i = ∏ i : Fin (n + 1), f i := by
        congr 1
        exact congrArg Fin (len.symm)
        repeat rw [len]
      rw [replace_prod, prod_insert_last_fin, mul_comm]
      congr
      . rw [List.get_last]
        simp only [List.length_map, List.length_reverse, Fin.val_nat_cast, Nat.mod_succ,
          lt_self_iff_false, not_false_eq_true]
      . rw [← gprod_reverse]
        simp only [Fin.val_nat_cast, Nat.mod_succ, th, n, t]
        rw [List.take_append_of_le_length (by rfl), List.take_length,
          List.map_reverse, List.reverse_reverse]
      . simp only [Fin.val_nat_cast, Nat.mod_succ]
        rw [List.take_left]
      . funext i
        simp only [List.get_map, Fin.coe_eq_castSucc, Fin.coe_castSucc]
        simp [g,List.get_append]
        . congr 1
          . simp only [Fin.coe_castSucc, th]
            rw [List.get_append]
          . simp only [Fin.coe_castSucc, Subtype.mk.injEq, th]
            rw [List.take_append_of_le_length]
            simp only [n] at i
            apply le_of_lt i.2

-- DLevel 3
lemma pi_aux_list_mul (s t : α) : ((pi_aux' s : Equiv.Perm R) * (pi_aux' t : Equiv.Perm R)) ^ n
    = ((alternating_word s t (2 * n)).map pi_aux' : List (Equiv.Perm R)).prod := by
  -- induction on n
  induction' n with k ih
  . simp only [pow_zero, alternating_word, Nat.zero_eq, mul_zero, List.range_zero, List.map_nil,
      List.prod_nil]
  . rw [Nat.succ_eq_add_one, pow_succ, mul_add, add_comm, mul_one,
      alternating_word_append_even s t 2 (2 * k) (by simp)]
    simp only [add_tsub_cancel_left, List.map_append, List.prod_append, ← ih, mul_left_inj,
      AlternatingWord.alternating_word]
    rw [pow_mul_comm']
    rfl

-- DLevel 3
lemma pi_relation (s t : α) : ((pi_aux' s : Equiv.Perm R) * (pi_aux' t : Equiv.Perm R)) ^ m s t = 1 := by
  have (r : R) : (((pi_aux' s : Equiv.Perm R) * (pi_aux' t : Equiv.Perm R)) ^ m s t) r = r := by
    rw [pi_aux_list_mul, pi_aux_list]
    ext
    . simp only []
      rw [List.map_reverse, gprod_reverse]
      repeat rw [alternating_word_map, alternating_word_relation]
      simp only [one_mul, inv_one, mul_one]
    . simp only [Submonoid.coe_mul, Subgroup.coe_toSubmonoid,
        SubmonoidClass.coe_pow, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg,
        Units.val_one, Int.reduceNeg, ne_eq, Units.ne_zero, not_false_eq_true, mul_eq_left₀]
      rw [List.map_reverse, alternating_word_map, even_alternating_word_reverse]
      have : m s t = m t s := by apply symmetric
      rw [this]
      apply Even.neg_one_pow
      apply pi_relation_word_nn_even
      norm_num
  exact Equiv.Perm.disjoint_refl_iff.mp fun x ↦ Or.inl (this x)

noncomputable def pi : G →* Equiv.Perm R := lift m (fun s ↦ pi_aux' s) (by simp [pi_relation])

lemma map_gprod_eq_map_prod (r : R) (L : List α) :
  pi (L.map (toSimpleRefl m)).gprod r = (L.map pi_aux').prod r := by
  induction L with
  | nil => simp only [List.map_nil, gprod_nil, map_one,
      Equiv.Perm.coe_one, id_eq, List.prod_nil]
  | cons hd tail ih =>
    simp only [List.map_cons, List.prod_cons, Equiv.Perm.coe_mul,
      Function.comp_apply, gprod_cons, map_mul]
    congr 1

-- Equation 1.16
-- Probably needs induction and wrangling with Finset.prod
-- DLevel 5
lemma pi_value (g : G) (L : List S) (h : g = L) (r : R) :
  (pi g) r = (⟨g * r.1 * g⁻¹, by apply Refl.conjugate_closed⟩, r.2 * μ₂.gen ^ nn L.reverse r.1)
  := by
  rw [h]
  rcases (toSimpleRefl_surj_list m L) with ⟨K, ek⟩
  rw [← ek, map_gprod_eq_map_prod, pi_aux_list]
  congr
  · rw [← List.reverse_map, gprod_reverse, inv_inj]
  · rw [← List.reverse_map]

-- DLevel 3
-- (maybe some list wrangling)
lemma pi_inj : Function.Injective (pi : G → Equiv.Perm R) := by
  apply (MonoidHom.ker_eq_bot_iff pi).mp
  apply (Subgroup.eq_bot_iff_forall (MonoidHom.ker pi)).mpr
  intro w wker
  by_contra! wne1
  rcases exists_reduced_word S w with ⟨L, ⟨hL, hw⟩⟩
  have L_notempty: L ≠ [] := by
    contrapose! wne1
    rw [hw, wne1, gprod_nil]
  have L_rev_notempty : L.reverse ≠ [] := List.reverseList_nonEmpty L_notempty
  have L_rev_ge1 : L.reverse.length > 0 := List.length_pos.mpr L_rev_notempty
  have : pi w ≠ 1 := by
    let s := L.getLast L_notempty
    let t : T := ⟨s, SimpleRefl_is_Refl (Subtype.mem s)⟩
    have : nn L.reverse t = 1 := by
      have zero_works : (toPalindrome_i L.reverse 0).gprod = [s] := by
        rw [toPalindrome_i, List.reverse_head L L_notempty]
        simp only [SimpleRefl, toPalindrome, zero_add, List.take_cons_succ, List.take_zero,
          List.reverse_cons, List.reverse_nil, List.nil_append, List.tail_cons,
          List.singleton_append]
      have other_fail (j : Fin L.reverse.length) :
        j ≠ ⟨0, Fin.pos j⟩ → (toPalindrome_i L.reverse j).gprod ≠ [s] := by
        rw [← zero_works]
        have : reduced_word L.reverse := reverse_is_reduced hL
        apply distinct_toPalindrome_i_of_reduced this j ⟨0, Fin.pos j⟩
      rw [nn]
      have (n : ℕ) : List.range (n + 1) = 0 :: (List.range n).map Nat.succ :=
        List.range_succ_eq_map n
      rw [← Nat.sub_add_cancel L_rev_ge1, List.length_reverse, ← Nat.one_eq_succ_zero, this,
        List.map_cons, List.count_cons, zero_works]
      nth_rw 3 [← zero_add 1]
      congr
      . apply List.count_eq_zero.2
        simp only [SimpleRefl, List.map_map, List.mem_map, List.mem_range, Function.comp_apply,
          not_exists, not_and]
        simp only [] at other_fail
        intro j k
        by_contra a
        have : Nat.succ j < L.reverse.length := by
          rw [List.length_reverse, Nat.succ_eq_add_one]
          exact Nat.add_lt_of_lt_sub k
        apply other_fail ⟨Nat.succ j, this⟩
        . simp only [SimpleRefl, ne_eq, Fin.mk.injEq, Nat.succ_ne_zero, not_false_eq_true]
        . simp only [gprod_singleton]
          exact a
      . simp only [gprod_singleton, ↓reduceIte]
    have : (pi w) (t, 1) ≠ (t, 1) := by
      rw [pi_value w L hw (t, 1), this]
      exact fun h ↦ μ₂.gen_ne_one (Prod.ext_iff.mp h).2
    intro h
    rw [h] at this
    exact this rfl
  exact this wker

end ReflRepn

noncomputable def eta (g : G) (t : T) : μ₂ := (ReflRepn.pi g⁻¹ ⟨t, 1⟩).2

lemma pi_eval (g : G) (t : T) (ε : μ₂): ReflRepn.pi g (t, ε)
  = (⟨(g : G) * t * (g : G)⁻¹, OrderTwoGen.Refl.conjugate_closed⟩, ε * eta g⁻¹ t) := by
  rcases toGroup_expression m g with ⟨L, eL⟩
  rw [ReflRepn.pi_value g L eL]
  ext
  . rfl
  . simp only [SubmonoidClass.coe_pow, Units.val_mul, Units.val_pow_eq_pow_val,
      Units.val_neg, Units.val_one, mul_eq_mul_left_iff, Units.ne_zero, or_false]
    congr
    rw [eta, inv_inv, ReflRepn.pi_value g L eL, one_mul]

lemma eta_equiv_nn {g : G} {t : T} : ∀ {L : List S}, g = L → eta g t = μ₂.gen ^ nn L t := by
  intro L geqL
  have := (geqL.symm.subst (motive := fun x ↦ x⁻¹ = _) (gprod_reverse L).symm)
  rw [eta, ReflRepn.pi_value g⁻¹ L.reverse this (t, 1), List.reverse_reverse, one_mul]

lemma eta_equiv_nn' {L : List S} {t : T} : eta L t = μ₂.gen ^ nn L t := eta_equiv_nn rfl

lemma eta_t_equal_lemma (t : T) (s : S) (L : List S) (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ L.length) (h3 : (t : G) = (L : G) * s * L.reverse) :
    eta_aux' (L.get ⟨L.length - n, (by omega)⟩) ⟨((L ++ [s] ++ L.reverse).take (L.length - n)).reverse * t * (L ++ [s] ++ L.reverse).take (L.length - n),
    by apply Refl_palindrome_in_Refl⟩ = eta_aux' (L.get ⟨L.length - n, (by omega)⟩)
    ⟨((L ++ [s] ++ L.reverse).take (L.length + n)).reverse * t * (L ++ [s] ++ L.reverse).take (L.length + n),
    by apply Refl_palindrome_in_Refl⟩ := by
  simp_rw [eta_aux']
  rw [propext (SimpleRefl_eq_iff_eq m _ _)]
  congr 2
  have : (L ++ [s] ++ L.reverse).take (L.length + n) =
      L ++ [s] ++ (L.reverse.take (n - 1)) := by
    have : L.length + n = (L ++ [s]).length + (n - 1) := by
      rw [List.length_append_singleton, ← Nat.add_sub_assoc h1, add_assoc,
        add_comm 1 n, ← add_assoc, Nat.add_sub_cancel]
    simp_rw [this, List.take_append]
  simp_rw [this]; clear this
  have : (L ++ [s] ++ L.reverse).take (L.length - n) = L.take (L.length - n) := by
    have : L.length - n ≤ (L ++ [s]).length := by
      rw [List.length_append_singleton]; omega
    simp_rw [List.take_append_of_le_length this,
      List.take_append_of_le_length (Nat.sub_le L.length n)]
  simp_rw [this]; clear this
  simp only [SimpleRefl, Set.mem_setOf_eq, gprod_reverse, List.append_assoc, List.singleton_append,
    List.reverse_append, List.reverse_cons, gprod_append, gprod_simps]
  have : (L.reverse.take (n - 1)).gprod = (L.reverse.take n).gprod * (L.get ⟨L.length - n, by omega⟩ : G) := by
    rcases n with (_ | m)
    · contradiction
    · simp only [Nat.succ_sub_succ_eq_sub, tsub_zero, List.take_succ, gprod_append]
      rw [mul_assoc]
      apply self_eq_mul_right.mpr
      rw [List.get?_eq_get (by rw [List.length_reverse]; exact h2)]
      simp only [Option.toList_some, gprod_singleton]
      rw [List.get_reverse' L _ (by omega)]
      simp only [Nat.succ_eq_add_one, add_comm, Nat.sub_sub]
      exact of_square_eq_one' _ (Subtype.mem _)
  simp_rw [this]; clear this
  simp only [Set.mem_setOf_eq, mul_inv_rev, inv_eq_self'', h3, gprod_simps]
  simp_rw [← mul_assoc (s : G) (s : G), of_square_eq_one' m s.2,
    one_mul, ← mul_assoc _ _ (L.get _ : G)]
  congr 2
  have : (L.reverse.take n : G) = (L : G)⁻¹ * (L.take (L.length - n) : G) := by
    nth_rw 2 [← List.take_append_drop (List.length L - n) L]
    simp only [gprod_simps]
    rw [← gprod_reverse, List.reverse_drop, Nat.sub_sub_self h2]
  simp [this]; group

lemma eta_t_product_lemma (t : T) (s : S) (L : List S) (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ L.length) (h3 : (t : G) = (L : G) * s * L.reverse) :
    eta_aux' ((L ++ [s] ++ L.reverse).get ⟨L.length - n, by simp_rw [List.length_append, List.length_singleton, List.length_reverse]; omega⟩)
    ⟨((L ++ [s] ++ L.reverse).take (L.length - n)).reverse * t * (L ++ [s] ++ L.reverse).take (L.length - n),
    by apply Refl_palindrome_in_Refl⟩ * eta_aux' ((L ++ [s] ++ L.reverse).get ⟨L.length + n, by simp_rw [List.length_append, List.length_singleton, List.length_reverse]; linarith⟩)
    ⟨((L ++ [s] ++ L.reverse).take (L.length + n)).reverse * t * (L ++ [s] ++ L.reverse).take (L.length + n),
    by apply Refl_palindrome_in_Refl⟩ = 1 := by
  apply (μ₂.mul_eq_one_iff_eq _ _).mpr
  calc
    _ = eta_aux' (L.get ⟨L.length - n, (by omega)⟩) ⟨((L ++ [s] ++ L.reverse).take (L.length - n)).reverse * t * (L ++ [s] ++ L.reverse).take (L.length - n),
        by apply Refl_palindrome_in_Refl⟩ := by
      rw [@List.get_append_left _ (L.length - n) (L ++ [s]) L.reverse
        (by rw [List.length_append, List.length_singleton]; omega)
        (by simp_rw [List.length_append, List.length_singleton, List.length_reverse]; omega),
        @List.get_append_left _ (L.length - n) L [s] (by omega)
        (by rw [List.length_append, List.length_singleton]; omega)]
    _ = eta_aux' (L.get ⟨L.length - n, (by omega)⟩)
      ⟨((L ++ [s] ++ L.reverse).take (L.length + n)).reverse * t * (L ++ [s] ++ L.reverse).take (L.length + n),
      by apply Refl_palindrome_in_Refl⟩ := eta_t_equal_lemma t s L n h1 h2 h3
    _ = eta_aux' ((L ++ [s] ++ L.reverse).get ⟨L.length + n, by simp_rw [List.length_append, List.length_singleton, List.length_reverse]; linarith⟩)
        ⟨((L ++ [s] ++ L.reverse).take (L.length + n)).reverse * t * (L ++ [s] ++ L.reverse).take (L.length + n),
        by apply Refl_palindrome_in_Refl⟩ := by
      rw [@List.get_append_right _ (L.length + n) (L ++ [s]) L.reverse
        (by rw [List.length_append_singleton]; linarith)
        (by simp_rw [List.length_append, List.length_singleton, List.length_reverse]; linarith)
        (by simp_rw [List.length_append, List.length_singleton, List.length_reverse]; omega),
        ← List.get_reverse L.reverse _
        (by simp_rw [List.length_append, List.length_singleton, List.length_reverse]; omega)]
      conv=>
        enter [2, 1]
        rw [List.get_reverse _ _
          (by simp_rw [List.length_append, List.length_singleton, List.length_reverse]; omega)
          (by rw [List.length_append, List.length_singleton, List.length_reverse]; omega),
          List.get_reverse' _ _ (by simp_rw [List.length_append_singleton]; omega)]
        enter [2, 1, 2, 1, 1]
        rw [List.length_append, List.length_singleton, add_comm,
          ← Nat.sub_sub, Nat.add_sub_cancel]
      simp only []
      conv=>
        enter [2, 1, 2, 1]
        rw [Nat.sub_sub, ← Nat.add_sub_assoc h1, add_comm, Nat.add_sub_cancel]

lemma eta_t (t : T) : eta (t : G) t = μ₂.gen := by
  rcases h : t with ⟨t', ⟨g, s, ht⟩⟩
  obtain ⟨L, hgL⟩ := @exists_prod G _ S _ g
  rw [hgL] at ht; clear hgL
  have tLgL : t' = (L ++ [s] ++ L.reverse : G) := by
    rw [gprod_append, gprod_append, gprod_singleton, gprod_reverse]
    exact ht
  simp_rw [tLgL] at *; clear tLgL
  clear ht
  rw [@eta_equiv_nn α m hm _ _ (L ++ [s] ++ L.reverse) rfl,
    nn_prod_eta_aux]
  let fnat : ℕ → μ₂ := fun i ↦ if h : i < (L ++ [s] ++ L.reverse).length then
    eta_aux' ((L ++ [s] ++ L.reverse).get ⟨i, h⟩)
    ⟨((L ++ [s] ++ L.reverse).take i).reverse * t * (L ++ [s] ++ L.reverse).take i,
    by apply Refl_palindrome_in_Refl⟩ else 1
  calc
    _ = ∏ i : Fin (L ++ [s] ++ L.reverse).length, fnat i := by
      congr 1
      ext x
      simp only [fnat, x.2, reduceDite]
      congr
      rw [h]
    _ = ∏ i : Fin (2 * L.length + 1), fnat i := by
      congr 1
      all_goals rw [List.append_singleton_reverse_length]
    _ = fnat L.length * ∏ i : Fin L.length, (fnat i * fnat (2 * L.length - i)) :=
      @halve_odd_prod μ₂ _ L.length fnat
    _ = fnat L.length * ∏ i : Fin L.length, (fnat (L.length - 1 - i) * fnat (L.length + 1 + i)) := by
      rw [← prod_reverse]
      congr 2
      ext x
      rw [two_mul, add_assoc, Nat.add_sub_assoc (by omega)]
      congr
      simp_rw [Nat.sub_sub]
      exact Nat.sub_sub_self (by omega)
    _ = μ₂.gen * ∏ i : Fin L.length, (fnat (L.length - 1 - i) * fnat (L.length + 1 + i)) := by
      congr
      simp_rw [fnat, List.append_assoc, List.singleton_append, List.length_append,
        List.length_cons, List.length_reverse, Set.mem_setOf_eq, gprod_reverse,
        lt_add_iff_pos_right, Nat.zero_lt_succ, reduceDite, List.take_left, eta_aux']
      clear fnat
      rw [List.get_append_left _ _ (List.lt_append s L),
        @List.get_append_right _ _ _ _ (lt_irrefl L.length) _
        (by simp only [List.length_singleton, Nat.sub_self, zero_lt_one])]
      simp only [List.length_singleton, le_refl, Nat.sub_self,
        Fin.zero_eta, List.get_cons_zero, eta_aux']
      simp_rw [h, gprod_append, gprod_reverse, gprod_singleton]
      group
      exact ite_true _ _
    _ = μ₂.gen * ∏ __ : Fin L.length, (1 : μ₂) := by
      congr
      ext x
      have h1 : L.length - 1 - x.1 < (L ++ [s] ++ L.reverse).length := by
        simp_rw [List.length_append, List.length_singleton, List.length_reverse]; omega
      have h2 : L.length + 1 + x.1 < (L ++ [s] ++ L.reverse).length := by
        simp_rw [List.length_append, List.length_singleton, List.length_reverse]; omega
      simp only [fnat, h1, h2, reduceDite]
      clear fnat
      have h3 : (t : G) = (L : G) * s * L.reverse := by
        simp_rw [h, gprod_append, gprod_reverse, gprod_singleton]
      simp_rw [Nat.sub_sub, Nat.add_assoc]
      rw [eta_t_product_lemma t s L (1 + x.1) (Nat.le_add_right 1 x.1) (by omega : 1 + x.1 ≤ L.length) h3]
    _ = _ := by
      rw [Finset.prod_const_one, mul_one]

lemma lt_iff_eta_eq_gen (g : G) (t : T) : ℓ(t * g) < ℓ(g) ↔ eta g t = μ₂.gen := by
  have mpr (g : G) (t : T) : eta g t = μ₂.gen → ℓ(t * g) < ℓ(g) := by
    intro h
    obtain ⟨L, hL⟩ := exists_reduced_word S g
    have h1 : nn L t > 0 := by
      have : (μ₂.gen)^(nn L t) = μ₂.gen := by rw [← eta_equiv_nn']; rw [← hL.right]; assumption
      exact Odd.pos (μ₂.odd_pow_iff_eq_gen.mp this)
    have : ∃ i : Fin L.length, (Palindrome.toPalindrome_i L i:G) = t := exists_of_nn_ne_zero L t h1
    obtain ⟨i, hi⟩ := this;
    rw [← hi, hL.right, Palindrome.removeNth_of_palindrome_prod L i]
    have h2 : (L.removeNth i).length < L.length := by
      rw [List.length_removeNth i.2]
      exact Nat.pred_lt' i.2
    rw [←OrderTwoGen.length_eq_iff.mp hL.left]
    exact lt_of_le_of_lt length_le_list_length h2

  have mp (g : G) (t : T) : ℓ(t * g) < ℓ(g) → eta g t = μ₂.gen := by
    contrapose
    intro h
    rw [μ₂.not_iff_not'] at h
    -- let g_inv_t_g := toRefl' m (g⁻¹ * t * g) t g rfl
    have g_inv_t_g_in_T : g⁻¹ * t * g ∈ T := by nth_rw 2 [← (inv_inv g)]; exact OrderTwoGen.Refl.conjugate_closed
    let g_inv_t_g : T := ⟨(g⁻¹ * t * g), g_inv_t_g_in_T⟩
    have eq1 : ReflRepn.pi ((t : G) * g)⁻¹ (t, μ₂.gen) = (⟨(g⁻¹ * t * g), g_inv_t_g_in_T⟩, μ₂.gen * eta ((t : G) * g) t) := by
      rw [pi_eval]
      apply Prod.eq_iff_fst_eq_snd_eq.mpr
      constructor
      . simp only [Refl, SimpleRefl, mul_inv_rev, inv_mul_cancel_right, inv_inv, Subtype.mk.injEq, ←mul_assoc]
      simp only [Subtype.mk.injEq, inv_inv]
    have eq2 : ReflRepn.pi ((t : G) * g)⁻¹ (t, μ₂.gen) = (g_inv_t_g, 1) := by
      rw [mul_inv_rev, map_mul, Equiv.Perm.coe_mul, Function.comp_apply, Refl.inv_eq_self]
      calc
        (ReflRepn.pi g⁻¹) ((ReflRepn.pi ↑t) (t, μ₂.gen)) = (ReflRepn.pi g⁻¹) (t, 1) := by
          congr; rw [pi_eval];
          simp only [Refl, SimpleRefl, mul_inv_cancel_right, Prod.mk.injEq, true_and]
          rw [Refl.inv_eq_self, eta_t]; exact μ₂.gen_square
        _ = (g_inv_t_g, 1) := by
          rw [pi_eval]
          simp only [Refl, SimpleRefl, inv_inv, one_mul, Prod.mk.injEq, true_and]; exact h;
    have : eta ((t : G) * g) t = μ₂.gen := by
      rw [eq1] at eq2
      have : μ₂.gen * eta ((t : G) * g) t = 1 := (Prod.eq_iff_fst_eq_snd_eq.mp eq2).right
      apply (@mul_left_cancel_iff _ _ _ μ₂.gen).mp
      rw [μ₂.gen_square]; assumption;
    let hh := mpr (t * g) t this
    rw [← mul_assoc, ← pow_two, OrderTwoGen.Refl.square_eq_one, one_mul] at hh
    rw [not_lt]
    exact le_of_lt hh
  exact Iff.intro (mp g t) (mpr g t)

end ReflRepresentation

lemma strong_exchange : ∀ (L : List S) (t : T), ℓ((t:G) * L) < ℓ(L) →
  ∃ (i : Fin L.length), (t : G) * L = (L.removeNth i) := by
  intro L t h
  have eta_eq_gen : eta L t = μ₂.gen := (lt_iff_eta_eq_gen L t).mp h
  have h1 : nn L t > 0 := by
    have : (μ₂.gen)^(nn L t) = μ₂.gen := by rw [← eta_equiv_nn']; assumption
    exact Odd.pos (μ₂.odd_pow_iff_eq_gen.mp this)
  have : ∃ i : Fin L.length, (Palindrome.toPalindrome_i L i:G) = t := exists_of_nn_ne_zero L t h1
  obtain ⟨i, hi⟩ := this; use i; rw [← hi]
  exact Palindrome.removeNth_of_palindrome_prod L i

lemma exchange : OrderTwoGen.ExchangeProp S := by
  intro L t _ h2
  obtain ⟨i, hi⟩ := strong_exchange L ⟨t.val, (OrderTwoGen.SimpleRefl_is_Refl t.prop)⟩ (length_smul_lt_of_le h2)
  exact ⟨i, hi⟩

end CoxeterMatrix

namespace CoxeterMatrix
open OrderTwoGen

variable {α : Type*} [DecidableEq α] {m : Matrix α α ℕ} [cm : CoxeterMatrix m]

instance ofCoxeterSystem : CoxeterSystem (toGroup m) (SimpleRefl m) where
  order_two := order_two m
  expression := toGroup_expression m
  exchange := exchange

instance ofCoxeterGroup : CoxeterGroup (toGroup m) where
  S := SimpleRefl m
  order_two := order_two m
  expression := toGroup_expression m
  exchange := exchange
  -- matrix x y := sorry
  -- symmetric := sorry -- cm.symmtric
  -- oneIff := sorry -- cm.oneIff


end CoxeterMatrix
