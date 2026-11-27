/-
Erdős Problem 1061: the statement of Eric Li's claim (arXiv:2606.25849v1, Theorem 1.1: for every fixed R > 0,
S(x) / (x (log x)^R) → ∞), written by the registrar on 2026-11-26 over the counting function `S` copied verbatim from
google-deepmind/formal-conjectures, FormalConjectures/ErdosProblems/1061.lean at commit 9097e2f9 (Apache-2.0;
Copyright 2026 The Formal Conjectures Authors), with the FormalConjecturesUtil import replaced by Mathlib.
Ordered pairs are counted, as in the paper. The searcher may not alter the definition or the statement.
References: erdosproblems.com/1061; Guy, Unsolved Problems in Number Theory, B15.
-/
module

public import Mathlib

@[expose] public section

open Filter Asymptotics
open scoped ArithmeticFunction.sigma

namespace Erdos1061

/-- Let `S x` count the number of **ordered** pairs of positive integers `(a, b)` with `a + b ≤ x`
such that `σ(a) + σ(b) = σ(a + b)`, where `σ` is the sum of divisors function. -/
noncomputable abbrev S (x : ℝ) : ℝ :=
  ((Finset.Icc 1 ⌊x⌋₊ ×ˢ Finset.Icc 1 ⌊x⌋₊).filter fun (a, b) ↦
      a + b ≤ x ∧ σ 1 a + σ 1 b = σ 1 (a + b)).card

-- ===== Blueprint rooms (in blueprint order) =====

-- N01 bienvenu_prop21_uniform [literature_import]
theorem bienvenu_prop21_uniform (d t : ℕ) (A0 B0 L0 cV ε : ℝ) (hcV : 0 < cV) (hε : 0 < ε) :
    ∃ N0 : ℝ, ∀ (N : ℝ) (c : Fin t → ℤ) (L : Fin t → Fin d → ℤ) (K : Set (Fin d → ℝ))
      (β : ℕ → ℝ) (F : Finset (Fin d → ℤ)),
      N0 ≤ N →
      (∀ i j, i ≠ j → LinearIndependent ℚ ![fun k => (L i k : ℚ), fun k => (L j k : ℚ)]) →
      (∀ p : ℕ, β p = ((p : ℝ) / (p - 1)) ^ t / (p : ℝ) ^ d *
        ((Fintype.piFinset fun _ : Fin d => Finset.range p).filter
          (fun n => ∀ i, ¬ (p : ℤ) ∣ c i + ∑ j, L i j * (n j : ℤ))).card) →
      (∀ p : ℕ, p.Prime → 0 < β p) →
      ((∑ i, |(c i : ℝ)|) / N + ∑ i, ∑ j, |(L i j : ℝ)|) / Real.log N ^ B0 ≤ L0 →
      Convex ℝ K →
      (∀ v ∈ K, ∀ j, |v j| ≤ N) →
      cV * N ^ d * Real.log N ^ (-A0) ≤ (MeasureTheory.volume K).toReal →
      (∀ v ∈ K, ∀ i, N ^ ((9 : ℝ) / 10) ≤ (c i : ℝ) + ∑ j, (L i j : ℝ) * v j) →
      (∀ n : Fin d → ℤ, n ∈ F ↔ (fun j => (n j : ℝ)) ∈ K) →
      |(∑ n ∈ F, ∏ i, (if 0 < c i + (∑ j, L i j * n j) ∧ (c i + ∑ j, L i j * n j).natAbs.Prime
            then Real.log ((c i + ∑ j, L i j * n j : ℤ) : ℝ) else 0)) /
          ((MeasureTheory.volume K).toReal * ∏' p : Nat.Primes, β p) - 1| ≤ ε := by
  sorry

-- N02 bienvenu_lemma12_singular_series [literature_import]
theorem bienvenu_lemma12_singular_series (d t : ℕ) (c : Fin t → ℤ) (L : Fin t → Fin d → ℤ) (β : ℕ → ℝ)
    (hfc : ∀ i j, i ≠ j → LinearIndependent ℚ ![fun k => (L i k : ℚ), fun k => (L j k : ℚ)])
    (hβ : ∀ p : ℕ, β p = ((p : ℝ) / (p - 1)) ^ t / (p : ℝ) ^ d *
        ((Fintype.piFinset fun _ : Fin d => Finset.range p).filter
          (fun n => ∀ i, ¬ (p : ℤ) ∣ c i + ∑ j, L i j * (n j : ℤ))).card)
    (hpos : ∀ p : ℕ, p.Prime → 0 < β p) :
    Multipliable (fun p : Nat.Primes => β p) ∧ 0 < ∏' p : Nat.Primes, β p := by
  sorry

lemma sigma_mul_coprime (a b : ℕ) (h : Nat.Coprime a b) : σ 1 (a * b) = σ 1 a * σ 1 b :=
  ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h

lemma sigma_prime_pow' (p i : ℕ) (hp : p.Prime) :
    σ 1 (p ^ i) = ∑ k ∈ Finset.range (i + 1), p ^ k :=
  ArithmeticFunction.sigma_one_apply_prime_pow hp

lemma sigma_prime' (p : ℕ) (hp : p.Prime) : σ 1 p = p + 1 := by
  have := sigma_prime_pow' p 1 hp
  simp [Finset.sum_range_succ] at this
  rw [this]; ring

-- N03 sigma_values_triple [algebraic_identity]
theorem sigma_values_triple :
    σ 1 54000 = 193440 ∧ σ 1 111600 = 399776 ∧ σ 1 1828800 = 6551168 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [show (54000 : ℕ) = 2 ^ 4 * 3 ^ 3 * 5 ^ 3 by norm_num,
      sigma_mul_coprime _ _ (by norm_num), sigma_mul_coprime _ _ (by norm_num),
      sigma_prime_pow' _ _ Nat.prime_two, sigma_prime_pow' _ _ Nat.prime_three,
      sigma_prime_pow' _ _ Nat.prime_five]
    simp [Finset.sum_range_succ]
  · rw [show (111600 : ℕ) = 2 ^ 4 * 3 ^ 2 * 5 ^ 2 * 31 by norm_num,
      sigma_mul_coprime _ _ (by norm_num), sigma_mul_coprime _ _ (by norm_num),
      sigma_mul_coprime _ _ (by norm_num),
      sigma_prime_pow' _ _ Nat.prime_two, sigma_prime_pow' _ _ Nat.prime_three,
      sigma_prime_pow' _ _ Nat.prime_five, sigma_prime' _ (by norm_num)]
    simp [Finset.sum_range_succ]
  · rw [show (1828800 : ℕ) = 2 ^ 6 * 3 ^ 2 * 5 ^ 2 * 127 by norm_num,
      sigma_mul_coprime _ _ (by norm_num), sigma_mul_coprime _ _ (by norm_num),
      sigma_mul_coprime _ _ (by norm_num),
      sigma_prime_pow' _ _ Nat.prime_two, sigma_prime_pow' _ _ Nat.prime_three,
      sigma_prime_pow' _ _ Nat.prime_five, sigma_prime' _ (by norm_num)]
    simp [Finset.sum_range_succ]

-- N04 sigma_mul_two_primes [algebraic_identity]
theorem sigma_mul_two_primes (K p r : ℕ) (hK : 0 < K) (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r)
    (hpK : ¬ p ∣ K) (hrK : ¬ r ∣ K) :
    σ 1 (K * (p * r)) = σ 1 K * ((p + 1) * (r + 1)) := by
  have hKp : Nat.Coprime K p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpK).symm
  have hKr : Nat.Coprime K r := ((Nat.Prime.coprime_iff_not_dvd hr).mpr hrK).symm
  have hpr' : Nat.Coprime p r := (Nat.coprime_primes hp hr).mpr hpr
  rw [sigma_mul_coprime _ _ (Nat.Coprime.mul_right hKp hKr), sigma_mul_coprime _ _ hpr',
    sigma_prime' _ hp, sigma_prime' _ hr]

-- N05 shifted_product_identity [algebraic_identity]
theorem shifted_product_identity (p1 p2 p3 p4 p5 p6 : ℤ)
    (h22 : 15 * p1 * p2 + 31 * p3 * p4 = 508 * p5 * p6)
    (h23 : 15 * (p1 + p2) + 31 * (p3 + p4) - 508 * (p5 + p6) = 462) :
    15 * (p1 + 1) * (p2 + 1) + 31 * (p3 + 1) * (p4 + 1) = 508 * (p5 + 1) * (p6 + 1) := by
  linear_combination h22 + h23

lemma prime_gt_not_dvd_54000 {p : ℕ} (hp : p.Prime) (h : 127 < p) : ¬ p ∣ 54000 := by
  intro hd
  rw [show (54000 : ℕ) = 2 ^ 4 * 3 ^ 3 * 5 ^ 3 by norm_num] at hd
  rcases (Nat.Prime.dvd_mul hp).mp hd with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2); omega
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2); omega
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h1); omega

lemma prime_gt_not_dvd_111600 {p : ℕ} (hp : p.Prime) (h : 127 < p) : ¬ p ∣ 111600 := by
  intro hd
  rw [show (111600 : ℕ) = 2 ^ 4 * 3 ^ 2 * 5 ^ 2 * 31 by norm_num] at hd
  rcases (Nat.Prime.dvd_mul hp).mp hd with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3); omega
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3); omega
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2); omega
  · have := Nat.le_of_dvd (by norm_num) h1; omega

lemma prime_gt_not_dvd_1828800 {p : ℕ} (hp : p.Prime) (h : 127 < p) : ¬ p ∣ 1828800 := by
  intro hd
  rw [show (1828800 : ℕ) = 2 ^ 6 * 3 ^ 2 * 5 ^ 2 * 127 by norm_num] at hd
  rcases (Nat.Prime.dvd_mul hp).mp hd with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3); omega
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3); omega
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2); omega
  · have := Nat.le_of_dvd (by norm_num) h1; omega

-- N06 friendly_triple_activation [assembly]
theorem friendly_triple_activation (p : Fin 6 → ℕ) (hp : ∀ i, (p i).Prime ∧ 127 < p i)
    (hinj : Function.Injective p)
    (h22 : 15 * (p 0 * p 1) + 31 * (p 2 * p 3) = 508 * (p 4 * p 5))
    (h23 : 15 * (p 0 + p 1) + 31 * (p 2 + p 3) = 508 * (p 4 + p 5) + 462) :
    54000 * (p 0 * p 1) + 111600 * (p 2 * p 3) = 1828800 * (p 4 * p 5) ∧
    σ 1 (54000 * (p 0 * p 1)) + σ 1 (111600 * (p 2 * p 3)) = σ 1 (1828800 * (p 4 * p 5)) := by
  have h01 : p 0 ≠ p 1 := fun h => by have := hinj h; exact absurd this (by decide)
  have h23' : p 2 ≠ p 3 := fun h => by have := hinj h; exact absurd this (by decide)
  have h45 : p 4 ≠ p 5 := fun h => by have := hinj h; exact absurd this (by decide)
  obtain ⟨s1, s2, s3⟩ := sigma_values_triple
  constructor
  · zify at h22 ⊢
    linear_combination 3600 * h22
  · rw [sigma_mul_two_primes 54000 (p 0) (p 1) (by norm_num) (hp 0).1 (hp 1).1 h01
        (prime_gt_not_dvd_54000 (hp 0).1 (hp 0).2) (prime_gt_not_dvd_54000 (hp 1).1 (hp 1).2),
      sigma_mul_two_primes 111600 (p 2) (p 3) (by norm_num) (hp 2).1 (hp 3).1 h23'
        (prime_gt_not_dvd_111600 (hp 2).1 (hp 2).2) (prime_gt_not_dvd_111600 (hp 3).1 (hp 3).2),
      sigma_mul_two_primes 1828800 (p 4) (p 5) (by norm_num) (hp 4).1 (hp 5).1 h45
        (prime_gt_not_dvd_1828800 (hp 4).1 (hp 4).2) (prime_gt_not_dvd_1828800 (hp 5).1 (hp 5).2),
      s1, s2, s3]
    have h22z : (15 : ℤ) * (p 0 * p 1) + 31 * (p 2 * p 3) = 508 * (p 4 * p 5) := by exact_mod_cast h22
    have h23z : (15 : ℤ) * (p 0 + p 1) + 31 * (p 2 + p 3) = 508 * (p 4 + p 5) + 462 := by exact_mod_cast h23
    have key := shifted_product_identity (p 0) (p 1) (p 2) (p 3) (p 4) (p 5)
      (by linear_combination h22z) (by linear_combination h23z)
    zify
    linear_combination 12896 * key

-- N07 core_from_sextuple [case_split]
theorem core_from_sextuple (p : Fin 6 → ℕ) (hp : ∀ i, (p i).Prime ∧ 127 < p i)
    (hinj : Function.Injective p)
    (h22 : 15 * (p 0 * p 1) + 31 * (p 2 * p 3) = 508 * (p 4 * p 5))
    (h23 : 15 * (p 0 + p 1) + 31 * (p 2 + p 3) = 508 * (p 4 + p 5) + 462) :
    Nat.Coprime (15 * (p 0 * p 1)) (31 * (p 2 * p 3)) ∧
    σ 1 (3600 * (15 * (p 0 * p 1))) + σ 1 (3600 * (31 * (p 2 * p 3))) =
      σ 1 (3600 * (15 * (p 0 * p 1) + 31 * (p 2 * p 3))) ∧
    (3600 * (15 * (p 0 * p 1)) * (31 * (p 2 * p 3)) * (15 * (p 0 * p 1) + 31 * (p 2 * p 3))).primeFactors.card ≤ 11 := by
  have hp' : ∀ i, (p i).Prime := fun i => (hp i).1
  have hbig : ∀ i, 127 < p i := fun i => (hp i).2
  have hne : ∀ i j, i ≠ j → p i ≠ p j := fun i j hij h => hij (hinj h)
  have cop_small : ∀ i (m : ℕ), 0 < m → m < 128 → Nat.Coprime m (p i) := fun i m hm0 hm =>
    ((Nat.Prime.coprime_iff_not_dvd (hp' i)).mpr
      (fun hd => by have := Nat.le_of_dvd hm0 hd; have := hbig i; omega)).symm
  have hcop : Nat.Coprime (15 * (p 0 * p 1)) (31 * (p 2 * p 3)) := by
    have c15 : Nat.Coprime 15 (31 * (p 2 * p 3)) :=
      Nat.Coprime.mul_right (by norm_num)
        (Nat.Coprime.mul_right (cop_small 2 15 (by norm_num) (by norm_num))
          (cop_small 3 15 (by norm_num) (by norm_num)))
    have c0 : Nat.Coprime (p 0) (31 * (p 2 * p 3)) :=
      Nat.Coprime.mul_right (cop_small 0 31 (by norm_num) (by norm_num)).symm
        (Nat.Coprime.mul_right ((Nat.coprime_primes (hp' 0) (hp' 2)).mpr (hne 0 2 (by decide)))
          ((Nat.coprime_primes (hp' 0) (hp' 3)).mpr (hne 0 3 (by decide))))
    have c1 : Nat.Coprime (p 1) (31 * (p 2 * p 3)) :=
      Nat.Coprime.mul_right (cop_small 1 31 (by norm_num) (by norm_num)).symm
        (Nat.Coprime.mul_right ((Nat.coprime_primes (hp' 1) (hp' 2)).mpr (hne 1 2 (by decide)))
          ((Nat.coprime_primes (hp' 1) (hp' 3)).mpr (hne 1 3 (by decide))))
    exact Nat.Coprime.symm (Nat.Coprime.mul_right c15.symm (Nat.Coprime.mul_right c0.symm c1.symm))
  obtain ⟨e1, e2⟩ := friendly_triple_activation p hp hinj h22 h23
  refine ⟨hcop, ?_, ?_⟩
  · rw [show 3600 * (15 * (p 0 * p 1)) = 54000 * (p 0 * p 1) by ring,
      show 3600 * (31 * (p 2 * p 3)) = 111600 * (p 2 * p 3) by ring, h22,
      show 3600 * (508 * (p 4 * p 5)) = 1828800 * (p 4 * p 5) by ring]
    exact e2
  · have hN : 3600 * (15 * (p 0 * p 1)) * (31 * (p 2 * p 3)) * (15 * (p 0 * p 1) + 31 * (p 2 * p 3)) =
        2 ^ 6 * 3 ^ 3 * 5 ^ 3 * 31 * 127 * (p 0 * p 1 * p 2 * p 3 * p 4 * p 5) := by rw [h22]; ring
    rw [hN]
    have hsub : (2 ^ 6 * 3 ^ 3 * 5 ^ 3 * 31 * 127 * (p 0 * p 1 * p 2 * p 3 * p 4 * p 5)).primeFactors ⊆
        ({2, 3, 5, 31, 127} : Finset ℕ) ∪ Finset.univ.image p := by
      intro q hq
      rw [Nat.mem_primeFactors] at hq
      obtain ⟨hqp, hqd, -⟩ := hq
      have hpi : ∀ i, q ∣ p i → q = p i := fun i h => (Nat.prime_dvd_prime_iff_eq hqp (hp' i)).mp h
      have hpow : ∀ (a n : ℕ), a.Prime → q ∣ a ^ n → q = a := fun a n ha h =>
        (Nat.prime_dvd_prime_iff_eq hqp ha).mp (hqp.dvd_of_dvd_pow h)
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
        Finset.mem_univ, true_and]
      simp only [Nat.Prime.dvd_mul hqp] at hqd
      rcases hqd with ((((h | h) | h) | h) | h) | (((((h | h) | h) | h) | h) | h)
      · exact Or.inl (Or.inl (hpow 2 6 Nat.prime_two h))
      · exact Or.inl (Or.inr (Or.inl (hpow 3 3 Nat.prime_three h)))
      · exact Or.inl (Or.inr (Or.inr (Or.inl (hpow 5 3 Nat.prime_five h))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hqp (by norm_num)).mp h)))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hqp (by norm_num)).mp h)))))
      · exact Or.inr ⟨0, (hpi 0 h).symm⟩
      · exact Or.inr ⟨1, (hpi 1 h).symm⟩
      · exact Or.inr ⟨2, (hpi 2 h).symm⟩
      · exact Or.inr ⟨3, (hpi 3 h).symm⟩
      · exact Or.inr ⟨4, (hpi 4 h).symm⟩
      · exact Or.inr ⟨5, (hpi 5 h).symm⟩
    calc _ ≤ (({2, 3, 5, 31, 127} : Finset ℕ) ∪ Finset.univ.image p).card := Finset.card_le_card hsub
      _ ≤ ({2, 3, 5, 31, 127} : Finset ℕ).card + (Finset.univ.image p).card := Finset.card_union_le _ _
      _ ≤ 5 + 6 := by
          gcongr
          · rfl
          · exact Finset.card_image_le.trans (by simp)

lemma pair_from_order {a b a' b' : ℕ} (ha : a.Prime) (hb' : b'.Prime) (ha' : a'.Prime)
    (hab' : a' ≠ b') (h : a * b = a' * b') (ho : decide (a < b) = decide (a' < b')) :
    a = a' ∧ b = b' := by
  have hda : a ∣ a' * b' := ⟨b, h.symm⟩
  rcases (Nat.Prime.dvd_mul ha).mp hda with h1 | h1
  · have e := (Nat.prime_dvd_prime_iff_eq ha ha').mp h1
    subst e
    exact ⟨rfl, Nat.eq_of_mul_eq_mul_left ha.pos h⟩
  · have e : a = b' := (Nat.prime_dvd_prime_iff_eq ha hb').mp h1
    have e2 : b = a' := by
      apply Nat.eq_of_mul_eq_mul_left ha.pos
      rw [h, e, mul_comm]
    exfalso
    rw [e, e2] at ho
    rcases Nat.lt_or_gt_of_ne hab' with hlt | hgt
    · simp [hlt, not_lt.mpr hlt.le] at ho
    · simp [hgt, not_lt.mpr hgt.le] at ho

-- N08 core_fiber_le_eight [case_split]
theorem core_fiber_le_eight (Sx : Finset (Fin 6 → ℕ))
    (hS : ∀ p ∈ Sx, (∀ i, (p i).Prime ∧ 127 < p i) ∧ Function.Injective p ∧
      15 * (p 0 * p 1) + 31 * (p 2 * p 3) = 508 * (p 4 * p 5)) :
    Sx.card ≤ 8 * (Sx.image fun p => (15 * (p 0 * p 1), 31 * (p 2 * p 3))).card := by
  classical
  apply Finset.card_le_mul_card_image
  intro b _
  have key : ∀ p ∈ Sx, ∀ p' ∈ Sx,
      (15 * (p 0 * p 1), 31 * (p 2 * p 3)) = (15 * (p' 0 * p' 1), 31 * (p' 2 * p' 3)) →
      (decide (p 0 < p 1), decide (p 2 < p 3), decide (p 4 < p 5)) =
        (decide (p' 0 < p' 1), decide (p' 2 < p' 3), decide (p' 4 < p' 5)) → p = p' := by
    intro p hp p' hp' hcore hord
    obtain ⟨hpr, hinj, h22⟩ := hS p hp
    obtain ⟨hpr', hinj', h22'⟩ := hS p' hp'
    simp only [Prod.mk.injEq] at hcore hord
    obtain ⟨hc1, hc2⟩ := hcore
    obtain ⟨ho1, ho2, ho3⟩ := hord
    have hc3 : 508 * (p 4 * p 5) = 508 * (p' 4 * p' 5) := by omega
    have e01 := pair_from_order (hpr 0).1 (hpr' 1).1 (hpr' 0).1 (hinj'.ne (by decide))
      (Nat.eq_of_mul_eq_mul_left (by norm_num) hc1) ho1
    have e23 := pair_from_order (hpr 2).1 (hpr' 3).1 (hpr' 2).1 (hinj'.ne (by decide))
      (Nat.eq_of_mul_eq_mul_left (by norm_num) hc2) ho2
    have e45 := pair_from_order (hpr 4).1 (hpr' 5).1 (hpr' 4).1 (hinj'.ne (by decide))
      (Nat.eq_of_mul_eq_mul_left (by norm_num) hc3) ho3
    funext i
    fin_cases i
    · exact e01.1
    · exact e01.2
    · exact e23.1
    · exact e23.2
    · exact e45.1
    · exact e45.2
  calc (Sx.filter (fun p => (15 * (p 0 * p 1), 31 * (p 2 * p 3)) = b)).card
      ≤ (Finset.univ : Finset (Bool × Bool × Bool)).card := by
        apply Finset.card_le_card_of_injOn
          (fun p => (decide (p 0 < p 1), decide (p 2 < p 3), decide (p 4 < p 5)))
        · intro p _
          simp
        · intro p hp p' hp' h
          simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hp hp'
          exact key p hp.1 p' hp'.1 (hp.2.trans hp'.2.symm) h
    _ = 8 := by simp

-- N09 multiplier_solution [algebraic_identity]
theorem multiplier_solution (u v g : ℕ) (hg : Nat.Coprime g (3600 * u * v * (u + v)))
    (h : σ 1 (3600 * u) + σ 1 (3600 * v) = σ 1 (3600 * (u + v))) :
    σ 1 (3600 * g * u) + σ 1 (3600 * g * v) = σ 1 (3600 * g * u + 3600 * g * v) := by
  have hgu : Nat.Coprime g (3600 * u) := hg.coprime_dvd_right ⟨v * (u + v), by ring⟩
  have hgv : Nat.Coprime g (3600 * v) := hg.coprime_dvd_right ⟨u * (u + v), by ring⟩
  have hguv : Nat.Coprime g (3600 * (u + v)) := hg.coprime_dvd_right ⟨u * v, by ring⟩
  have e1 : 3600 * g * u = g * (3600 * u) := by ring
  have e2 : 3600 * g * v = g * (3600 * v) := by ring
  have e3 : 3600 * g * u + 3600 * g * v = g * (3600 * (u + v)) := by ring
  rw [e3, e1, e2, sigma_mul_coprime _ _ hgu, sigma_mul_coprime _ _ hgv, sigma_mul_coprime _ _ hguv,
    ← mul_add, h]

-- N10 multiplier_disjoint [algebraic_identity]
theorem multiplier_disjoint (u v u' v' g g' : ℕ) (hu : 0 < u) (hv : 0 < v) (hu' : 0 < u') (hv' : 0 < v')
    (hcop : Nat.Coprime u v) (hcop' : Nat.Coprime u' v') (hg : 0 < g) (hg' : 0 < g')
    (h1 : 3600 * g * u = 3600 * g' * u') (h2 : 3600 * g * v = 3600 * g' * v') :
    g = g' ∧ u = u' ∧ v = v' := by
  have h1' : g * u = g' * u' := by
    rw [mul_assoc, mul_assoc] at h1
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h1
  have h2' : g * v = g' * v' := by
    rw [mul_assoc, mul_assoc] at h2
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2
  have hA : Nat.gcd (g * u) (g * v) = g := by
    rw [Nat.gcd_mul_left, Nat.Coprime.gcd_eq_one hcop, mul_one]
  have hB : Nat.gcd (g' * u') (g' * v') = g' := by
    rw [Nat.gcd_mul_left, Nat.Coprime.gcd_eq_one hcop', mul_one]
  have hgg : g = g' := by rw [← hA, ← hB, h1', h2']
  subst hgg
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hg h1', Nat.eq_of_mul_eq_mul_left hg h2'⟩

/-- Legendre's sieve identity with the crude error term `2^|P| - 1`. -/
lemma legendre_count (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∀ N : ℕ, |(((Finset.Icc 1 N).filter (fun g => ∀ p ∈ P, ¬ p ∣ g)).card : ℝ) -
      N * ∏ p ∈ P, (1 - 1 / (p : ℝ))| ≤ 2 ^ P.card - 1 := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    intro N
    simp
  | insert p P hpP ih =>
    intro N
    have hp : p.Prime := hP p (Finset.mem_insert_self p P)
    have hP' : ∀ p' ∈ P, p'.Prime := fun p' h => hP p' (Finset.mem_insert_of_mem h)
    have ihN := ih hP' N
    have ihq := ih hP' (N / p)
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    -- the splitting of the count
    set A := (Finset.Icc 1 N).filter (fun g => ∀ p' ∈ P, ¬ p' ∣ g) with hA
    have hA1 : A.filter (fun g => ¬ p ∣ g) =
        (Finset.Icc 1 N).filter (fun g => ∀ p' ∈ insert p P, ¬ p' ∣ g) := by
      ext g
      simp only [hA, Finset.mem_filter, Finset.forall_mem_insert]
      tauto
    have hA2 : A.filter (fun g => p ∣ g) =
        ((Finset.Icc 1 (N / p)).filter (fun g => ∀ p' ∈ P, ¬ p' ∣ g)).image (fun h => p * h) := by
      ext g
      simp only [hA, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
      constructor
      · rintro ⟨⟨⟨hg1, hgN⟩, hfree⟩, ⟨h, rfl⟩⟩
        refine ⟨h, ⟨⟨?_, ?_⟩, ?_⟩, rfl⟩
        · rcases Nat.eq_zero_or_pos h with h0 | h0
          · subst h0; simp at hg1
          · exact h0
        · exact (Nat.le_div_iff_mul_le hp.pos).mpr (by linarith [mul_comm p h])
        · intro p' hp' hdvd
          exact hfree p' hp' (Dvd.dvd.mul_left hdvd p)
      · rintro ⟨h, ⟨⟨hh1, hhN⟩, hfree⟩, rfl⟩
        refine ⟨⟨⟨?_, ?_⟩, ?_⟩, Dvd.intro h rfl⟩
        · exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hp.ne_zero (by omega))
        · have := (Nat.le_div_iff_mul_le hp.pos).mp hhN; linarith [mul_comm p h]
        · intro p' hp' hdvd
          rcases (Nat.Prime.dvd_mul (hP' p' hp')).mp hdvd with h1 | h1
          · have := (Nat.prime_dvd_prime_iff_eq (hP' p' hp') hp).mp h1
            subst this
            exact hpP hp'
          · exact hfree p' hp' h1
    have hcardA : A.card = (A.filter (fun g => ¬ p ∣ g)).card + (A.filter (fun g => p ∣ g)).card := by
      rw [add_comm]
      exact (Finset.card_filter_add_card_filter_not _).symm
    rw [hA1, hA2, Finset.card_image_of_injective _ (mul_right_injective₀ hp.ne_zero)] at hcardA
    -- the real estimate
    rw [Finset.prod_insert hpP, Finset.card_insert_of_notMem hpP, pow_succ]
    have hPr0 : 0 ≤ ∏ p' ∈ P, (1 - 1 / (p' : ℝ)) := by
      apply Finset.prod_nonneg
      intro p' hp'
      have : (1 : ℝ) ≤ p' := by exact_mod_cast (hP' p' hp').one_lt.le
      have : 1 / (p' : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact this
      linarith
    have hPr1 : ∏ p' ∈ P, (1 - 1 / (p' : ℝ)) ≤ 1 := by
      apply Finset.prod_le_one₀
      · intro p' hp'
        have : (1 : ℝ) ≤ p' := by exact_mod_cast (hP' p' hp').one_lt.le
        have : 1 / (p' : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact this
        linarith
      · intro p' hp'
        have : (0 : ℝ) < p' := by exact_mod_cast (hP' p' hp').pos
        have : 0 ≤ 1 / (p' : ℝ) := by positivity
        linarith
    have hfl : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p := Nat.cast_div_le
    have hfu : (N : ℝ) / p < ((N / p : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hp0]
      have e : (N : ℝ) = p * ((N / p : ℕ) : ℝ) + ((N % p : ℕ) : ℝ) := by
        exact_mod_cast (Nat.div_add_mod N p).symm
      have hm : ((N % p : ℕ) : ℝ) < p := by exact_mod_cast Nat.mod_lt N hp.pos
      linarith
    have hprod0 : 0 ≤ ((N : ℝ) / p - ((N / p : ℕ) : ℝ)) * ∏ p' ∈ P, (1 - 1 / (p' : ℝ)) :=
      mul_nonneg (by linarith) hPr0
    have hprod1 : ((N : ℝ) / p - ((N / p : ℕ) : ℝ)) * ∏ p' ∈ P, (1 - 1 / (p' : ℝ)) ≤ 1 :=
      mul_le_one₀ (by linarith) hPr0 hPr1
    have hcardA' : (A.card : ℝ) =
        (((Finset.Icc 1 N).filter (fun g => ∀ p' ∈ insert p P, ¬ p' ∣ g)).card : ℝ) +
        (((Finset.Icc 1 (N / p)).filter (fun g => ∀ p' ∈ P, ¬ p' ∣ g)).card : ℝ) := by
      exact_mod_cast hcardA
    have e : (N : ℝ) / p = N * (1 / p) := by ring
    rw [e] at hfl hfu hprod0 hprod1
    rw [abs_le] at ihN ihq ⊢
    have h2k : (0 : ℝ) < 2 ^ P.card := by positivity
    constructor
    · linarith
    · linarith

-- N11 coprime_density [extremal_averaging]
theorem coprime_density : ∃ c6 X0 : ℝ, 0 < c6 ∧ ∀ (n : ℕ) (X : ℝ), n ≠ 0 → n.primeFactors.card ≤ 11 →
    X0 ≤ X → c6 * X ≤ ((Finset.Icc 1 ⌊X⌋₊).filter (fun g => Nat.Coprime g n)).card := by
  refine ⟨1 / 2 ^ 12, 2 ^ 24, by norm_num, ?_⟩
  intro n X hn hω hX
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hP : ∀ p ∈ n.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hfilter : (Finset.Icc 1 ⌊X⌋₊).filter (fun g => Nat.Coprime g n) =
      (Finset.Icc 1 ⌊X⌋₊).filter (fun g => ∀ p ∈ n.primeFactors, ¬ p ∣ g) := by
    apply Finset.filter_congr
    intro g _
    constructor
    · intro hcop p hp hpg
      have hpn := Nat.dvd_of_mem_primeFactors hp
      have h1 := Nat.dvd_gcd hpg hpn
      rw [Nat.Coprime.gcd_eq_one hcop] at h1
      exact (Nat.prime_of_mem_primeFactors hp).one_lt.ne' (Nat.dvd_one.mp h1)
    · intro h
      apply Nat.coprime_of_dvd
      intro k hk hkg hkn
      exact h k (Nat.mem_primeFactors.mpr ⟨hk, hkn, hn⟩) hkg
  rw [hfilter]
  have hleg := legendre_count n.primeFactors hP ⌊X⌋₊
  rw [abs_le] at hleg
  have hPr : (1 / 2 : ℝ) ^ 11 ≤ ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ)) := by
    calc (1 / 2 : ℝ) ^ 11 ≤ (1 / 2) ^ n.primeFactors.card :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hω
      _ = ∏ p ∈ n.primeFactors, (1 / 2 : ℝ) := by rw [Finset.prod_const]
      _ ≤ ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ)) := by
        apply Finset.prod_le_prod₀
        · intros; norm_num
        · intro p hp
          have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
          have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
          linarith
  have h2k : (2 : ℝ) ^ n.primeFactors.card ≤ 2 ^ 11 := pow_le_pow_right₀ (by norm_num) hω
  have hfloor : X - 1 ≤ (⌊X⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one X
    linarith
  have hfloor0 : (0 : ℝ) ≤ ⌊X⌋₊ := by positivity
  have hmul : (X - 1) * (1 / 2 : ℝ) ^ 11 ≤ (⌊X⌋₊ : ℝ) * ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ)) :=
    mul_le_mul hfloor hPr (by positivity) hfloor0
  have hc : (⌊X⌋₊ : ℝ) * ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ)) - (2 ^ n.primeFactors.card - 1) ≤
      (((Finset.Icc 1 ⌊X⌋₊).filter (fun g => ∀ p ∈ n.primeFactors, ¬ p ∣ g)).card : ℝ) := by
    linarith [hleg.1]
  norm_num at hmul hc ⊢
  linarith

-- N12 S_ge_card [assembly]
theorem S_ge_card (x : ℝ) (F : Finset (ℕ × ℕ))
    (hF : ∀ ab ∈ F, 1 ≤ ab.1 ∧ 1 ≤ ab.2 ∧ (ab.1 : ℝ) + ab.2 ≤ x ∧ σ 1 ab.1 + σ 1 ab.2 = σ 1 (ab.1 + ab.2)) :
    (F.card : ℝ) ≤ S x := by
  have hsub : F ⊆ (Finset.Icc 1 ⌊x⌋₊ ×ˢ Finset.Icc 1 ⌊x⌋₊).filter fun (a, b) ↦
      a + b ≤ x ∧ σ 1 a + σ 1 b = σ 1 (a + b) := by
    intro ab hab
    obtain ⟨a, b⟩ := ab
    obtain ⟨h1, h2, h3, h4⟩ := hF (a, b) hab
    simp only at h1 h2 h3 h4
    have ha : (1 : ℝ) ≤ a := by exact_mod_cast h1
    have hb : (1 : ℝ) ≤ b := by exact_mod_cast h2
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨⟨h1, Nat.le_floor (by linarith)⟩, ⟨h2, Nat.le_floor (by linarith)⟩⟩, h3, h4⟩
  exact_mod_cast Finset.card_le_card hsub

-- N13 ruling_plane_identity [algebraic_identity]
theorem ruling_plane_identity (α β γ r s x1 x2 x3 x4 x5 x6 : ℝ)
    (hx1 : x1 = -1 + (1 / 15 - β) * r - γ * s)
    (hx2 : x2 = -1 - 462 * β + (-462 * β ^ 2 - β) * r + (α - 462 * β * γ - γ) * s)
    (hx3 : x3 = -1 - β * r + (1 / 31 - γ) * s)
    (hx4 : x4 = -1 - 462 * γ + (-α - 462 * β * γ - β) * r + (-462 * γ ^ 2 - γ) * s)
    (hx5 : x5 = -1 - β * r - γ * s)
    (hx6 : x6 = (15 * (x1 + x2) + 31 * (x3 + x4) - 508 * x5 - 462) / 508) :
    15 * x1 * x2 + 31 * x3 * x4 = 508 * x5 * x6 ∧
    15 * (x1 + x2) + 31 * (x3 + x4) - 508 * (x5 + x6) = 462 ∧
    508 * x6 = -(6930 * β + 14322 * γ + 46) +
      (-31 * α - 6930 * β ^ 2 - 14322 * β * γ + 416 * β + 1) * r +
      (15 * α - 6930 * β * γ - 14322 * γ ^ 2 + 416 * γ + 1) * s := by
  subst hx1 hx2 hx3 hx4 hx5 hx6
  refine ⟨by ring, by ring, by ring⟩

-- N14 determinant_table [algebraic_identity]
theorem determinant_table (α β γ a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 : ℝ)
    (ha1 : a1 = 1 / 15 - β) (hb1 : b1 = -γ)
    (ha2 : a2 = -462 * β ^ 2 - β) (hb2 : b2 = α - 462 * β * γ - γ)
    (ha3 : a3 = -β) (hb3 : b3 = 1 / 31 - γ)
    (ha4 : a4 = -α - 462 * β * γ - β) (hb4 : b4 = -462 * γ ^ 2 - γ)
    (ha5 : a5 = -β) (hb5 : b5 = -γ)
    (ha6 : a6 = (15 * (a1 + a2) + 31 * (a3 + a4) - 508 * a5) / 508)
    (hb6 : b6 = (15 * (b1 + b2) + 31 * (b3 + b4) - 508 * b5) / 508) :
    a1 * b2 - b1 * a2 = -(15 * α * β - α + 462 * β * γ + γ) / 15 ∧
    a1 * b3 - b1 * a3 = -(15 * β + 31 * γ - 1) / 465 ∧
    a1 * b4 - b1 * a4 = -γ * (15 * α + 462 * γ + 1) / 15 ∧
    a1 * b5 - b1 * a5 = -γ / 15 ∧
    a1 * b6 - b1 * a6 = -(15 * α + 462 * γ + 1) * (15 * β + 31 * γ - 1) / 7620 ∧
    a2 * b3 - b2 * a3 = β * (31 * α - 462 * β - 1) / 31 ∧
    a2 * b4 - b2 * a4 = α * (α + β - γ) ∧
    a2 * b5 - b2 * a5 = α * β ∧
    a2 * b6 - b2 * a6 = (α + β - γ) * (31 * α - 462 * β - 1) / 508 ∧
    a3 * b4 - b3 * a4 = -(31 * α * γ - α - 462 * β * γ - β) / 31 ∧
    a3 * b5 - b3 * a5 = β / 31 ∧
    a3 * b6 - b3 * a6 = -(31 * α - 462 * β - 1) * (15 * β + 31 * γ - 1) / 15748 ∧
    a4 * b5 - b4 * a5 = α * γ ∧
    a4 * b6 - b4 * a6 = -(α + β - γ) * (15 * α + 462 * γ + 1) / 508 ∧
    a5 * b6 - b5 * a6 = -(15 * α * β + 31 * α * γ + β - γ) / 508 := by
  subst ha1 hb1 ha2 hb2 ha3 hb3 ha4 hb4 ha5 hb5 ha6 hb6
  refine ⟨by ring, by ring, by ring, by ring, by ring, by ring, by ring, by ring, by ring, by ring,
    by ring, by ring, by ring, by ring, by ring⟩

-- N15 finite_complexity_real [case_split]
theorem finite_complexity_real (Z α β γ a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 : ℝ)
    (hZ : 100 ≤ Z) (hα1 : Z ^ 2 ≤ α) (hα2 : α ≤ 2 * Z ^ 2) (hβ1 : Z ≤ β) (hβ2 : β ≤ 2 * Z)
    (hγ1 : Z ≤ γ) (hγ2 : γ ≤ 2 * Z)
    (ha1 : a1 = 1 / 15 - β) (hb1 : b1 = -γ)
    (ha2 : a2 = -462 * β ^ 2 - β) (hb2 : b2 = α - 462 * β * γ - γ)
    (ha3 : a3 = -β) (hb3 : b3 = 1 / 31 - γ)
    (ha4 : a4 = -α - 462 * β * γ - β) (hb4 : b4 = -462 * γ ^ 2 - γ)
    (ha5 : a5 = -β) (hb5 : b5 = -γ)
    (ha6 : a6 = (15 * (a1 + a2) + 31 * (a3 + a4) - 508 * a5) / 508)
    (hb6 : b6 = (15 * (b1 + b2) + 31 * (b3 + b4) - 508 * b5) / 508) :
    a1 * b2 - b1 * a2 ≠ 0 ∧
    a1 * b3 - b1 * a3 ≠ 0 ∧
    a1 * b4 - b1 * a4 ≠ 0 ∧
    a1 * b5 - b1 * a5 ≠ 0 ∧
    a1 * b6 - b1 * a6 ≠ 0 ∧
    a2 * b3 - b2 * a3 ≠ 0 ∧
    a2 * b4 - b2 * a4 ≠ 0 ∧
    a2 * b5 - b2 * a5 ≠ 0 ∧
    a2 * b6 - b2 * a6 ≠ 0 ∧
    a3 * b4 - b3 * a4 ≠ 0 ∧
    a3 * b5 - b3 * a5 ≠ 0 ∧
    a3 * b6 - b3 * a6 ≠ 0 ∧
    a4 * b5 - b4 * a5 ≠ 0 ∧
    a4 * b6 - b4 * a6 ≠ 0 ∧
    a5 * b6 - b5 * a6 ≠ 0 := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15⟩ :=
    determinant_table α β γ a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 ha1 hb1 ha2 hb2 ha3 hb3 ha4 hb4
      ha5 hb5 ha6 hb6
  rw [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15]
  clear t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 ha1 hb1 ha2 hb2 ha3 hb3 ha4 hb4 ha5 hb5
    ha6 hb6
  have hZ0 : 0 < Z := by linarith
  have hZZ : 100 * Z ≤ Z * Z := mul_le_mul_of_nonneg_right hZ hZ0.le
  have hZ2 : 100 * Z ≤ Z ^ 2 := by rw [sq]; exact hZZ
  have hα0 : 0 < α := by linarith
  have hβ0 : 0 < β := by linarith
  have hγ0 : 0 < γ := by linarith
  have hαZ : 100 * Z ≤ α := by linarith
  have hZ3 : Z ^ 2 * 100 ≤ Z ^ 2 * Z := mul_le_mul_of_nonneg_left hZ (by positivity)
  have hαγ : Z ^ 2 * Z ≤ α * γ := mul_le_mul hα1 hγ1 hZ0.le hα0.le
  have hβγ : β * γ ≤ 2 * Z * (2 * Z) := mul_le_mul hβ2 hγ2 hγ0.le (by linarith)
  have hαβ : Z ^ 2 * Z ≤ α * β := mul_le_mul hα1 hβ1 hZ0.le hα0.le
  have hZZ2 : Z * Z = Z ^ 2 := by ring
  have P1 : 0 < 15 * α * β - α + 462 * β * γ + γ := by
    have h1 := mul_pos hα0 (show 0 < 15 * β - 1 by linarith)
    have h2 := mul_pos hγ0 (show 0 < 462 * β + 1 by linarith)
    nlinarith
  have P2 : 0 < 15 * β + 31 * γ - 1 := by linarith
  have P3 : 0 < 15 * α + 462 * γ + 1 := by linarith
  have P4 : 0 < 31 * α - 462 * β - 1 := by linarith
  have P5 : 0 < α + β - γ := by linarith
  have P6 : 0 < 31 * α * γ - α - 462 * β * γ - β := by nlinarith
  have P7 : 0 < 15 * α * β + 31 * α * γ + β - γ := by nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact div_ne_zero (neg_ne_zero.mpr P1.ne') (by norm_num)
  · exact div_ne_zero (neg_ne_zero.mpr P2.ne') (by norm_num)
  · exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr hγ0.ne') P3.ne') (by norm_num)
  · exact div_ne_zero (neg_ne_zero.mpr hγ0.ne') (by norm_num)
  · exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr P3.ne') P2.ne') (by norm_num)
  · exact div_ne_zero (mul_ne_zero hβ0.ne' P4.ne') (by norm_num)
  · exact mul_ne_zero hα0.ne' P5.ne'
  · exact mul_ne_zero hα0.ne' hβ0.ne'
  · exact div_ne_zero (mul_ne_zero P5.ne' P4.ne') (by norm_num)
  · exact div_ne_zero (neg_ne_zero.mpr P6.ne') (by norm_num)
  · exact div_ne_zero hβ0.ne' (by norm_num)
  · exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr P4.ne') P2.ne') (by norm_num)
  · exact mul_ne_zero hα0.ne' hγ0.ne'
  · exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr P5.ne') P3.ne') (by norm_num)
  · exact div_ne_zero (neg_ne_zero.mpr P7.ne') (by norm_num)

-- N16 archimedean_bounds [extremal_averaging]
set_option maxHeartbeats 400000 in
theorem archimedean_bounds : ∃ c C : ℝ, 0 < c ∧ c < C ∧
    ∀ (Z T α β γ r s x1 x2 x3 x4 x5 x6 : ℝ),
      100 ≤ Z → 10 ≤ T → Z ^ 2 ≤ α → α ≤ 2 * Z ^ 2 → Z ≤ β → β ≤ 2 * Z → Z ≤ γ → γ ≤ 2 * Z →
      -2 * T ≤ r → r ≤ -T → |s| ≤ 1 / 100000 * |r| →
      x1 = -1 + (1 / 15 - β) * r - γ * s →
      x2 = -1 - 462 * β + (-462 * β ^ 2 - β) * r + (α - 462 * β * γ - γ) * s →
      x3 = -1 - β * r + (1 / 31 - γ) * s →
      x4 = -1 - 462 * γ + (-α - 462 * β * γ - β) * r + (-462 * γ ^ 2 - γ) * s →
      x5 = -1 - β * r - γ * s →
      x6 = (15 * (x1 + x2) + 31 * (x3 + x4) - 508 * x5 - 462) / 508 →
      (c * Z * T ≤ x1 ∧ x1 ≤ C * Z * T ∧ c * Z * T ≤ x3 ∧ x3 ≤ C * Z * T ∧
       c * Z * T ≤ x5 ∧ x5 ≤ C * Z * T ∧
       c * Z ^ 2 * T ≤ x2 ∧ x2 ≤ C * Z ^ 2 * T ∧ c * Z ^ 2 * T ≤ x4 ∧ x4 ≤ C * Z ^ 2 * T ∧
       c * Z ^ 2 * T ≤ x6 ∧ x6 ≤ C * Z ^ 2 * T) := by
  refine ⟨1 / 2, 4000, by norm_num, by norm_num, ?_⟩
  intro Z T α β γ r s x1 x2 x3 x4 x5 x6 hZ hT hα1 hα2 hβ1 hβ2 hγ1 hγ2 hr1 hr2 hs hx1 hx2 hx3 hx4 hx5 hx6
  obtain ⟨u, rfl⟩ : ∃ u, r = -u := ⟨-r, by ring⟩
  have hu1 : T ≤ u := by linarith
  have hu2 : u ≤ 2 * T := by linarith
  have hu0 : 0 < u := by linarith
  rw [abs_neg, abs_of_pos hu0] at hs
  obtain ⟨hs1, hs2⟩ := abs_le.mp hs
  have hZ0 : 0 < Z := by linarith
  have hT0 : 0 < T := by linarith
  have hα0 : 0 ≤ α := by nlinarith
  have hβ0 : 0 ≤ β := by linarith
  have hγ0 : 0 ≤ γ := by linarith
  have hZT : 1000 ≤ Z * T := by nlinarith
  have hZZT : 10 * Z ≤ Z * T := by nlinarith
  have hTZT : 100 * T ≤ Z * T := mul_le_mul_of_nonneg_right hZ hT0.le
  have hZ2T : 100 * (Z * T) ≤ Z ^ 2 * T := by nlinarith
  -- degree-2 products with u
  have hβu1 : Z * T ≤ β * u := mul_le_mul hβ1 hu1 hT0.le hβ0
  have hβu2 : β * u ≤ 2 * Z * (2 * T) := mul_le_mul hβ2 hu2 hu0.le (by linarith)
  have hγu1 : Z * T ≤ γ * u := mul_le_mul hγ1 hu1 hT0.le hγ0
  have hγu2 : γ * u ≤ 2 * Z * (2 * T) := mul_le_mul hγ2 hu2 hu0.le (by linarith)
  have hαu1 : Z ^ 2 * T ≤ α * u := mul_le_mul hα1 hu1 hT0.le hα0
  have hαu2 : α * u ≤ 2 * Z ^ 2 * (2 * T) := mul_le_mul hα2 hu2 hu0.le (by linarith)
  -- degree-3 products with u
  have hβsq : β ^ 2 ≤ (2 * Z) ^ 2 := pow_le_pow_left₀ hβ0 hβ2 2
  have hβsq' : Z ^ 2 ≤ β ^ 2 := pow_le_pow_left₀ hZ0.le hβ1 2
  have hγsq : γ ^ 2 ≤ (2 * Z) ^ 2 := pow_le_pow_left₀ hγ0 hγ2 2
  have hγsq' : Z ^ 2 ≤ γ ^ 2 := pow_le_pow_left₀ hZ0.le hγ1 2
  have hβγ1 : Z * Z ≤ β * γ := mul_le_mul hβ1 hγ1 hZ0.le hβ0
  have hβγ2 : β * γ ≤ 2 * Z * (2 * Z) := mul_le_mul hβ2 hγ2 hγ0 (by linarith)
  have hβ2u1 : Z ^ 2 * T ≤ β ^ 2 * u := mul_le_mul hβsq' hu1 hT0.le (by positivity)
  have hβ2u2 : β ^ 2 * u ≤ (2 * Z) ^ 2 * (2 * T) := mul_le_mul hβsq hu2 hu0.le (by positivity)
  have hγ2u1 : Z ^ 2 * T ≤ γ ^ 2 * u := mul_le_mul hγsq' hu1 hT0.le (by positivity)
  have hγ2u2 : γ ^ 2 * u ≤ (2 * Z) ^ 2 * (2 * T) := mul_le_mul hγsq hu2 hu0.le (by positivity)
  have hβγu1 : Z * Z * T ≤ β * γ * u := mul_le_mul hβγ1 hu1 hT0.le (by positivity)
  have hβγu2 : β * γ * u ≤ 2 * Z * (2 * Z) * (2 * T) := mul_le_mul hβγ2 hu2 hu0.le (by positivity)
  -- products with s
  have hγs1 : γ * (-(1 / 100000 * u)) ≤ γ * s := mul_le_mul_of_nonneg_left hs1 hγ0
  have hγs2 : γ * s ≤ γ * (1 / 100000 * u) := mul_le_mul_of_nonneg_left hs2 hγ0
  have hαs1 : α * (-(1 / 100000 * u)) ≤ α * s := mul_le_mul_of_nonneg_left hs1 hα0
  have hαs2 : α * s ≤ α * (1 / 100000 * u) := mul_le_mul_of_nonneg_left hs2 hα0
  have hβγs1 : β * γ * (-(1 / 100000 * u)) ≤ β * γ * s := mul_le_mul_of_nonneg_left hs1 (by positivity)
  have hβγs2 : β * γ * s ≤ β * γ * (1 / 100000 * u) := mul_le_mul_of_nonneg_left hs2 (by positivity)
  have hγ2s1 : γ ^ 2 * (-(1 / 100000 * u)) ≤ γ ^ 2 * s := mul_le_mul_of_nonneg_left hs1 (by positivity)
  have hγ2s2 : γ ^ 2 * s ≤ γ ^ 2 * (1 / 100000 * u) := mul_le_mul_of_nonneg_left hs2 (by positivity)
  subst hx1 hx2 hx3 hx4 hx5 hx6
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

-- N17 zero_form_criteria [algebraic_identity]
theorem zero_form_criteria {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (h7 : (7 : F) ≠ 0) (h11 : (11 : F) ≠ 0) (α β γ : F) :
    ((-1 - 462 * β = 0 ∧ -462 * β ^ 2 - β = 0 ∧ α - 462 * β * γ - γ = 0) ↔ (α = 0 ∧ 462 * β + 1 = 0)) ∧
    ((-1 - 462 * γ = 0 ∧ -α - 462 * β * γ - β = 0 ∧ -462 * γ ^ 2 - γ = 0) ↔ (α = 0 ∧ 462 * γ + 1 = 0)) ∧
    ((6930 * β + 14322 * γ + 46 = 0 ∧
      -31 * α - 6930 * β ^ 2 - 14322 * β * γ + 416 * β + 1 = 0 ∧
      15 * α - 6930 * β * γ - 14322 * γ ^ 2 + 416 * γ + 1 = 0) ↔
     (31 * α - 462 * β - 1 = 0 ∧ 15 * α + 462 * γ + 1 = 0)) := by
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · obtain ⟨h1, h2, h3⟩ := h
    exact ⟨by linear_combination h3 - γ * h1, by linear_combination -h1⟩
  · obtain ⟨h1, h2⟩ := h
    exact ⟨by linear_combination -h2, by linear_combination -β * h2, by linear_combination h1 - γ * h2⟩
  · obtain ⟨h1, h2, h3⟩ := h
    exact ⟨by linear_combination -h2 + β * h1, by linear_combination -h1⟩
  · obtain ⟨h1, h2⟩ := h
    exact ⟨by linear_combination -h2, by linear_combination -h1 - β * h2, by linear_combination -γ * h2⟩
  · obtain ⟨h1, h2, h3⟩ := h
    exact ⟨by linear_combination -h2 - β * h1, by linear_combination h3 + γ * h1⟩
  · obtain ⟨hu, hv⟩ := h
    exact ⟨by linear_combination -15 * hu + 31 * hv,
      by linear_combination (-1 + 15 * β) * hu - 31 * β * hv,
      by linear_combination 15 * γ * hu + (1 - 31 * γ) * hv⟩

-- N18 integral_lift [algebraic_identity]
theorem integral_lift (OnPl : ℤ → ℤ → ℤ → ℤ → (Fin 6 → ℤ) → Prop)
    (hOnPl : ∀ q A B C (x : Fin 6 → ℤ), OnPl q A B C x ↔
      (q * (x 1 - x 4) = 31 * A * (x 2 - x 4) + 462 * B * x 4 ∧
       q * (x 3 - x 4) = -15 * A * (x 0 - x 4) + 462 * C * x 4 ∧
       q * (x 4 + 1) = -(15 * B * (x 0 - x 4) + 31 * C * (x 2 - x 4)) ∧
       508 * x 5 = 15 * (x 0 + x 1) + 31 * (x 2 + x 3) - 508 * x 4 - 462))
    (q A B C : ℤ) (x : Fin 6 → ℤ) (hq : q ≠ 0) (hx : OnPl q A B C x) :
    ∀ α β γ r s : ℝ, α = A / q → β = B / q → γ = C / q →
      r = 15 * ((x 0 : ℝ) - x 4) → s = 31 * ((x 2 : ℝ) - x 4) →
      (x 0 : ℝ) = -1 + (1 / 15 - β) * r - γ * s ∧
      (x 1 : ℝ) = -1 - 462 * β + (-462 * β ^ 2 - β) * r + (α - 462 * β * γ - γ) * s ∧
      (x 2 : ℝ) = -1 - β * r + (1 / 31 - γ) * s ∧
      (x 3 : ℝ) = -1 - 462 * γ + (-α - 462 * β * γ - β) * r + (-462 * γ ^ 2 - γ) * s ∧
      (x 4 : ℝ) = -1 - β * r - γ * s ∧
      (x 5 : ℝ) = (15 * ((x 0 : ℝ) + x 1) + 31 * ((x 2 : ℝ) + x 3) - 508 * (x 4 : ℝ) - 462) / 508 := by
  intro α β γ r s hα hβ hγ hr hs
  rw [hOnPl] at hx
  obtain ⟨e1, e2, e3, e4⟩ := hx
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have e1' : (q : ℝ) * (x 1 - x 4) = 31 * A * (x 2 - x 4) + 462 * B * x 4 := by exact_mod_cast e1
  have e2' : (q : ℝ) * (x 3 - x 4) = -15 * A * (x 0 - x 4) + 462 * C * x 4 := by exact_mod_cast e2
  have e3' : (q : ℝ) * (x 4 + 1) = -(15 * B * (x 0 - x 4) + 31 * C * (x 2 - x 4)) := by
    exact_mod_cast e3
  have e4' : (508 : ℝ) * x 5 = 15 * (x 0 + x 1) + 31 * (x 2 + x 3) - 508 * x 4 - 462 := by
    exact_mod_cast e4
  have hA : (A : ℝ) = α * q := by rw [hα]; field_simp
  have hB : (B : ℝ) = β * q := by rw [hβ]; field_simp
  have hC : (C : ℝ) = γ * q := by rw [hγ]; field_simp
  rw [hA] at e1' e2'
  rw [hB] at e1' e3'
  rw [hC] at e2' e3'
  have f1 : (x 1 : ℝ) - x 4 = 31 * α * (x 2 - x 4) + 462 * β * x 4 :=
    mul_left_cancel₀ hq' (by linear_combination e1')
  have f2 : (x 3 : ℝ) - x 4 = -15 * α * (x 0 - x 4) + 462 * γ * x 4 :=
    mul_left_cancel₀ hq' (by linear_combination e2')
  have f3 : (x 4 : ℝ) + 1 = -(15 * β * (x 0 - x 4) + 31 * γ * (x 2 - x 4)) :=
    mul_left_cancel₀ hq' (by linear_combination e3')
  subst hr hs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination f3
  · linear_combination f1 + (1 + 462 * β) * f3
  · linear_combination f3
  · linear_combination f2 + (1 + 462 * γ) * f3
  · linear_combination f3
  · linear_combination e4' / 508

-- N19 onPlane_equations [algebraic_identity]
theorem onPlane_equations (OnPl : ℤ → ℤ → ℤ → ℤ → (Fin 6 → ℤ) → Prop)
    (hOnPl : ∀ q A B C (x : Fin 6 → ℤ), OnPl q A B C x ↔
      (q * (x 1 - x 4) = 31 * A * (x 2 - x 4) + 462 * B * x 4 ∧
       q * (x 3 - x 4) = -15 * A * (x 0 - x 4) + 462 * C * x 4 ∧
       q * (x 4 + 1) = -(15 * B * (x 0 - x 4) + 31 * C * (x 2 - x 4)) ∧
       508 * x 5 = 15 * (x 0 + x 1) + 31 * (x 2 + x 3) - 508 * x 4 - 462))
    (q A B C : ℤ) (x : Fin 6 → ℤ) (hq : q ≠ 0) (hx : OnPl q A B C x) :
    15 * x 0 * x 1 + 31 * x 2 * x 3 = 508 * x 4 * x 5 ∧
    15 * (x 0 + x 1) + 31 * (x 2 + x 3) - 508 * (x 4 + x 5) = 462 := by
  have lift := integral_lift OnPl hOnPl q A B C x hq hx (A / q) (B / q) (C / q)
    (15 * ((x 0 : ℝ) - x 4)) (31 * ((x 2 : ℝ) - x 4)) rfl rfl rfl rfl rfl
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := lift
  obtain ⟨k1, k2, -⟩ := ruling_plane_identity (A / q) (B / q) (C / q) (15 * ((x 0 : ℝ) - x 4))
    (31 * ((x 2 : ℝ) - x 4)) (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) h0 h1 h2 h3 h4 h5
  constructor
  · exact_mod_cast k1
  · exact_mod_cast k2

-- N20 good_coprime [case_split]
theorem good_coprime (Good : ℝ → ℕ → ℤ → ℤ → ℤ → Prop)
    (hGood : ∀ Z q A B C, Good Z q A B C ↔
      ((4619990760 : ℤ) ∣ A ∧ (4619990760 : ℤ) ∣ B ∧ (4619990760 : ℤ) ∣ C ∧
       (q : ℝ) * Z ^ 2 ≤ A ∧ (A : ℝ) < 2 * q * Z ^ 2 ∧
       (q : ℝ) * Z ≤ B ∧ (B : ℝ) < 2 * q * Z ∧
       (q : ℝ) * Z ≤ C ∧ (C : ℝ) < 2 * q * Z ∧
       (∀ p : ℕ, p.Prime → p ∣ q →
         ¬ (p : ℤ) ∣ A * B * C * (462 * C + 15 * A) * (31 * A - 462 * B) * (15 * B + 31 * C)) ∧
       (∀ p : ℕ, p.Prime → ¬ p ∣ 4619990760 * q →
         ¬ (((p : ℤ) ∣ A ∧ (p : ℤ) ∣ 462 * B + q) ∨ ((p : ℤ) ∣ A ∧ (p : ℤ) ∣ 462 * C + q) ∨
           ((p : ℤ) ∣ 31 * A - 462 * B - q ∧ (p : ℤ) ∣ 15 * A + 462 * C + q)))))
    (Z : ℝ) (q : ℕ) (A B C : ℤ) (hG : Good Z q A B C) :
    IsCoprime A (q : ℤ) ∧ IsCoprime B (q : ℤ) ∧ IsCoprime C (q : ℤ) ∧ IsCoprime (A * B * C) (q : ℤ) := by
  rw [hGood] at hG
  obtain ⟨-, -, -, -, -, -, -, -, -, hdiv, -⟩ := hG
  have gen : ∀ X : ℤ, X ∣ A * B * C * (462 * C + 15 * A) * (31 * A - 462 * B) * (15 * B + 31 * C) →
      IsCoprime X (q : ℤ) := by
    intro X hX
    rw [Int.isCoprime_iff_gcd_eq_one]
    by_contra hne
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    have h1 : (p : ℤ) ∣ X := (Int.natCast_dvd_natCast.mpr hpd).trans (Int.gcd_dvd_left X q)
    have h2 : (p : ℤ) ∣ (q : ℤ) := (Int.natCast_dvd_natCast.mpr hpd).trans (Int.gcd_dvd_right X q)
    exact hdiv p hp (Int.natCast_dvd_natCast.mp h2) (h1.trans hX)
  have hA := gen A ⟨B * C * (462 * C + 15 * A) * (31 * A - 462 * B) * (15 * B + 31 * C), by ring⟩
  have hB := gen B ⟨A * C * (462 * C + 15 * A) * (31 * A - 462 * B) * (15 * B + 31 * C), by ring⟩
  have hC := gen C ⟨A * B * (462 * C + 15 * A) * (31 * A - 462 * B) * (15 * B + 31 * C), by ring⟩
  exact ⟨hA, hB, hC, IsCoprime.mul_left (IsCoprime.mul_left hA hB) hC⟩

-- N21 helper
lemma lw_unit (p : ℕ) (hp : p.Prime) (hpW : p ∣ 4619990760) (x c D t : ℤ) (hx : x = c + D * t)
    (hD : (4619990760 : ℤ) ∣ D ^ 3) (hc : IsCoprime c 4619990760) : ¬ (p : ℤ) ∣ x := by
  intro h
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpW' : (p : ℤ) ∣ 4619990760 := by exact_mod_cast hpW
  have hpD : (p : ℤ) ∣ D := hpZ.dvd_of_dvd_pow (hpW'.trans hD)
  have hpc : (p : ℤ) ∣ c := by
    have h2 := dvd_sub h (dvd_mul_of_dvd_left hpD t)
    rw [hx] at h2
    simpa using h2
  exact hpZ.not_unit (hc.isUnit_of_dvd' hpc hpW')

-- N21 local_witness [algebraic_identity]
theorem local_witness (OnPl : ℤ → ℤ → ℤ → ℤ → (Fin 6 → ℤ) → Prop)
    (hOnPl : ∀ q A B C (x : Fin 6 → ℤ), OnPl q A B C x ↔
      (q * (x 1 - x 4) = 31 * A * (x 2 - x 4) + 462 * B * x 4 ∧
       q * (x 3 - x 4) = -15 * A * (x 0 - x 4) + 462 * C * x 4 ∧
       q * (x 4 + 1) = -(15 * B * (x 0 - x 4) + 31 * C * (x 2 - x 4)) ∧
       508 * x 5 = 15 * (x 0 + x 1) + 31 * (x 2 + x 3) - 508 * x 4 - 462))
    (q : ℕ) (A B C : ℤ) (hq1 : 1 ≤ q) (hqW : q % 4619990760 = 1) (hA : (4619990760 : ℤ) ∣ A) (hB : (4619990760 : ℤ) ∣ B) (hC : (4619990760 : ℤ) ∣ C)
    (hCq : IsCoprime C (q : ℤ)) :
    ∃ x : Fin 6 → ℤ, OnPl q A B C x ∧ ∀ p : ℕ, p.Prime → p ∣ 4619990760 → ∀ i, ¬ (p : ℤ) ∣ x i := by
  -- Route: x0 = x4 = -q n, x2 = x4 + q v, v = 3918 + W k with q n = 1 + 31 C v (k from IsCoprime C q);
  -- every coordinate is then ≡ -1, 3917 or (for x5) 239 modulo W (resp. W/508), all units mod rad W.
  obtain ⟨a, rfl⟩ := hA
  obtain ⟨b, rfl⟩ := hB
  obtain ⟨c, rfl⟩ := hC
  have hqr : (q : ℤ) = 4619990760 * ((q / 4619990760 : ℕ) : ℤ) + 1 := by
    have h := Nat.div_add_mod q 4619990760
    rw [hqW] at h
    exact_mod_cast h.symm
  generalize ((q / 4619990760 : ℕ) : ℤ) = r at hqr
  generalize hQ : (q : ℤ) = Q at hqr hCq ⊢
  subst hqr
  have hWQ : IsCoprime (4619990760 : ℤ) (4619990760 * r + 1) := ⟨-r, 1, by ring⟩
  have h31 : IsCoprime (31 : ℤ) (4619990760 * r + 1) := ⟨-149031960 * r, 1, by ring⟩
  have hcop : IsCoprime (31 * (4619990760 * c) * 4619990760) (4619990760 * r + 1) :=
    (h31.mul_left hCq).mul_left hWQ
  obtain ⟨μ, ν, hμν⟩ := hcop
  have hqn0 : (4619990760 * r + 1) * ((1 + 31 * (4619990760 * c) * 3918) * ν) =
      1 + 31 * (4619990760 * c) * (3918 + 4619990760 * (-(1 + 31 * (4619990760 * c) * 3918) * μ)) := by
    linear_combination (1 + 31 * (4619990760 * c) * 3918) * hμν
  obtain ⟨k, n, hqn⟩ : ∃ k n : ℤ, (4619990760 * r + 1) * n = 1 + 31 * (4619990760 * c) * (3918 + 4619990760 * k) :=
    ⟨_, _, hqn0⟩
  obtain ⟨s, rfl⟩ : ∃ s : ℤ, n = 1 + 4619990760 * s :=
    ⟨31 * c * (3918 + 4619990760 * k) - r * n, by linear_combination hqn⟩
  have hW3 : (4619990760 : ℤ) ∣ 4619990760 ^ 3 := dvd_pow_self _ (by norm_num)
  have hD3 : (4619990760 : ℤ) ∣ 9094470 ^ 3 := by norm_num
  have cm1 : IsCoprime (-1 : ℤ) 4619990760 := Int.isCoprime_iff_gcd_eq_one.mpr (by norm_num)
  have c2 : IsCoprime (3917 : ℤ) 4619990760 := Int.isCoprime_iff_gcd_eq_one.mpr (by norm_num)
  have c5 : IsCoprime (239 : ℤ) 4619990760 := Int.isCoprime_iff_gcd_eq_one.mpr (by norm_num)
  refine ⟨![-(4619990760 * r + 1) * (1 + 4619990760 * s),
    -(4619990760 * r + 1) * (1 + 4619990760 * s) + 31 * (4619990760 * a) * (3918 + 4619990760 * k) -
      462 * (4619990760 * b) * (1 + 4619990760 * s),
    -(4619990760 * r + 1) * (1 + 4619990760 * s) + (4619990760 * r + 1) * (3918 + 4619990760 * k),
    -(4619990760 * r + 1) * (1 + 4619990760 * s) - 462 * (4619990760 * c) * (1 + 4619990760 * s),
    -(4619990760 * r + 1) * (1 + 4619990760 * s),
    239 + 9094470 * (416 * (r + s + 4619990760 * r * s) + 465 * a * (3918 + 4619990760 * k) -
      6930 * b * (1 + 4619990760 * s) + 31 * k + 31 * r * (3918 + 4619990760 * k) -
      14322 * c * (1 + 4619990760 * s))], ?_, ?_⟩
  · rw [hOnPl]
    simp only [Matrix.cons_val, Fin.isValue]
    refine ⟨by ring, by ring, by linear_combination (-(4619990760 * r + 1)) * hqn, by ring⟩
  · intro p hp hpW i
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
    · exact lw_unit p hp hpW _ (-1) 4619990760 (-(r + s + 4619990760 * r * s)) (by ring) hW3 cm1
    · exact lw_unit p hp hpW _ (-1) 4619990760
        (-(r + s + 4619990760 * r * s) + 31 * a * (3918 + 4619990760 * k) - 462 * b * (1 + 4619990760 * s))
        (by ring) hW3 cm1
    · exact lw_unit p hp hpW _ 3917 4619990760
        (-(r + s + 4619990760 * r * s) + k + 3918 * r + 4619990760 * r * k) (by ring) hW3 c2
    · exact lw_unit p hp hpW _ (-1) 4619990760
        (-(r + s + 4619990760 * r * s) - 462 * c * (1 + 4619990760 * s)) (by ring) hW3 cm1
    · exact lw_unit p hp hpW _ (-1) 4619990760 (-(r + s + 4619990760 * r * s)) (by ring) hW3 cm1
    · exact lw_unit p hp hpW _ 239 9094470 _ rfl hD3 c5

-- N22 projected_index [two_structure_coupling]
theorem projected_index (OnPl : ℤ → ℤ → ℤ → ℤ → (Fin 6 → ℤ) → Prop)
    (hOnPl : ∀ q A B C (x : Fin 6 → ℤ), OnPl q A B C x ↔
      (q * (x 1 - x 4) = 31 * A * (x 2 - x 4) + 462 * B * x 4 ∧
       q * (x 3 - x 4) = -15 * A * (x 0 - x 4) + 462 * C * x 4 ∧
       q * (x 4 + 1) = -(15 * B * (x 0 - x 4) + 31 * C * (x 2 - x 4)) ∧
       508 * x 5 = 15 * (x 0 + x 1) + 31 * (x 2 + x 3) - 508 * x 4 - 462))
    (q : ℕ) (A B C : ℤ) (hq1 : 1 ≤ q) (hqW : q % 4619990760 = 1) (hA : (4619990760 : ℤ) ∣ A) (hB : (4619990760 : ℤ) ∣ B) (hC : (4619990760 : ℤ) ∣ C)
    (hcop : IsCoprime (A * B * C) (q : ℤ)) :
    ∃ (z : ℤ × ℤ) (Γ : AddSubgroup (ℤ × ℤ)) (δ : ℕ), δ ∣ 508 ∧ Γ.index = q ^ 2 * δ ∧
      ∀ y : ℤ × ℤ, (∃ x : Fin 6 → ℤ, OnPl q A B C x ∧ x 0 - x 4 = y.1 ∧ x 2 - x 4 = y.2) ↔ y - z ∈ Γ := by
  -- Route: Γ = kernel of (u, v) ↦ ((15 A q + 6930 B C) u + 14322 C² v mod q², 15 u + 31 v mod 508), δ = 508.
  -- The q-part is one congruence mod q² (the second plane condition follows from the other two since C is a unit
  -- mod q); the 508-part is 508 ∣ 15u + 31v because A, B, C ≡ 0 and q ≡ 1 mod W.
  obtain ⟨x₀, hx₀, -⟩ := local_witness OnPl hOnPl q A B C hq1 hqW hA hB hC
    (IsCoprime.of_mul_left_right hcop)
  rw [hOnPl] at hx₀
  obtain ⟨e1₀, e2₀, e3₀, e4₀⟩ := hx₀
  obtain ⟨a, rfl⟩ := hA
  obtain ⟨b, rfl⟩ := hB
  obtain ⟨c, rfl⟩ := hC
  have hqr : (q : ℤ) = 4619990760 * ((q / 4619990760 : ℕ) : ℤ) + 1 := by
    have h := Nat.div_add_mod q 4619990760
    rw [hqW] at h
    exact_mod_cast h.symm
  generalize ((q / 4619990760 : ℕ) : ℤ) = r at hqr
  have hCq : IsCoprime (4619990760 * c) (q : ℤ) := IsCoprime.of_mul_left_right hcop
  have hQpos : (0 : ℤ) < (q : ℤ) := by omega
  generalize hQ : (q : ℤ) = Q at hqr hCq hQpos e1₀ e2₀ e3₀ e4₀ ⊢
  subst hqr
  have hQ0 : (4619990760 * r + 1 : ℤ) ≠ 0 := hQpos.ne'
  have h462 : IsCoprime (462 : ℤ) (4619990760 * r + 1) := ⟨-9999980 * r, 1, by ring⟩
  have h508 : IsCoprime (508 : ℤ) (4619990760 * r + 1) := ⟨-9094470 * r, 1, by ring⟩
  have h14322 : IsCoprime (14322 : ℤ) (4619990760 * r + 1) := ⟨-322580 * r, 1, by ring⟩
  have hq2 : ((q ^ 2 : ℕ) : ℤ) = (4619990760 * r + 1) ^ 2 := by push_cast; rw [hQ]
  obtain ⟨f, hf⟩ : ∃ f : ℤ × ℤ →+ ZMod (q ^ 2) × ZMod 508, ∀ y : ℤ × ℤ,
      f y = ((((15 * (4619990760 * a) * (4619990760 * r + 1) + 6930 * (4619990760 * b) * (4619990760 * c)) * y.1 +
        14322 * (4619990760 * c) ^ 2 * y.2 : ℤ) : ZMod (q ^ 2)), ((15 * y.1 + 31 * y.2 : ℤ) : ZMod 508)) :=
    ⟨AddMonoidHom.mk' (fun y : ℤ × ℤ => ((((15 * (4619990760 * a) * (4619990760 * r + 1) + 6930 * (4619990760 * b) * (4619990760 * c)) * y.1 +
        14322 * (4619990760 * c) ^ 2 * y.2 : ℤ) : ZMod (q ^ 2)), ((15 * y.1 + 31 * y.2 : ℤ) : ZMod 508)))
      (by
        intro y y'
        simp only [Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, Prod.mk.injEq]
        constructor <;> push_cast <;> ring), fun y => rfl⟩
  have hker : ∀ y : ℤ × ℤ, y ∈ f.ker ↔
      (4619990760 * r + 1) ^ 2 ∣ (15 * (4619990760 * a) * (4619990760 * r + 1) + 6930 * (4619990760 * b) * (4619990760 * c)) * y.1 +
        14322 * (4619990760 * c) ^ 2 * y.2 ∧ (508 : ℤ) ∣ 15 * y.1 + 31 * y.2 := by
    intro y
    rw [AddMonoidHom.mem_ker, hf, Prod.mk_eq_zero, ZMod.intCast_zmod_eq_zero_iff_dvd,
      ZMod.intCast_zmod_eq_zero_iff_dvd, hq2]
    simp only [Nat.cast_ofNat]
  have hsurj : Function.Surjective f := by
    rintro ⟨s, t⟩
    have hk : IsCoprime (508 * (14322 * (4619990760 * c) ^ 2)) ((4619990760 * r + 1) ^ 2) :=
      (h508.mul_left (h14322.mul_left (hCq.pow_left))).pow_right
    obtain ⟨μ, ν, hμν⟩ := hk
    refine ⟨(0, 295 * (ZMod.cast t : ℤ) + 508 * (μ * ((ZMod.cast s : ℤ) -
      14322 * (4619990760 * c) ^ 2 * 295 * (ZMod.cast t : ℤ)))), ?_⟩
    rw [hf, Prod.mk.injEq]
    constructor
    · conv_rhs => rw [← ZMod.intCast_zmod_cast s]
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub, hq2]
      exact ⟨((ZMod.cast s : ℤ) - 14322 * (4619990760 * c) ^ 2 * 295 * (ZMod.cast t : ℤ)) * ν, by
        linear_combination (-((ZMod.cast s : ℤ) - 14322 * (4619990760 * c) ^ 2 * 295 * (ZMod.cast t : ℤ))) * hμν⟩
    · conv_rhs => rw [← ZMod.intCast_zmod_cast t]
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      exact ⟨-18 * (ZMod.cast t : ℤ) - 31 * (μ * ((ZMod.cast s : ℤ) -
        14322 * (4619990760 * c) ^ 2 * 295 * (ZMod.cast t : ℤ))), by push_cast; ring⟩
  refine ⟨(x₀ 0 - x₀ 4, x₀ 2 - x₀ 4), f.ker, 508, dvd_rfl, ?_, ?_⟩
  · rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hsurj, AddSubgroup.card_top,
      Nat.card_prod, Nat.card_zmod, Nat.card_zmod]
  · rintro ⟨y1, y2⟩
    rw [hker]
    simp only [Prod.mk_sub_mk]
    constructor
    · rintro ⟨x, hx, hy1, hy2⟩
      rw [hOnPl] at hx
      obtain ⟨e1, e2, e3, e4⟩ := hx
      subst hy1 hy2
      refine ⟨⟨-((x 3 - x 4) - (x₀ 3 - x₀ 4)), by
        linear_combination (4619990760 * r + 1) * (e2 - e2₀) + 462 * (4619990760 * c) * (e3 - e3₀)⟩, ?_⟩
      have h4 : x 4 - x₀ 4 = 4619990760 * (-(15 * b * ((x 0 - x 4) - (x₀ 0 - x₀ 4)) +
          31 * c * ((x 2 - x 4) - (x₀ 2 - x₀ 4))) - r * (x 4 - x₀ 4)) := by
        linear_combination (e3 - e3₀)
      have h1 : (x 1 - x 4) - (x₀ 1 - x₀ 4) = 4619990760 * (31 * a * ((x 2 - x 4) - (x₀ 2 - x₀ 4)) +
          462 * b * (x 4 - x₀ 4) - r * ((x 1 - x 4) - (x₀ 1 - x₀ 4))) := by
        linear_combination (e1 - e1₀)
      have h3 : (x 3 - x 4) - (x₀ 3 - x₀ 4) = 4619990760 * (-15 * a * ((x 0 - x 4) - (x₀ 0 - x₀ 4)) +
          462 * c * (x 4 - x₀ 4) - r * ((x 3 - x 4) - (x₀ 3 - x₀ 4))) := by
        linear_combination (e2 - e2₀)
      exact ⟨(x 5 - x₀ 5) - 9094470 * (15 * (31 * a * ((x 2 - x 4) - (x₀ 2 - x₀ 4)) +
          462 * b * (x 4 - x₀ 4) - r * ((x 1 - x 4) - (x₀ 1 - x₀ 4))) +
        31 * (-15 * a * ((x 0 - x 4) - (x₀ 0 - x₀ 4)) +
          462 * c * (x 4 - x₀ 4) - r * ((x 3 - x 4) - (x₀ 3 - x₀ 4))) -
        416 * (-(15 * b * ((x 0 - x 4) - (x₀ 0 - x₀ 4)) +
          31 * c * ((x 2 - x 4) - (x₀ 2 - x₀ 4))) - r * (x 4 - x₀ 4))), by
        linear_combination -(e4 - e4₀) - 15 * h1 - 31 * h3 + 416 * h4⟩
    · rintro ⟨⟨w, hw⟩, ⟨h5, h5eq⟩⟩
      set u := y1 - (x₀ 0 - x₀ 4) with hu
      set v := y2 - (x₀ 2 - x₀ 4) with hv
      have hQL : (4619990760 * r + 1) ∣ 462 * (4619990760 * c) * (15 * (4619990760 * b) * u + 31 * (4619990760 * c) * v) :=
        ⟨(4619990760 * r + 1) * w - 15 * (4619990760 * a) * u, by linear_combination hw⟩
      obtain ⟨m1, hm1⟩ := ((h462.mul_left hCq).symm).dvd_of_dvd_mul_left hQL
      have hQw : (4619990760 * r + 1) * w = 15 * (4619990760 * a) * u - 462 * (4619990760 * c) * (-m1) :=
        mul_left_cancel₀ hQ0 (by linear_combination -hw + 462 * (4619990760 * c) * hm1)
      have hQg : (4619990760 * r + 1) ∣ (4619990760 * c) * (31 * (4619990760 * a) * v + 462 * (4619990760 * b) * (-m1)) :=
        ⟨(4619990760 * a) * m1 - (4619990760 * b) * w, by
          linear_combination (4619990760 * a) * hm1 + (4619990760 * b) * hQw⟩
      obtain ⟨g, hg⟩ := hCq.symm.dvd_of_dvd_mul_left hQg
      have h4W : -m1 = 4619990760 * (-(15 * b * u + 31 * c * v) - r * (-m1)) := by linear_combination hm1
      have hgW : g = 4619990760 * (31 * a * v + 462 * b * (-m1) - r * g) := by linear_combination -hg
      have hwW : w = 4619990760 * (15 * a * u - 462 * c * (-m1) - r * w) := by linear_combination hQw
      refine ⟨![x₀ 0 + (u + -m1), x₀ 1 + (-m1 + g), x₀ 2 + (v + -m1), x₀ 3 + (-m1 - w), x₀ 4 + -m1,
        x₀ 5 + (h5 + 9094470 * (15 * (31 * a * v + 462 * b * (-m1) - r * g) -
          31 * (15 * a * u - 462 * c * (-m1) - r * w) - 416 * (-(15 * b * u + 31 * c * v) - r * (-m1))))],
        ?_, ?_, ?_⟩
      · rw [hOnPl]
        simp only [Matrix.cons_val, Fin.isValue]
        refine ⟨by linear_combination e1₀ - hg, by linear_combination e2₀ - hQw,
          by linear_combination e3₀ + hm1, ?_⟩
        linear_combination e4₀ - h5eq - 15 * hgW + 31 * hwW + 416 * h4W
      · simp only [Matrix.cons_val, Fin.isValue]; rw [hu]; ring
      · simp only [Matrix.cons_val, Fin.isValue]; rw [hv]; ring

-- N23 helper
lemma lc_mul_abs (P y M U : ℝ) (hP0 : 0 ≤ P) (hP : P ≤ M) (hy : |y| ≤ U) : |P * y| ≤ M * U := by
  rw [abs_mul, abs_of_nonneg hP0]
  exact mul_le_mul hP hy (abs_nonneg _) (hP0.trans hP)

-- N23 helper
lemma lc_div_abs (Q w R : ℝ) (hQ : 0 < Q) (h : |Q * w| ≤ Q * R) : |w| ≤ R := by
  rw [abs_mul, abs_of_pos hQ] at h
  exact le_of_mul_le_mul_left h hQ

-- N23 helper
lemma lc_bound (Q A B C Z U e x0 x1 x2 x3 x4 x5 : ℝ) (hQ : 1 ≤ Q) (hZ : 1 ≤ Z) (hA0 : 0 ≤ A)
    (hA : A ≤ 2 * Q * Z ^ 2) (hB0 : 0 ≤ B) (hB : B ≤ 2 * Q * Z) (hC0 : 0 ≤ C) (hC : C ≤ 2 * Q * Z)
    (hU : 0 ≤ U) (he0 : 0 ≤ e) (he1 : e ≤ 1) (hu : |x0 - x4| ≤ U) (hv : |x2 - x4| ≤ U)
    (h1 : Q * (x1 - x4) = 31 * A * (x2 - x4) + 462 * B * x4)
    (h2 : Q * (x3 - x4) = -15 * A * (x0 - x4) + 462 * C * x4)
    (h3 : Q * (x4 + e) = -(15 * B * (x0 - x4) + 31 * C * (x2 - x4)))
    (h4 : 508 * x5 = 15 * (x0 + x1) + 31 * (x2 + x3) - 508 * x4 - 462 * e) :
    |x0| ≤ 10 ^ 6 * Z ^ 2 * (U + 1) ∧ |x1| ≤ 10 ^ 6 * Z ^ 2 * (U + 1) ∧ |x2| ≤ 10 ^ 6 * Z ^ 2 * (U + 1) ∧
    |x3| ≤ 10 ^ 6 * Z ^ 2 * (U + 1) ∧ |x4| ≤ 10 ^ 6 * Z ^ 2 * (U + 1) ∧
    |x5| ≤ 10 ^ 6 * Z ^ 2 * (U + 1) := by
  have hQ0 : 0 < Q := by linarith
  have hZ0 : 0 ≤ Z := by linarith
  have hZZ : Z ≤ Z ^ 2 := by nlinarith
  have hZ1 : 1 ≤ Z ^ 2 := by nlinarith
  have hZU : Z * U ≤ Z ^ 2 * U := mul_le_mul_of_nonneg_right hZZ hU
  have hU2 : U ≤ Z ^ 2 * U := le_mul_of_one_le_left hU hZ1
  have k4 : |x4 + e| ≤ 92 * Z * U := by
    apply lc_div_abs Q _ _ hQ0
    rw [h3, abs_neg]
    calc |15 * B * (x0 - x4) + 31 * C * (x2 - x4)| ≤ |15 * B * (x0 - x4)| + |31 * C * (x2 - x4)| :=
          abs_add_le _ _
      _ ≤ (30 * Q * Z) * U + (62 * Q * Z) * U :=
          add_le_add (lc_mul_abs _ _ _ _ (by positivity) (by linarith) hu)
            (lc_mul_abs _ _ _ _ (by positivity) (by linarith) hv)
      _ = Q * (92 * Z * U) := by ring
  obtain ⟨k4l, k4u⟩ := abs_le.mp k4
  have hx4 : |x4| ≤ 92 * Z * U + 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have k1 : |x1 - x4| ≤ 62 * Z ^ 2 * U + 924 * Z * (92 * Z * U + 1) := by
    apply lc_div_abs Q _ _ hQ0
    rw [h1]
    calc |31 * A * (x2 - x4) + 462 * B * x4| ≤ |31 * A * (x2 - x4)| + |462 * B * x4| := abs_add_le _ _
      _ ≤ (62 * Q * Z ^ 2) * U + (924 * Q * Z) * (92 * Z * U + 1) :=
          add_le_add (lc_mul_abs _ _ _ _ (by positivity) (by linarith) hv)
            (lc_mul_abs _ _ _ _ (by positivity) (by linarith) hx4)
      _ = Q * (62 * Z ^ 2 * U + 924 * Z * (92 * Z * U + 1)) := by ring
  have k3 : |x3 - x4| ≤ 30 * Z ^ 2 * U + 924 * Z * (92 * Z * U + 1) := by
    apply lc_div_abs Q _ _ hQ0
    rw [h2]
    calc |-15 * A * (x0 - x4) + 462 * C * x4| ≤ |-15 * A * (x0 - x4)| + |462 * C * x4| := abs_add_le _ _
      _ = |15 * A * (x0 - x4)| + |462 * C * x4| := by
          rw [show -15 * A * (x0 - x4) = -(15 * A * (x0 - x4)) by ring, abs_neg]
      _ ≤ (30 * Q * Z ^ 2) * U + (924 * Q * Z) * (92 * Z * U + 1) :=
          add_le_add (lc_mul_abs _ _ _ _ (by positivity) (by linarith) hu)
            (lc_mul_abs _ _ _ _ (by positivity) (by linarith) hx4)
      _ = Q * (30 * Z ^ 2 * U + 924 * Z * (92 * Z * U + 1)) := by ring
  obtain ⟨hul, huu⟩ := abs_le.mp hu
  obtain ⟨hvl, hvu⟩ := abs_le.mp hv
  obtain ⟨k1l, k1u⟩ := abs_le.mp k1
  obtain ⟨k3l, k3u⟩ := abs_le.mp k3
  obtain ⟨x4l, x4u⟩ := abs_le.mp hx4
  have hx5u : 508 * x5 ≤ 15 * ((U + (92 * Z * U + 1)) + (62 * Z ^ 2 * U + 924 * Z * (92 * Z * U + 1) +
      (92 * Z * U + 1))) + 31 * ((U + (92 * Z * U + 1)) + (30 * Z ^ 2 * U + 924 * Z * (92 * Z * U + 1) +
      (92 * Z * U + 1))) + 508 * (92 * Z * U + 1) + 462 := by
    rw [h4]; linarith
  have hx5l : -(15 * ((U + (92 * Z * U + 1)) + (62 * Z ^ 2 * U + 924 * Z * (92 * Z * U + 1) +
      (92 * Z * U + 1))) + 31 * ((U + (92 * Z * U + 1)) + (30 * Z ^ 2 * U + 924 * Z * (92 * Z * U + 1) +
      (92 * Z * U + 1))) + 508 * (92 * Z * U + 1) + 462) ≤ 508 * x5 := by
    rw [h4]; linarith
  refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩,
    abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩,
    abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩

-- N23 helper
lemma lc_zero (Q A B C : ℤ) (hQ0 : Q ≠ 0) (d : Fin 6 → ℤ)
    (e1 : Q * (d 1 - d 4) = 31 * A * (d 2 - d 4) + 462 * B * d 4)
    (e2 : Q * (d 3 - d 4) = -15 * A * (d 0 - d 4) + 462 * C * d 4)
    (e3 : Q * d 4 = -(15 * B * (d 0 - d 4) + 31 * C * (d 2 - d 4)))
    (e4 : 508 * d 5 = 15 * (d 0 + d 1) + 31 * (d 2 + d 3) - 508 * d 4)
    (h0 : d 0 - d 4 = 0) (h2 : d 2 - d 4 = 0) : ∀ i, d i = 0 := by
  have h4 : d 4 = 0 := mul_left_cancel₀ hQ0 (by linear_combination e3 - 15 * B * h0 - 31 * C * h2)
  have h1' : d 1 - d 4 = 0 := mul_left_cancel₀ hQ0 (by linear_combination e1 + 31 * A * h2 + 462 * B * h4)
  have h3' : d 3 - d 4 = 0 := mul_left_cancel₀ hQ0 (by linear_combination e2 - 15 * A * h0 + 462 * C * h4)
  have hd0 : d 0 = 0 := by linarith
  have hd1 : d 1 = 0 := by linarith
  have hd2 : d 2 = 0 := by linarith
  have hd3 : d 3 = 0 := by linarith
  have hd5 : d 5 = 0 := by
    have : (508 : ℤ) * d 5 = 508 * 0 := by
      linear_combination e4 + 15 * hd0 + 15 * hd1 + 31 * hd2 + 31 * hd3 - 508 * h4
    omega
  intro i
  fin_cases i
  · exact hd0
  · exact hd1
  · exact hd2
  · exact hd3
  · exact h4
  · exact hd5

-- N23 helper
lemma lc_hlift (a b c r u v w h : ℤ) (hCq : IsCoprime (4619990760 * c) (4619990760 * r + 1))
    (h462 : IsCoprime (462 : ℤ) (4619990760 * r + 1)) (hQ0 : (4619990760 * r + 1 : ℤ) ≠ 0)
    (hw : (15 * (4619990760 * a) * (4619990760 * r + 1) + 6930 * (4619990760 * b) * (4619990760 * c)) * u + 14322 * (4619990760 * c) ^ 2 * v =
      (4619990760 * r + 1) ^ 2 * w)
    (h5eq : 15 * u + 31 * v = 508 * h) :
    ∃ d : Fin 6 → ℤ,
      (4619990760 * r + 1) * (d 1 - d 4) = 31 * (4619990760 * a) * (d 2 - d 4) + 462 * (4619990760 * b) * d 4 ∧
      (4619990760 * r + 1) * (d 3 - d 4) = -15 * (4619990760 * a) * (d 0 - d 4) + 462 * (4619990760 * c) * d 4 ∧
      (4619990760 * r + 1) * d 4 = -(15 * (4619990760 * b) * (d 0 - d 4) + 31 * (4619990760 * c) * (d 2 - d 4)) ∧
      508 * d 5 = 15 * (d 0 + d 1) + 31 * (d 2 + d 3) - 508 * d 4 ∧
      d 0 - d 4 = u ∧ d 2 - d 4 = v := by
  have hQL : (4619990760 * r + 1) ∣ 462 * (4619990760 * c) * (15 * (4619990760 * b) * u + 31 * (4619990760 * c) * v) :=
    ⟨(4619990760 * r + 1) * w - 15 * (4619990760 * a) * u, by linear_combination hw⟩
  obtain ⟨m1, hm1⟩ := ((h462.mul_left hCq).symm).dvd_of_dvd_mul_left hQL
  have hQw : (4619990760 * r + 1) * w = 15 * (4619990760 * a) * u - 462 * (4619990760 * c) * (-m1) :=
    mul_left_cancel₀ hQ0 (by linear_combination -hw + 462 * (4619990760 * c) * hm1)
  have hQg : (4619990760 * r + 1) ∣ (4619990760 * c) * (31 * (4619990760 * a) * v + 462 * (4619990760 * b) * (-m1)) :=
    ⟨(4619990760 * a) * m1 - (4619990760 * b) * w, by linear_combination (4619990760 * a) * hm1 + (4619990760 * b) * hQw⟩
  obtain ⟨g, hg⟩ := hCq.symm.dvd_of_dvd_mul_left hQg
  have h4W : -m1 = 4619990760 * (-(15 * b * u + 31 * c * v) - r * (-m1)) := by linear_combination hm1
  have hgW : g = 4619990760 * (31 * a * v + 462 * b * (-m1) - r * g) := by linear_combination -hg
  have hwW : w = 4619990760 * (15 * a * u - 462 * c * (-m1) - r * w) := by linear_combination hQw
  refine ⟨![u + -m1, -m1 + g, v + -m1, -m1 - w, -m1,
    h + 9094470 * (15 * (31 * a * v + 462 * b * (-m1) - r * g) -
      31 * (15 * a * u - 462 * c * (-m1) - r * w) - 416 * (-(15 * b * u + 31 * c * v) - r * (-m1)))], ?_⟩
  simp only [Matrix.cons_val, Fin.isValue]
  refine ⟨by linear_combination -hg, by linear_combination -hQw, by linear_combination hm1, ?_,
    by ring, by ring⟩
  linear_combination -h5eq - 15 * hgW + 31 * hwW + 416 * h4W

-- N23 helper
lemma lc_proj (a b c r : ℤ) (D : Fin 6 → ℤ)
    (E1 : (4619990760 * r + 1) * (D 1 - D 4) = 31 * (4619990760 * a) * (D 2 - D 4) + 462 * (4619990760 * b) * D 4)
    (E2 : (4619990760 * r + 1) * (D 3 - D 4) = -15 * (4619990760 * a) * (D 0 - D 4) + 462 * (4619990760 * c) * D 4)
    (E3 : (4619990760 * r + 1) * D 4 = -(15 * (4619990760 * b) * (D 0 - D 4) + 31 * (4619990760 * c) * (D 2 - D 4)))
    (E4 : 508 * D 5 = 15 * (D 0 + D 1) + 31 * (D 2 + D 3) - 508 * D 4) :
    (4619990760 * r + 1) ^ 2 ∣ (15 * (4619990760 * a) * (4619990760 * r + 1) + 6930 * (4619990760 * b) * (4619990760 * c)) * (D 0 - D 4) +
      14322 * (4619990760 * c) ^ 2 * (D 2 - D 4) ∧ (508 : ℤ) ∣ 15 * (D 0 - D 4) + 31 * (D 2 - D 4) := by
  refine ⟨⟨-(D 3 - D 4), by linear_combination (4619990760 * r + 1) * E2 + 462 * (4619990760 * c) * E3⟩, ?_⟩
  have h4 : D 4 = 4619990760 * (-(15 * b * (D 0 - D 4) + 31 * c * (D 2 - D 4)) - r * D 4) := by
    linear_combination E3
  have h1 : D 1 - D 4 = 4619990760 * (31 * a * (D 2 - D 4) + 462 * b * D 4 - r * (D 1 - D 4)) := by
    linear_combination E1
  have h3 : D 3 - D 4 = 4619990760 * (-15 * a * (D 0 - D 4) + 462 * c * D 4 - r * (D 3 - D 4)) := by
    linear_combination E2
  exact ⟨D 5 - 9094470 * (15 * (31 * a * (D 2 - D 4) + 462 * b * D 4 - r * (D 1 - D 4)) +
      31 * (-15 * a * (D 0 - D 4) + 462 * c * D 4 - r * (D 3 - D 4)) -
      416 * (-(15 * b * (D 0 - D 4) + 31 * c * (D 2 - D 4)) - r * D 4)), by
    linear_combination -E4 - 15 * h1 - 31 * h3 + 416 * h4⟩

-- N23 helper
lemma lc_volume (T N ρ t0 : ℝ) (hT : 0 < T) (hN : 0 < N) (K : Set (Fin 2 → ℝ))
    (hK : ∀ v, v ∈ K ↔ (-2 * T ≤ 15 * v 0 ∧ 15 * v 0 ≤ -T ∧
      |31 * (t0 - ρ * v 0 + N * v 1)| ≤ 1 / 100000 * |15 * v 0|)) :
    MeasureTheory.volume K = ENNReal.ofReal (3 / 100000 * T ^ 2 / (465 * N)) := by
  set g1 : ℝ → ℝ := fun x => (ρ * x - t0 - 15 / 3100000 * (-x)) / N with hg1
  set g2 : ℝ → ℝ := fun x => (ρ * x - t0 + 15 / 3100000 * (-x)) / N with hg2
  set S : Set (ℝ × ℝ) := {p | p.fst ∈ Set.Icc (-2 * T / 15) (-T / 15) ∧ p.snd ∈ Set.Icc (g1 p.fst) (g2 p.fst)}
    with hS
  have hKS : K = MeasurableEquiv.finTwoArrow ⁻¹' S := by
    ext v
    rw [hK v, Set.mem_preimage, MeasurableEquiv.finTwoArrow_apply, hS]
    simp only [Set.mem_setOf_eq, Set.mem_Icc, hg1, hg2]
    constructor
    · rintro ⟨h1, h2, h3⟩
      have hv0 : v 0 < 0 := by linarith
      rw [abs_of_neg (by linarith : 15 * v 0 < 0)] at h3
      obtain ⟨h3l, h3u⟩ := abs_le.mp h3
      refine ⟨⟨by linarith, by linarith⟩, ?_, ?_⟩
      · rw [div_le_iff₀ hN]; linarith
      · rw [le_div_iff₀ hN]; linarith
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      rw [div_le_iff₀ hN] at h3
      rw [le_div_iff₀ hN] at h4
      have hv0 : v 0 < 0 := by linarith
      refine ⟨by linarith, by linarith, ?_⟩
      rw [abs_of_neg (by linarith : 15 * v 0 < 0)]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hg1m : Measurable g1 := by
    have : Continuous g1 := by rw [hg1]; fun_prop
    exact this.measurable
  have hg2m : Measurable g2 := by
    have : Continuous g2 := by rw [hg2]; fun_prop
    exact this.measurable
  have hSm : MeasurableSet S := measurableSet_region_between_cc hg1m hg2m measurableSet_Icc
  rw [hKS, (MeasureTheory.volume_preserving_finTwoArrow ℝ).measure_preimage_equiv,
    MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_apply hSm]
  have hfib : ∀ x, MeasureTheory.volume (Prod.mk x ⁻¹' S) =
      (Set.Icc (-2 * T / 15) (-T / 15)).indicator (fun x => ENNReal.ofReal (g2 x - g1 x)) x := by
    intro x
    by_cases hx : x ∈ Set.Icc (-2 * T / 15) (-T / 15)
    · rw [Set.indicator_apply, if_pos hx]
      have : Prod.mk x ⁻¹' S = Set.Icc (g1 x) (g2 x) := by
        ext y; simp only [hS, Set.mem_preimage, Set.mem_setOf_eq]; exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
      rw [this, Real.volume_Icc]
    · rw [Set.indicator_apply, if_neg hx]
      have : Prod.mk x ⁻¹' S = ∅ := by
        ext y; simp only [hS, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hx h.1
      rw [this, MeasureTheory.measure_empty]
  simp only [hfib]
  rw [MeasureTheory.lintegral_indicator measurableSet_Icc]
  have hfun : ∀ x, g2 x - g1 x = (-(30 / 3100000) / N) * x := by
    intro x; simp only [hg1, hg2]; ring
  have hab : -2 * T / 15 ≤ -T / 15 := by linarith
  have hint : MeasureTheory.IntegrableOn (fun x => g2 x - g1 x) (Set.Icc (-2 * T / 15) (-T / 15)) := by
    have : Continuous (fun x => g2 x - g1 x) := by rw [hg1, hg2]; fun_prop
    exact this.integrableOn_Icc
  have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Icc (-2 * T / 15) (-T / 15))] (fun x => g2 x - g1 x) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with x hx
    show (0 : ℝ) ≤ g2 x - g1 x
    rw [hfun x]
    have hx2 : x ≤ -T / 15 := hx.2
    have : 0 ≤ -x := by linarith
    have hc : (-(30 / 3100000) / N) * x = (30 / 3100000) / N * (-x) := by ring
    rw [hc]; positivity
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  rw [show (fun x => g2 x - g1 x) = fun x => (-(30 / 3100000) / N) * x from funext hfun]
  rw [intervalIntegral.integral_const_mul, integral_id]
  field_simp
  ring

-- N23 helper
lemma lc_convex (T N ρ t0 : ℝ) (hT : 0 < T) (K : Set (Fin 2 → ℝ))
    (hK : ∀ v, v ∈ K ↔ (-2 * T ≤ 15 * v 0 ∧ 15 * v 0 ≤ -T ∧
      |31 * (t0 - ρ * v 0 + N * v 1)| ≤ 1 / 100000 * |15 * v 0|)) : Convex ℝ K := by
  intro v hv w hw a b ha hb hab
  rw [hK] at hv hw ⊢
  obtain ⟨v1, v2, v3⟩ := hv
  obtain ⟨w1, w2, w3⟩ := hw
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hv0 : 15 * v 0 < 0 := by linarith
  have hw0 : 15 * w 0 < 0 := by linarith
  have l1 := mul_le_mul_of_nonneg_left v1 ha
  have l2 := mul_le_mul_of_nonneg_left w1 hb
  have l3 := mul_le_mul_of_nonneg_left v2 ha
  have l4 := mul_le_mul_of_nonneg_left w2 hb
  have hT' : a * T + b * T = T := by rw [← add_mul, hab, one_mul]
  refine ⟨by linarith, by linarith, ?_⟩
  have e : 31 * (t0 - ρ * (a * v 0 + b * w 0) + N * (a * v 1 + b * w 1)) =
      a * (31 * (t0 - ρ * v 0 + N * v 1)) + b * (31 * (t0 - ρ * w 0 + N * w 1)) := by
    linear_combination (-31 * t0) * hab
  have hsum : 15 * (a * v 0 + b * w 0) ≤ 0 := by linarith
  rw [abs_of_neg hv0] at v3
  rw [abs_of_neg hw0] at w3
  rw [e, abs_of_nonpos hsum]
  calc |a * (31 * (t0 - ρ * v 0 + N * v 1)) + b * (31 * (t0 - ρ * w 0 + N * w 1))|
      ≤ |a * (31 * (t0 - ρ * v 0 + N * v 1))| + |b * (31 * (t0 - ρ * w 0 + N * w 1))| := abs_add_le _ _
    _ = a * |31 * (t0 - ρ * v 0 + N * v 1)| + b * |31 * (t0 - ρ * w 0 + N * w 1)| := by
        rw [abs_mul a, abs_mul b, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * (1 / 100000 * -(15 * v 0)) + b * (1 / 100000 * -(15 * w 0)) :=
        add_le_add (mul_le_mul_of_nonneg_left v3 ha) (mul_le_mul_of_nonneg_left w3 hb)
    _ = 1 / 100000 * -(15 * (a * v 0 + b * w 0)) := by ring

-- N23 helper
lemma lc_bounded (T N ρ t0 : ℝ) (hT : 2 ≤ T) (hN : 1 ≤ N) (hρ0 : 0 ≤ ρ) (hρN : ρ ≤ N) (ht0 : 0 ≤ t0)
    (ht0N : t0 ≤ N) (K : Set (Fin 2 → ℝ))
    (hK : ∀ v, v ∈ K ↔ (-2 * T ≤ 15 * v 0 ∧ 15 * v 0 ≤ -T ∧
      |31 * (t0 - ρ * v 0 + N * v 1)| ≤ 1 / 100000 * |15 * v 0|)) : ∀ v ∈ K, ∀ j, |v j| ≤ 1 * T := by
  intro v hv j
  rw [hK] at hv
  obtain ⟨h1, h2, h3⟩ := hv
  have hv0 : v 0 ≤ 0 := by linarith
  rw [abs_of_neg (by linarith : 15 * v 0 < 0)] at h3
  obtain ⟨h3l, h3u⟩ := abs_le.mp h3
  have hNpos : 0 < N := by linarith
  have p1 : ρ * v 0 ≤ 0 := by nlinarith [mul_nonneg hρ0 (show 0 ≤ -v 0 by linarith)]
  have p2 : N * v 0 ≤ ρ * v 0 := by nlinarith [mul_nonneg (sub_nonneg.mpr hρN) (show 0 ≤ -v 0 by linarith)]
  have p3 : -(2 * T) * N ≤ 15 * (N * v 0) := by
    nlinarith [mul_nonneg hNpos.le (show 0 ≤ 15 * v 0 + 2 * T by linarith)]
  have p4 : T ≤ N * T := by nlinarith [mul_nonneg (sub_nonneg.mpr hN) (by linarith : (0 : ℝ) ≤ T)]
  have p5 : 2 * N ≤ N * T := by nlinarith [mul_nonneg hNpos.le (sub_nonneg.mpr hT)]
  have up : N * v 1 ≤ N * T := by linarith
  have lo : N * (-T) ≤ N * v 1 := by linarith
  have hv1 : |v 1| ≤ T := abs_le.mpr ⟨le_of_mul_le_mul_left lo hNpos, le_of_mul_le_mul_left up hNpos⟩
  have hv0' : |v 0| ≤ T := abs_le.mpr ⟨by linarith, by linarith⟩
  rw [one_mul]
  fin_cases j
  · exact hv0'
  · exact hv1

-- N23 lattice_coords [extremal_averaging]
theorem lattice_coords (OnPl : ℤ → ℤ → ℤ → ℤ → (Fin 6 → ℤ) → Prop)
    (hOnPl : ∀ q A B C (x : Fin 6 → ℤ), OnPl q A B C x ↔
      (q * (x 1 - x 4) = 31 * A * (x 2 - x 4) + 462 * B * x 4 ∧
       q * (x 3 - x 4) = -15 * A * (x 0 - x 4) + 462 * C * x 4 ∧
       q * (x 4 + 1) = -(15 * B * (x 0 - x 4) + 31 * C * (x 2 - x 4)) ∧
       508 * x 5 = 15 * (x 0 + x 1) + 31 * (x 2 + x 3) - 508 * x 4 - 462)) :
    ∃ C0 C1 C2 : ℝ, 0 < C1 ∧ ∀ (q : ℕ) (A B C : ℤ) (Z T : ℝ),
      1 ≤ q → q % 4619990760 = 1 → (4619990760 : ℤ) ∣ A → (4619990760 : ℤ) ∣ B → (4619990760 : ℤ) ∣ C →
      IsCoprime (A * B * C) (q : ℤ) → 100 ≤ Z →
      (q : ℝ) * Z ^ 2 ≤ A → (A : ℝ) < 2 * q * Z ^ 2 → (q : ℝ) * Z ≤ B → (B : ℝ) < 2 * q * Z →
      (q : ℝ) * Z ≤ C → (C : ℝ) < 2 * q * Z → C0 * (q : ℝ) ^ 2 ≤ T →
      ∃ (c : Fin 6 → ℤ) (L : Fin 6 → Fin 2 → ℤ) (δ : ℕ), δ ∣ 508 ∧
        (∀ n : Fin 2 → ℤ, OnPl q A B C (fun i => c i + ∑ j, L i j * n j)) ∧
        (∀ x, OnPl q A B C x → ∃! n : Fin 2 → ℤ, x = fun i => c i + ∑ j, L i j * n j) ∧
        |15 * (L 0 0 - L 4 0) * (31 * (L 2 1 - L 4 1)) - 15 * (L 0 1 - L 4 1) * (31 * (L 2 0 - L 4 0))| = 465 * (q : ℤ) ^ 2 * δ ∧
        (∀ i, |(c i : ℝ)| ≤ C2 * Z ^ 2 * (q : ℝ) ^ 2 ∧ ∀ j, |(L i j : ℝ)| ≤ C2 * Z ^ 2 * (q : ℝ) ^ 2) ∧
        ∀ K : Set (Fin 2 → ℝ),
          (∀ v, v ∈ K ↔
            (-2 * T ≤ 15 * (((c 0 : ℝ) + ∑ j, (L 0 j : ℝ) * v j) - ((c 4 : ℝ) + ∑ j, (L 4 j : ℝ) * v j)) ∧ 15 * (((c 0 : ℝ) + ∑ j, (L 0 j : ℝ) * v j) - ((c 4 : ℝ) + ∑ j, (L 4 j : ℝ) * v j)) ≤ -T ∧
             |31 * (((c 2 : ℝ) + ∑ j, (L 2 j : ℝ) * v j) - ((c 4 : ℝ) + ∑ j, (L 4 j : ℝ) * v j))| ≤ 1 / 100000 * |15 * (((c 0 : ℝ) + ∑ j, (L 0 j : ℝ) * v j) - ((c 4 : ℝ) + ∑ j, (L 4 j : ℝ) * v j))|)) →
          Convex ℝ K ∧
          MeasureTheory.volume K = ENNReal.ofReal (3 / 100000 * T ^ 2 / (465 * (q : ℝ) ^ 2 * δ)) ∧
          ∀ v ∈ K, ∀ j, |v j| ≤ C1 * T := by
  -- Route: the projected lattice is {(u, v) : v ≡ -ρ u mod 508 q²} (ρ from CRT), so the basis
  -- (1, -ρ), (0, 508 q²) with 0 ≤ ρ < 508 q² has a bounded inverse (no reduction needed); c is the plane point
  -- over (0, t0), 0 ≤ t0 < 508 q²; lifts by lc_hlift; K is then {v₀ ∈ [-2T/15, -T/15], v₁ in an interval}
  -- whose area is computed by Fubini (lc_volume).
  refine ⟨2, 1, 10 ^ 9, by norm_num, ?_⟩
  intro q A B C Z T hq hqW hA hB hC hcop hZ hA1 hA2 hB1 hB2 hC1 hC2 hT
  obtain ⟨x₀, hx₀, -⟩ := local_witness OnPl hOnPl q A B C hq hqW hA hB hC
    (IsCoprime.of_mul_left_right hcop)
  rw [hOnPl] at hx₀
  obtain ⟨e1₀, e2₀, e3₀, e4₀⟩ := hx₀
  obtain ⟨a, rfl⟩ := hA
  obtain ⟨b, rfl⟩ := hB
  obtain ⟨c, rfl⟩ := hC
  have hqr : (q : ℤ) = 4619990760 * ((q / 4619990760 : ℕ) : ℤ) + 1 := by
    have h := Nat.div_add_mod q 4619990760
    rw [hqW] at h
    exact_mod_cast h.symm
  generalize ((q / 4619990760 : ℕ) : ℤ) = r at hqr
  have hCq : IsCoprime (4619990760 * c) (q : ℤ) := IsCoprime.of_mul_left_right hcop
  have hQpos : (0 : ℤ) < (q : ℤ) := by omega
  have hqR : ((q : ℤ) : ℝ) = (q : ℝ) := Int.cast_natCast q
  generalize hQ : (q : ℤ) = Q at hqr hCq hQpos e1₀ e2₀ e3₀ e4₀ hqR ⊢
  subst hqr
  have hQ0 : (4619990760 * r + 1) ≠ 0 := hQpos.ne'
  have h462 : IsCoprime (462 : ℤ) (4619990760 * r + 1) := ⟨-9999980 * r, 1, by ring⟩
  have h508 : IsCoprime (508 : ℤ) (4619990760 * r + 1) := ⟨-9094470 * r, 1, by ring⟩
  have h14322 : IsCoprime (14322 : ℤ) (4619990760 * r + 1) := ⟨-322580 * r, 1, by ring⟩
  have hk : IsCoprime (508 * (14322 * (4619990760 * c) ^ 2)) ((4619990760 * r + 1) ^ 2) :=
    (h508.mul_left (h14322.mul_left (hCq.pow_left))).pow_right
  obtain ⟨μ, ν, hμν⟩ := hk
  have hNpos : (0 : ℤ) < 508 * (4619990760 * r + 1) ^ 2 := mul_pos (by norm_num) (pow_pos hQpos 2)
  obtain ⟨ρ, hρ0, hρN, hρ1, hρ2⟩ : ∃ ρ : ℤ, 0 ≤ ρ ∧ ρ < 508 * (4619990760 * r + 1) ^ 2 ∧
      (4619990760 * r + 1) ^ 2 ∣ (15 * (4619990760 * a) * (4619990760 * r + 1) + 6930 * (4619990760 * b) * (4619990760 * c)) - (14322 * (4619990760 * c) ^ 2) * ρ ∧ (508 : ℤ) ∣ 31 * ρ - 15 := by
    obtain ⟨ρ0, hρ0def⟩ : ∃ ρ0 : ℤ, ρ0 = 4425 + 508 * (μ * ((15 * (4619990760 * a) * (4619990760 * r + 1) + 6930 * (4619990760 * b) * (4619990760 * c)) - (14322 * (4619990760 * c) ^ 2) * 4425)) := ⟨_, rfl⟩
    refine ⟨ρ0 % (508 * (4619990760 * r + 1) ^ 2), Int.emod_nonneg _ hNpos.ne', Int.emod_lt_of_pos _ hNpos, ?_, ?_⟩
    · rw [Int.emod_def]
      exact ⟨ν * ((15 * (4619990760 * a) * (4619990760 * r + 1) + 6930 * (4619990760 * b) * (4619990760 * c)) - (14322 * (4619990760 * c) ^ 2) * 4425) + 508 * (14322 * (4619990760 * c) ^ 2) * (ρ0 / (508 * (4619990760 * r + 1) ^ 2)), by
        linear_combination (-((15 * (4619990760 * a) * (4619990760 * r + 1) + 6930 * (4619990760 * b) * (4619990760 * c)) - (14322 * (4619990760 * c) ^ 2) * 4425)) * hμν - (14322 * (4619990760 * c) ^ 2) * hρ0def⟩
    · rw [Int.emod_def]
      exact ⟨270 + 31 * (μ * ((15 * (4619990760 * a) * (4619990760 * r + 1) + 6930 * (4619990760 * b) * (4619990760 * c)) - (14322 * (4619990760 * c) ^ 2) * 4425)) - 31 * (4619990760 * r + 1) ^ 2 * (ρ0 / (508 * (4619990760 * r + 1) ^ 2)), by
        linear_combination 31 * hρ0def⟩
  obtain ⟨w0, hw0⟩ := hρ1
  obtain ⟨h50, h50e⟩ := hρ2
  obtain ⟨L0, f1, f2, f3, f4, f5, f6⟩ := lc_hlift a b c r 1 (-ρ) w0 (-h50) hCq h462 hQ0
    (by linear_combination hw0) (by linear_combination -h50e)
  obtain ⟨L1, k1, k2, k3, k4, k5, k6⟩ := lc_hlift a b c r 0 (508 * (4619990760 * r + 1) ^ 2) (508 * (14322 * (4619990760 * c) ^ 2)) (31 * (4619990760 * r + 1) ^ 2)
    hCq h462 hQ0 (by ring) (by ring)
  obtain ⟨kk, t0, ht0, ht00, ht0N⟩ : ∃ kk t0 : ℤ,
      t0 = (x₀ 2 - x₀ 4) + ρ * (x₀ 0 - x₀ 4) - 508 * (4619990760 * r + 1) ^ 2 * kk ∧ 0 ≤ t0 ∧ t0 < 508 * (4619990760 * r + 1) ^ 2 :=
    ⟨((x₀ 2 - x₀ 4) + ρ * (x₀ 0 - x₀ 4)) / (508 * (4619990760 * r + 1) ^ 2),
      ((x₀ 2 - x₀ 4) + ρ * (x₀ 0 - x₀ 4)) % (508 * (4619990760 * r + 1) ^ 2),
      Int.emod_def _ _, Int.emod_nonneg _ hNpos.ne', Int.emod_lt_of_pos _ hNpos⟩
  obtain ⟨d, g1, g2, g3, g4, g5, g6⟩ := lc_hlift a b c r (-(x₀ 0 - x₀ 4)) (t0 - (x₀ 2 - x₀ 4))
    (-(x₀ 0 - x₀ 4) * w0 - 508 * (14322 * (4619990760 * c) ^ 2) * kk) ((x₀ 0 - x₀ 4) * h50 - 31 * (4619990760 * r + 1) ^ 2 * kk) hCq h462 hQ0
    (by linear_combination (-(x₀ 0 - x₀ 4)) * hw0 + (14322 * (4619990760 * c) ^ 2) * ht0)
    (by linear_combination (x₀ 0 - x₀ 4) * h50e + 31 * ht0)
  obtain ⟨cc, hcc⟩ : ∃ cc : Fin 6 → ℤ, ∀ i, cc i = x₀ i + d i := ⟨_, fun _ => rfl⟩
  obtain ⟨LL, hLL0, hLL1⟩ : ∃ LL : Fin 6 → Fin 2 → ℤ, (∀ i, LL i 0 = L0 i) ∧ (∀ i, LL i 1 = L1 i) :=
    ⟨fun i => ![L0 i, L1 i], fun _ => rfl, fun _ => rfl⟩
  have hc1 : (4619990760 * r + 1) * (cc 1 - cc 4) = 31 * (4619990760 * a) * (cc 2 - cc 4) + 462 * (4619990760 * b) * cc 4 := by
    simp only [hcc]; linear_combination e1₀ + g1
  have hc2 : (4619990760 * r + 1) * (cc 3 - cc 4) = -15 * (4619990760 * a) * (cc 0 - cc 4) + 462 * (4619990760 * c) * cc 4 := by
    simp only [hcc]; linear_combination e2₀ + g2
  have hc3 : (4619990760 * r + 1) * (cc 4 + 1) = -(15 * (4619990760 * b) * (cc 0 - cc 4) + 31 * (4619990760 * c) * (cc 2 - cc 4)) := by
    simp only [hcc]; linear_combination e3₀ + g3
  have hc4 : 508 * cc 5 = 15 * (cc 0 + cc 1) + 31 * (cc 2 + cc 3) - 508 * cc 4 - 462 := by
    simp only [hcc]; linear_combination e4₀ + g4
  have hcp0 : cc 0 - cc 4 = 0 := by simp only [hcc]; linear_combination g5
  have hcp2 : cc 2 - cc 4 = t0 := by simp only [hcc]; linear_combination g6
  have hsum : ∀ (i : Fin 6) (n : Fin 2 → ℤ), ∑ j, LL i j * n j = L0 i * n 0 + L1 i * n 1 := by
    intro i n; rw [Fin.sum_univ_two, hLL0, hLL1]
  refine ⟨cc, LL, 508, dvd_rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    rw [hOnPl]
    simp only [hsum]
    refine ⟨by linear_combination hc1 + n 0 * f1 + n 1 * k1, by linear_combination hc2 + n 0 * f2 + n 1 * k2,
      by linear_combination hc3 + n 0 * f3 + n 1 * k3, by linear_combination hc4 + n 0 * f4 + n 1 * k4⟩
  · intro x hx
    rw [hOnPl] at hx
    obtain ⟨ex1, ex2, ex3, ex4⟩ := hx
    obtain ⟨D, hD⟩ : ∃ D : Fin 6 → ℤ, ∀ i, D i = x i - cc i - (x 0 - x 4) * L0 i := ⟨_, fun _ => rfl⟩
    have E1 : (4619990760 * r + 1) * (D 1 - D 4) = 31 * (4619990760 * a) * (D 2 - D 4) + 462 * (4619990760 * b) * D 4 := by
      simp only [hD]; linear_combination ex1 - hc1 - (x 0 - x 4) * f1
    have E2 : (4619990760 * r + 1) * (D 3 - D 4) = -15 * (4619990760 * a) * (D 0 - D 4) + 462 * (4619990760 * c) * D 4 := by
      simp only [hD]; linear_combination ex2 - hc2 - (x 0 - x 4) * f2
    have E3 : (4619990760 * r + 1) * D 4 = -(15 * (4619990760 * b) * (D 0 - D 4) + 31 * (4619990760 * c) * (D 2 - D 4)) := by
      simp only [hD]; linear_combination ex3 - hc3 - (x 0 - x 4) * f3
    have E4 : 508 * D 5 = 15 * (D 0 + D 1) + 31 * (D 2 + D 3) - 508 * D 4 := by
      simp only [hD]; linear_combination ex4 - hc4 - (x 0 - x 4) * f4
    have hD0 : D 0 - D 4 = 0 := by simp only [hD]; linear_combination -hcp0 - (x 0 - x 4) * f5
    obtain ⟨hpq, hp5⟩ := lc_proj a b c r D E1 E2 E3 E4
    rw [hD0, mul_zero, zero_add] at hpq
    rw [hD0, mul_zero, zero_add] at hp5
    have hK2 : (4619990760 * r + 1) ^ 2 ∣ D 2 - D 4 := by
      have hcopK : IsCoprime (14322 * (4619990760 * c) ^ 2) ((4619990760 * r + 1) ^ 2) := (h14322.mul_left hCq.pow_left).pow_right
      exact hcopK.symm.dvd_of_dvd_mul_left hpq
    have h5d : (508 : ℤ) ∣ D 2 - D 4 := by
      have hc31 : IsCoprime (508 : ℤ) 31 := ⟨-18, 295, by norm_num⟩
      exact hc31.dvd_of_dvd_mul_left hp5
    obtain ⟨n1, hn1⟩ := IsCoprime.mul_dvd h508.pow_right h5d hK2
    refine ⟨![x 0 - x 4, n1], ?_, ?_⟩
    · obtain ⟨D', hD'⟩ : ∃ D' : Fin 6 → ℤ, ∀ i, D' i = D i - n1 * L1 i := ⟨_, fun _ => rfl⟩
      have hz := lc_zero (4619990760 * r + 1) (4619990760 * a) (4619990760 * b) (4619990760 * c) hQ0 D'
        (by simp only [hD']; linear_combination E1 - n1 * k1)
        (by simp only [hD']; linear_combination E2 - n1 * k2)
        (by simp only [hD']; linear_combination E3 - n1 * k3)
        (by simp only [hD']; linear_combination E4 - n1 * k4)
        (by simp only [hD']; linear_combination hD0 - n1 * k5)
        (by simp only [hD']; linear_combination hn1 - n1 * k6)
      funext i
      have hzi := hz i
      rw [hD', hD] at hzi
      simp only [hsum, Matrix.cons_val, Fin.isValue]
      linear_combination hzi
    · intro n' hn'
      have h0 := congrFun hn' 0
      have h4 := congrFun hn' 4
      have h2 := congrFun hn' 2
      simp only [hsum] at h0 h4 h2
      have e0 : n' 0 = x 0 - x 4 := by
        linear_combination -h0 + h4 - hcp0 - n' 0 * f5 - n' 1 * k5
      have s1 : x 2 - x 4 = t0 - ρ * n' 0 + 508 * (4619990760 * r + 1) ^ 2 * n' 1 := by
        linear_combination h2 - h4 + hcp2 + n' 0 * f6 + n' 1 * k6
      have s2 : x 2 - x 4 - t0 + ρ * (x 0 - x 4) = 508 * (4619990760 * r + 1) ^ 2 * n1 := by
        have hh := hn1
        simp only [hD] at hh
        linear_combination hh + hcp2 + (x 0 - x 4) * f6
      have e1 : n' 1 = n1 := by
        have : 508 * (4619990760 * r + 1) ^ 2 * n' 1 = 508 * (4619990760 * r + 1) ^ 2 * n1 := by linear_combination s2 - s1 + ρ * e0
        exact mul_left_cancel₀ hNpos.ne' this
      funext j
      fin_cases j
      · simpa using e0
      · simpa using e1
  · simp only [hLL0, hLL1]
    rw [f5, k6, k5, f6]
    rw [show (15 * 1 * (31 * (508 * (4619990760 * r + 1) ^ 2)) - 15 * 0 * (31 * -ρ) : ℤ) = 465 * (4619990760 * r + 1) ^ 2 * 508 by ring,
      abs_of_nonneg (by positivity)]
    norm_num
  · have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hZ1 : (1 : ℝ) ≤ Z := by linarith
    have hQR : (1 : ℝ) ≤ (((4619990760 * r + 1) : ℤ) : ℝ) := by rw [hqR]; exact hq1
    have hNR : ((508 * (4619990760 * r + 1) ^ 2 : ℤ) : ℝ) = 508 * (q : ℝ) ^ 2 := by rw [← hqR]; push_cast; ring
    have hN0 : (0 : ℝ) ≤ ((508 * (4619990760 * r + 1) ^ 2 : ℤ) : ℝ) := by rw [hNR]; positivity
    have hN1 : (1 : ℝ) ≤ ((508 * (4619990760 * r + 1) ^ 2 : ℤ) : ℝ) := by rw [hNR]; nlinarith
    have hqZ0 : (0 : ℝ) ≤ (q : ℝ) * Z ^ 2 := by positivity
    have hqZ1 : (0 : ℝ) ≤ (q : ℝ) * Z := by positivity
    have hAR0 : (0 : ℝ) ≤ ((4619990760 * a : ℤ) : ℝ) := by linarith
    have hAR : ((4619990760 * a : ℤ) : ℝ) ≤ 2 * (((4619990760 * r + 1) : ℤ) : ℝ) * Z ^ 2 := by rw [hqR]; linarith
    have hBR0 : (0 : ℝ) ≤ ((4619990760 * b : ℤ) : ℝ) := by linarith
    have hBR : ((4619990760 * b : ℤ) : ℝ) ≤ 2 * (((4619990760 * r + 1) : ℤ) : ℝ) * Z := by rw [hqR]; linarith
    have hCR0 : (0 : ℝ) ≤ ((4619990760 * c : ℤ) : ℝ) := by linarith
    have hCR : ((4619990760 * c : ℤ) : ℝ) ≤ 2 * (((4619990760 * r + 1) : ℤ) : ℝ) * Z := by rw [hqR]; linarith
    have hfin : ∀ y : ℝ, y ≤ 10 ^ 6 * Z ^ 2 * (((508 * (4619990760 * r + 1) ^ 2 : ℤ) : ℝ) + 1) →
        y ≤ 10 ^ 9 * Z ^ 2 * (q : ℝ) ^ 2 := by
      intro y hy
      rw [hNR] at hy
      have hq2 : (1 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
      nlinarith [mul_nonneg (sq_nonneg Z) (show (0 : ℝ) ≤ 492 * 10 ^ 6 * (q : ℝ) ^ 2 - 10 ^ 6 by nlinarith)]
    have Bc := lc_bound (((4619990760 * r + 1) : ℤ) : ℝ) ((4619990760 * a : ℤ) : ℝ) ((4619990760 * b : ℤ) : ℝ) ((4619990760 * c : ℤ) : ℝ) Z
      ((508 * (4619990760 * r + 1) ^ 2 : ℤ) : ℝ) 1 (cc 0) (cc 1) (cc 2) (cc 3) (cc 4) (cc 5) hQR hZ1 hAR0 hAR hBR0 hBR hCR0 hCR
      hN0 (by norm_num) le_rfl
      (by rw [show (cc 0 : ℝ) - cc 4 = 0 by exact_mod_cast hcp0, abs_zero]; exact hN0)
      (by rw [show (cc 2 : ℝ) - cc 4 = (t0 : ℝ) by exact_mod_cast hcp2,
            abs_of_nonneg (by exact_mod_cast ht00)]; exact_mod_cast ht0N.le)
      (by exact_mod_cast hc1) (by exact_mod_cast hc2) (by exact_mod_cast hc3)
      (by rw [mul_one]; exact_mod_cast hc4)
    have B0 := lc_bound (((4619990760 * r + 1) : ℤ) : ℝ) ((4619990760 * a : ℤ) : ℝ) ((4619990760 * b : ℤ) : ℝ) ((4619990760 * c : ℤ) : ℝ) Z
      ((508 * (4619990760 * r + 1) ^ 2 : ℤ) : ℝ) 0 (L0 0) (L0 1) (L0 2) (L0 3) (L0 4) (L0 5) hQR hZ1 hAR0 hAR hBR0 hBR hCR0 hCR
      hN0 le_rfl (by norm_num)
      (by rw [show (L0 0 : ℝ) - L0 4 = 1 by exact_mod_cast f5, abs_one]; exact hN1)
      (by rw [show (L0 2 : ℝ) - L0 4 = -(ρ : ℝ) by exact_mod_cast f6, abs_neg,
            abs_of_nonneg (by exact_mod_cast hρ0)]; exact_mod_cast hρN.le)
      (by exact_mod_cast f1) (by exact_mod_cast f2) (by rw [add_zero]; exact_mod_cast f3)
      (by rw [mul_zero, sub_zero]; exact_mod_cast f4)
    have B1 := lc_bound (((4619990760 * r + 1) : ℤ) : ℝ) ((4619990760 * a : ℤ) : ℝ) ((4619990760 * b : ℤ) : ℝ) ((4619990760 * c : ℤ) : ℝ) Z
      ((508 * (4619990760 * r + 1) ^ 2 : ℤ) : ℝ) 0 (L1 0) (L1 1) (L1 2) (L1 3) (L1 4) (L1 5) hQR hZ1 hAR0 hAR hBR0 hBR hCR0 hCR
      hN0 le_rfl (by norm_num)
      (by rw [show (L1 0 : ℝ) - L1 4 = 0 by exact_mod_cast k5, abs_zero]; exact hN0)
      (by rw [show (L1 2 : ℝ) - L1 4 = ((508 * (4619990760 * r + 1) ^ 2 : ℤ) : ℝ) by exact_mod_cast k6, abs_of_nonneg hN0])
      (by exact_mod_cast k1) (by exact_mod_cast k2) (by rw [add_zero]; exact_mod_cast k3)
      (by rw [mul_zero, sub_zero]; exact_mod_cast k4)
    have pick : ∀ (y : Fin 6 → ℤ), (|(y 0 : ℝ)| ≤ 10 ^ 6 * Z ^ 2 * (((508 * (4619990760 * r + 1) ^ 2 : ℤ) : ℝ) + 1) ∧
        |(y 1 : ℝ)| ≤ 10 ^ 6 * Z ^ 2 * (((508 * (4619990760 * r + 1) ^ 2 : ℤ) : ℝ) + 1) ∧
        |(y 2 : ℝ)| ≤ 10 ^ 6 * Z ^ 2 * (((508 * (4619990760 * r + 1) ^ 2 : ℤ) : ℝ) + 1) ∧
        |(y 3 : ℝ)| ≤ 10 ^ 6 * Z ^ 2 * (((508 * (4619990760 * r + 1) ^ 2 : ℤ) : ℝ) + 1) ∧
        |(y 4 : ℝ)| ≤ 10 ^ 6 * Z ^ 2 * (((508 * (4619990760 * r + 1) ^ 2 : ℤ) : ℝ) + 1) ∧
        |(y 5 : ℝ)| ≤ 10 ^ 6 * Z ^ 2 * (((508 * (4619990760 * r + 1) ^ 2 : ℤ) : ℝ) + 1)) →
        ∀ i, |(y i : ℝ)| ≤ 10 ^ 9 * Z ^ 2 * (q : ℝ) ^ 2 := by
      rintro y ⟨y0, y1, y2, y3, y4, y5⟩ i
      apply hfin
      fin_cases i
      · exact y0
      · exact y1
      · exact y2
      · exact y3
      · exact y4
      · exact y5
    intro i
    refine ⟨pick cc Bc i, ?_⟩
    intro j
    fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, hLL0]; exact pick L0 B0 i
    · simp only [Fin.mk_one, Fin.isValue, hLL1]; exact pick L1 B1 i
  · intro K hK
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hT2 : (2 : ℝ) ≤ T := by nlinarith
    have hT0 : (0 : ℝ) < T := by linarith
    have hNR : ((508 * (4619990760 * r + 1) ^ 2 : ℤ) : ℝ) = 508 * (q : ℝ) ^ 2 := by rw [← hqR]; push_cast; ring
    have hN1 : (1 : ℝ) ≤ ((508 * (4619990760 * r + 1) ^ 2 : ℤ) : ℝ) := by rw [hNR]; nlinarith
    have hK' : ∀ v, v ∈ K ↔ (-2 * T ≤ 15 * v 0 ∧ 15 * v 0 ≤ -T ∧
        |31 * ((t0 : ℝ) - (ρ : ℝ) * v 0 + ((508 * (4619990760 * r + 1) ^ 2 : ℤ) : ℝ) * v 1)| ≤ 1 / 100000 * |15 * v 0|) := by
      intro v
      rw [hK v]
      have r0 : ((cc 0 : ℝ) + ∑ j, (LL 0 j : ℝ) * v j) - ((cc 4 : ℝ) + ∑ j, (LL 4 j : ℝ) * v j) = v 0 := by
        rw [Fin.sum_univ_two, Fin.sum_univ_two, hLL0, hLL0, hLL1, hLL1]
        have a1 : (cc 0 : ℝ) - cc 4 = 0 := by exact_mod_cast hcp0
        have a2 : (L0 0 : ℝ) - L0 4 = 1 := by exact_mod_cast f5
        have a3 : (L1 0 : ℝ) - L1 4 = 0 := by exact_mod_cast k5
        linear_combination a1 + v 0 * a2 + v 1 * a3
      have r2 : ((cc 2 : ℝ) + ∑ j, (LL 2 j : ℝ) * v j) - ((cc 4 : ℝ) + ∑ j, (LL 4 j : ℝ) * v j) =
          (t0 : ℝ) - (ρ : ℝ) * v 0 + ((508 * (4619990760 * r + 1) ^ 2 : ℤ) : ℝ) * v 1 := by
        rw [Fin.sum_univ_two, Fin.sum_univ_two, hLL0, hLL0, hLL1, hLL1]
        have a1 : (cc 2 : ℝ) - cc 4 = t0 := by exact_mod_cast hcp2
        have a2 : (L0 2 : ℝ) - L0 4 = -ρ := by exact_mod_cast f6
        have a3 : (L1 2 : ℝ) - L1 4 = ((508 * (4619990760 * r + 1) ^ 2 : ℤ) : ℝ) := by exact_mod_cast k6
        linear_combination a1 + v 0 * a2 + v 1 * a3
      rw [r0, r2]
    refine ⟨lc_convex T _ _ _ hT0 K hK', ?_,
      lc_bounded T _ _ _ hT2 hN1 (by exact_mod_cast hρ0) (by exact_mod_cast hρN.le)
        (by exact_mod_cast ht00) (by exact_mod_cast ht0N.le) K hK'⟩
    rw [lc_volume T _ _ _ hT0 (by linarith) K hK', hNR]
    congr 1
    push_cast
    ring

-- N24 region_bounds_int [assembly]
set_option maxHeartbeats 400000 in
theorem region_bounds_int (OnPl : ℤ → ℤ → ℤ → ℤ → (Fin 6 → ℤ) → Prop)
    (hOnPl : ∀ q A B C (x : Fin 6 → ℤ), OnPl q A B C x ↔
      (q * (x 1 - x 4) = 31 * A * (x 2 - x 4) + 462 * B * x 4 ∧
       q * (x 3 - x 4) = -15 * A * (x 0 - x 4) + 462 * C * x 4 ∧
       q * (x 4 + 1) = -(15 * B * (x 0 - x 4) + 31 * C * (x 2 - x 4)) ∧
       508 * x 5 = 15 * (x 0 + x 1) + 31 * (x 2 + x 3) - 508 * x 4 - 462))
    (InReg : ℝ → (Fin 6 → ℤ) → Prop)
    (hInReg : ∀ T (x : Fin 6 → ℤ), InReg T x ↔
      (-2 * T ≤ 15 * ((x 0 : ℝ) - x 4) ∧ 15 * ((x 0 : ℝ) - x 4) ≤ -T ∧
       |31 * ((x 2 : ℝ) - x 4)| ≤ 1 / 100000 * |15 * ((x 0 : ℝ) - x 4)|)) :
    ∃ cl Cu ch Ch : ℝ, 0 < cl ∧ 0 < ch ∧ ch < Ch ∧ ∀ (q : ℕ) (A B C : ℤ) (Z T : ℝ) (x : Fin 6 → ℤ),
      1 ≤ q → 100 ≤ Z → 10 ≤ T →
      (q : ℝ) * Z ^ 2 ≤ A → (A : ℝ) ≤ 2 * q * Z ^ 2 → (q : ℝ) * Z ≤ B → (B : ℝ) ≤ 2 * q * Z →
      (q : ℝ) * Z ≤ C → (C : ℝ) ≤ 2 * q * Z → OnPl q A B C x → InReg T x →
      (cl * Z * T ≤ x 0 ∧ cl * Z * T ≤ x 2 ∧ cl * Z * T ≤ x 4 ∧
       cl * Z ^ 2 * T ≤ x 1 ∧ cl * Z ^ 2 * T ≤ x 3 ∧ cl * Z ^ 2 * T ≤ x 5 ∧
       (∀ i, (x i : ℝ) ≤ Cu * Z ^ 2 * T) ∧
       ch * Z ^ 3 * T ^ 2 ≤ 508 * (x 4 : ℝ) * x 5 ∧ 508 * (x 4 : ℝ) * x 5 ≤ Ch * Z ^ 3 * T ^ 2) := by
  obtain ⟨c₀, C₀, hc₀, hcC, hbnd⟩ := archimedean_bounds
  refine ⟨c₀, C₀, 508 * c₀ ^ 2, 508 * C₀ ^ 2, hc₀, by positivity, by nlinarith, ?_⟩
  intro q A B C Z T x hq hZ hT hA1 hA2 hB1 hB2 hC1 hC2 hx hreg
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq' : (q : ℤ) ≠ 0 := by omega
  have hq0' : (0 : ℝ) < ((q : ℤ) : ℝ) := by exact_mod_cast hq
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := integral_lift OnPl hOnPl q A B C x hq' hx
    (A / ((q : ℤ) : ℝ)) (B / ((q : ℤ) : ℝ)) (C / ((q : ℤ) : ℝ))
    (15 * ((x 0 : ℝ) - x 4)) (31 * ((x 2 : ℝ) - x 4)) rfl rfl rfl rfl rfl
  rw [hInReg] at hreg
  obtain ⟨hr1, hr2, hs⟩ := hreg
  have hqq : ((q : ℤ) : ℝ) = (q : ℝ) := Int.cast_natCast q
  have hα1 : Z ^ 2 ≤ (A : ℝ) / ((q : ℤ) : ℝ) := by rw [le_div_iff₀ hq0', hqq]; linarith
  have hα2 : (A : ℝ) / ((q : ℤ) : ℝ) ≤ 2 * Z ^ 2 := by rw [div_le_iff₀ hq0', hqq]; linarith
  have hβ1 : Z ≤ (B : ℝ) / ((q : ℤ) : ℝ) := by rw [le_div_iff₀ hq0', hqq]; linarith
  have hβ2 : (B : ℝ) / ((q : ℤ) : ℝ) ≤ 2 * Z := by rw [div_le_iff₀ hq0', hqq]; linarith
  have hγ1 : Z ≤ (C : ℝ) / ((q : ℤ) : ℝ) := by rw [le_div_iff₀ hq0', hqq]; linarith
  have hγ2 : (C : ℝ) / ((q : ℤ) : ℝ) ≤ 2 * Z := by rw [div_le_iff₀ hq0', hqq]; linarith
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ :=
    hbnd Z T _ _ _ _ _ (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) hZ hT hα1 hα2 hβ1 hβ2 hγ1 hγ2 hr1 hr2 hs
      h0 h1 h2 h3 h4 h5
  have hZ0 : 0 < Z := by linarith
  have hT0 : 0 < T := by linarith
  have hZT : Z * T ≤ Z ^ 2 * T := by nlinarith
  have hx4pos : 0 ≤ c₀ * Z * T := mul_nonneg (mul_nonneg hc₀.le hZ0.le) hT0.le
  have hx5pos : 0 ≤ c₀ * Z ^ 2 * T := mul_nonneg (mul_nonneg hc₀.le (sq_nonneg Z)) hT0.le
  have hC0 : 0 ≤ C₀ := by linarith
  have hCZT : 0 ≤ C₀ * Z ^ 2 * T := mul_nonneg (mul_nonneg hC0 (sq_nonneg Z)) hT0.le
  have hCZ : C₀ * (Z * T) ≤ C₀ * (Z ^ 2 * T) := mul_le_mul_of_nonneg_left hZT hC0
  have hlo := mul_le_mul b5 b11 hx5pos (le_trans hx4pos b5)
  have hCZT' : 0 ≤ C₀ * Z * T := mul_nonneg (mul_nonneg hC0 hZ0.le) hT0.le
  have hhi := mul_le_mul b6 b12 (le_trans hx5pos b11) hCZT'
  refine ⟨b1, b3, b5, b7, b9, b11, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> linarith
  · calc 508 * c₀ ^ 2 * Z ^ 3 * T ^ 2 = 508 * (c₀ * Z * T * (c₀ * Z ^ 2 * T)) := by ring
      _ ≤ 508 * ((x 4 : ℝ) * x 5) := by gcongr
      _ = 508 * (x 4 : ℝ) * x 5 := by ring
  · calc 508 * (x 4 : ℝ) * x 5 = 508 * ((x 4 : ℝ) * x 5) := by ring
      _ ≤ 508 * (C₀ * Z * T * (C₀ * Z ^ 2 * T)) := by gcongr
      _ = 508 * C₀ ^ 2 * Z ^ 3 * T ^ 2 := by ring

-- N25 helper
lemma sq_class_card (K L m : ℕ) (hm : 0 < m) (S : Finset ℕ) (hS : S ⊆ Finset.Ico K (K + L))
    (hmod : ∀ x ∈ S, ∀ y ∈ S, x % m = y % m) : S.card ≤ L / m + 1 := by
  calc S.card ≤ (Finset.range (L / m + 1)).card := by
        apply Finset.card_le_card_of_injOn (fun k => (k - K) / m)
        · intro k hk
          have hk' := Finset.mem_Ico.mp (hS hk)
          simp only [Finset.coe_range, Set.mem_Iio]
          have : (k - K) / m ≤ L / m := Nat.div_le_div_right (by omega)
          omega
        · intro x hx y hy hxy
          have hxy' : (x - K) / m = (y - K) / m := hxy
          have hx' := Finset.mem_Ico.mp (hS hx)
          have hy' := Finset.mem_Ico.mp (hS hy)
          have hmxy := hmod x hx y hy
          have h1 : (x - K) % m = (y - K) % m := by
            have e : (K + (x - K)) % m = (K + (y - K)) % m := by
              rw [Nat.add_sub_cancel' hx'.1, Nat.add_sub_cancel' hy'.1]; exact hmxy
            exact Nat.ModEq.add_left_cancel' K e
          have h2 := Nat.div_add_mod (x - K) m
          have h3 := Nat.div_add_mod (y - K) m
          rw [hxy', h1] at h2
          omega
    _ = L / m + 1 := Finset.card_range _

-- N25 sqfree_progression_count [extremal_averaging]
theorem sqfree_progression_count : ∃ csf Q1 : ℝ, 0 < csf ∧ ∀ Q : ℝ, Q1 ≤ Q →
    ∃ F : Finset ℕ, (∀ q ∈ F, Q ≤ q ∧ (q : ℝ) ≤ 2 * Q ∧ q % 4619990760 = 1 ∧ Squarefree q) ∧ csf * Q ≤ F.card := by
  -- Route: q = 1 + W k with k ∈ [K, 2K - 2), K = ⌈Q⌉/W + 1; the non-squarefree ones have p² ∣ 1 + W k for a prime
  -- 13 ≤ p ≤ √N, p ∤ W, a single class of k mod p², so at most L/p² + 1 of them; ∑ 1/p² ≤ 2/13.
  refine ⟨1 / (10 * 4619990760), 10 ^ 30, by norm_num, ?_⟩
  intro Q hQ
  have hQ0 : 0 < Q := by linarith [show (0 : ℝ) < 10 ^ 30 by norm_num]
  set n := ⌈Q⌉₊ with hn
  have hnQ : Q ≤ (n : ℝ) := Nat.le_ceil Q
  have hnQ1 : (n : ℝ) < Q + 1 := Nat.ceil_lt_add_one hQ0.le
  have hn30 : 10 ^ 30 ≤ n := by exact_mod_cast hQ.trans hnQ
  set K := n / 4619990760 + 1 with hK
  set L := K - 2 with hL
  set N := 1 + 4619990760 * (K + L) with hN
  set M := Nat.sqrt N with hM
  set G := Finset.Ico K (K + L) with hG
  set P := (Finset.range (M + 1)).filter (fun p => p.Prime ∧ 13 ≤ p ∧ ¬ p ∣ 4619990760) with hP
  have hK1 : n < 4619990760 * K := by omega
  have hK2 : 4619990760 * K ≤ n + 4619990760 := by omega
  have hK3 : 2 ≤ K := by omega
  refine ⟨(G.filter (fun k => Squarefree (1 + 4619990760 * k))).image (fun k => 1 + 4619990760 * k), ?_, ?_⟩
  · intro q hq
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hkG, hsq⟩ := Finset.mem_filter.mp hk
    have hk' := Finset.mem_Ico.mp hkG
    have h1 : n ≤ 1 + 4619990760 * k := by omega
    have h2 : 1 + 4619990760 * k + 4619990760 ≤ 2 * n + 1 := by omega
    have h1' : (n : ℝ) ≤ ((1 + 4619990760 * k : ℕ) : ℝ) := by exact_mod_cast h1
    have h2' : ((1 + 4619990760 * k : ℕ) : ℝ) + 4619990760 ≤ 2 * n + 1 := by exact_mod_cast h2
    refine ⟨by linarith, by linarith, by omega, hsq⟩
  · have hinj : Function.Injective (fun k : ℕ => 1 + 4619990760 * k) := by
      intro a b h
      have h' : 1 + 4619990760 * a = 1 + 4619990760 * b := h
      omega
    rw [Finset.card_image_of_injective _ hinj]
    have hsplit := Finset.card_filter_add_card_filter_not (s := G) (fun k => Squarefree (1 + 4619990760 * k))
    have hGc : G.card = L := by rw [hG, Nat.card_Ico]; omega
    -- the bad set lies in a union of single residue classes
    have hsub : G.filter (fun k => ¬ Squarefree (1 + 4619990760 * k)) ⊆
        P.biUnion (fun p => G.filter (fun k => p * p ∣ 1 + 4619990760 * k)) := by
      intro k hk
      obtain ⟨hkG, hns⟩ := Finset.mem_filter.mp hk
      have hk' := Finset.mem_Ico.mp hkG
      rw [Nat.squarefree_iff_prime_squarefree] at hns
      push_neg at hns
      obtain ⟨p, hpr, hpd⟩ := hns
      have hp : p.Prime := hpr
      have hpd1 : p ∣ 1 + 4619990760 * k := (dvd_mul_right p p).trans hpd
      have hpW : ¬ p ∣ 4619990760 := by
        intro h
        have hpd2 : p ∣ 4619990760 * k + 1 := by rwa [add_comm] at hpd1
        have h3 : p ∣ 1 := (Nat.dvd_add_right (dvd_mul_of_dvd_left h k)).mp hpd2
        exact hp.one_lt.ne' (Nat.dvd_one.mp h3)
      have h13 : 13 ≤ p := by
        by_contra h
        push_neg at h
        interval_cases p <;> (revert hp hpW; norm_num)
      have hpM : p ≤ M := by
        rw [hM, Nat.le_sqrt]
        exact le_trans (Nat.le_of_dvd (by omega) hpd) (by omega)
      refine Finset.mem_biUnion.mpr ⟨p, ?_, Finset.mem_filter.mpr ⟨hkG, hpd⟩⟩
      rw [hP, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hp, h13, hpW⟩
    have hfib : ∀ p ∈ P, (G.filter (fun k => p * p ∣ 1 + 4619990760 * k)).card ≤ L / (p * p) + 1 := by
      intro p hpP
      rw [hP, Finset.mem_filter] at hpP
      obtain ⟨-, hp, -, hpW⟩ := hpP
      have hcop : Nat.Coprime (p * p) 4619990760 :=
        Nat.coprime_mul_iff_left.mpr ⟨(Nat.Prime.coprime_iff_not_dvd hp).mpr hpW,
          (Nat.Prime.coprime_iff_not_dvd hp).mpr hpW⟩
      apply sq_class_card K L (p * p) (Nat.mul_pos hp.pos hp.pos) _ (Finset.filter_subset _ _)
      intro x hx y hy
      have hx2 := (Finset.mem_filter.mp hx).2
      have hy2 := (Finset.mem_filter.mp hy).2
      have e1 : 1 + 4619990760 * x ≡ 1 + 4619990760 * y [MOD p * p] :=
        (Nat.modEq_zero_iff_dvd.mpr hx2).trans (Nat.modEq_zero_iff_dvd.mpr hy2).symm
      exact Nat.ModEq.cancel_left_of_coprime hcop (Nat.ModEq.add_left_cancel' 1 e1)
    have hbadN : (G.filter (fun k => ¬ Squarefree (1 + 4619990760 * k))).card ≤
        ∑ p ∈ P, (L / (p * p) + 1) :=
      (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans (Finset.sum_le_sum hfib))
    have hPc : P.card ≤ M + 1 := (Finset.card_filter_le _ _).trans (by rw [Finset.card_range])
    have hsum : ∑ p ∈ P, ((p : ℝ) ^ 2)⁻¹ ≤ 2 / 13 := by
      calc ∑ p ∈ P, ((p : ℝ) ^ 2)⁻¹ ≤ ∑ i ∈ Finset.Ioo 12 (M + 1), ((i : ℝ) ^ 2)⁻¹ := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro p hp
              rw [hP, Finset.mem_filter, Finset.mem_range] at hp
              rw [Finset.mem_Ioo]
              omega
            · intro i _ _; positivity
        _ ≤ 2 / ((12 : ℕ) + 1) := sum_Ioo_inv_sq_le 12 (M + 1)
        _ = 2 / 13 := by norm_num
    have hbadR : ((G.filter (fun k => ¬ Squarefree (1 + 4619990760 * k))).card : ℝ) ≤
        2 / 13 * L + (M + 1) := by
      have h1 : ((G.filter (fun k => ¬ Squarefree (1 + 4619990760 * k))).card : ℝ) ≤
          ∑ p ∈ P, (((L / (p * p) : ℕ) : ℝ) + 1) := by
        have := (Nat.cast_le (α := ℝ)).mpr hbadN
        push_cast at this
        exact this
      have h2 : ∑ p ∈ P, (((L / (p * p) : ℕ) : ℝ) + 1) ≤ ∑ p ∈ P, ((L : ℝ) * ((p : ℝ) ^ 2)⁻¹ + 1) := by
        apply Finset.sum_le_sum
        intro p _
        have : ((L / (p * p) : ℕ) : ℝ) ≤ (L : ℝ) / ((p * p : ℕ) : ℝ) := Nat.cast_div_le
        have e : (L : ℝ) / ((p * p : ℕ) : ℝ) = (L : ℝ) * ((p : ℝ) ^ 2)⁻¹ := by push_cast; ring
        linarith
      have h3 : ∑ p ∈ P, ((L : ℝ) * ((p : ℝ) ^ 2)⁻¹ + 1) = (L : ℝ) * ∑ p ∈ P, ((p : ℝ) ^ 2)⁻¹ + P.card := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one]
      have hPc' : (P.card : ℝ) ≤ M + 1 := by exact_mod_cast hPc
      have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
      have h4 : (L : ℝ) * ∑ p ∈ P, ((p : ℝ) ^ 2)⁻¹ ≤ L * (2 / 13) := mul_le_mul_of_nonneg_left hsum hL0
      linarith
    -- sizes
    have hsplitR : ((G.filter (fun k => Squarefree (1 + 4619990760 * k))).card : ℝ) +
        ((G.filter (fun k => ¬ Squarefree (1 + 4619990760 * k))).card : ℝ) = L := by
      rw [← hGc]; exact_mod_cast hsplit
    have hKR : Q ≤ 4619990760 * (K : ℝ) := by
      have : (n : ℝ) < ((4619990760 * K : ℕ) : ℝ) := by exact_mod_cast hK1
      push_cast at this; linarith
    have hLK : L + 2 = K := by omega
    have hLR : (L : ℝ) + 2 = K := by exact_mod_cast hLK
    have hNle : N ≤ 2 * n + 2 * 4619990760 + 1 := by omega
    have hMM : M * M ≤ N := Nat.sqrt_le N
    have hMMR : (M : ℝ) * M ≤ 3 * Q := by
      have h1 : ((M * M : ℕ) : ℝ) ≤ ((2 * n + 2 * 4619990760 + 1 : ℕ) : ℝ) := by exact_mod_cast hMM.trans hNle
      push_cast at h1
      linarith
    have hMR : (M : ℝ) * (100 * 4619990760) ≤ Q := by
      by_contra h
      push_neg at h
      have h1 : Q * Q < ((M : ℝ) * (100 * 4619990760)) * ((M : ℝ) * (100 * 4619990760)) :=
        mul_self_lt_mul_self hQ0.le h
      have h2 : ((M : ℝ) * (100 * 4619990760)) * ((M : ℝ) * (100 * 4619990760)) ≤
          3 * Q * (100 * 4619990760) ^ 2 := by
        have := mul_le_mul_of_nonneg_right hMMR (by positivity : (0 : ℝ) ≤ (100 * 4619990760) ^ 2)
        calc ((M : ℝ) * (100 * 4619990760)) * ((M : ℝ) * (100 * 4619990760))
            = ((M : ℝ) * M) * (100 * 4619990760) ^ 2 := by ring
          _ ≤ _ := this
      have h3 : 3 * Q * (100 * 4619990760) ^ 2 ≤ Q * Q := by
        have h4 : 3 * (100 * 4619990760 : ℝ) ^ 2 ≤ Q := by norm_num; linarith
        have := mul_le_mul_of_nonneg_right h4 hQ0.le
        linarith
      linarith
    set y := Q / 4619990760 with hy
    have hyQ : Q = 4619990760 * y := by rw [hy]; field_simp
    have hy100 : 100 ≤ y := by rw [hy, le_div_iff₀ (by norm_num)]; linarith
    have hLy : y - 2 ≤ (L : ℝ) := by linarith
    have hMy : (M : ℝ) ≤ y / 100 := by linarith
    have hcsf : 1 / (10 * 4619990760) * Q = y / 10 := by rw [hyQ]; field_simp
    rw [hcsf]
    clear_value y
    linarith

-- N26 H_sum_bound [extremal_averaging]
theorem H_sum_bound : ∃ CH Q1 : ℝ, ∀ Q : ℝ, Q1 ≤ Q →
    ∑ q ∈ (Finset.Icc ⌈Q⌉₊ ⌊2 * Q⌋₊).filter (fun q => q % 4619990760 = 1),
      ∑ p ∈ q.primeFactors, (1 : ℝ) / p ≤ CH * Q := by
  refine ⟨2, 1, ?_⟩
  intro Q hQ
  have hQ0 : 0 < Q := by linarith
  set S := (Finset.Icc ⌈Q⌉₊ ⌊2 * Q⌋₊).filter (fun q => q % 4619990760 = 1) with hS
  set N := ⌊2 * Q⌋₊ with hN
  set P := (Finset.range (N + 1)).filter Nat.Prime with hP
  have hceil : 0 < ⌈Q⌉₊ := Nat.ceil_pos.mpr hQ0
  have hsub : ∀ q ∈ S, q.primeFactors ⊆ P := by
    intro q hq p hp
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at hq
    rw [Nat.mem_primeFactors] at hp
    rw [hP, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le ((Nat.le_of_dvd (Nat.pos_of_ne_zero hp.2.2) hp.2.1).trans hq.1.2), hp.1⟩
  have step1 : ∑ q ∈ S, ∑ p ∈ q.primeFactors, (1 : ℝ) / p =
      ∑ q ∈ S, ∑ p ∈ P, (if p ∣ q then (1 : ℝ) / p else 0) := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext p
    rw [Finset.mem_filter, Nat.mem_primeFactors]
    constructor
    · intro h
      exact ⟨hsub q hq (Nat.mem_primeFactors.mpr h), h.2.1⟩
    · rintro ⟨hpP, hpq⟩
      rw [hP, Finset.mem_filter] at hpP
      have hq0 : q ≠ 0 := by
        rw [hS, Finset.mem_filter, Finset.mem_Icc] at hq
        omega
      exact ⟨hpP.2, hpq, hq0⟩
  have step2 : ∑ q ∈ S, ∑ p ∈ P, (if p ∣ q then (1 : ℝ) / p else 0) =
      ∑ p ∈ P, (1 : ℝ) / p * ((S.filter (fun q => p ∣ q)).card : ℝ) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have step3 : ∀ p ∈ P, ((S.filter (fun q => p ∣ q)).card : ℝ) ≤ 2 * Q / p := by
    intro p hp
    rw [hP, Finset.mem_filter] at hp
    have hcard : (S.filter (fun q => p ∣ q)).card ≤ N / p := by
      rw [← Nat.Ioc_filter_dvd_card_eq_div]
      apply Finset.card_le_card
      intro q hq
      rw [Finset.mem_filter] at hq ⊢
      rw [hS, Finset.mem_filter, Finset.mem_Icc] at hq
      exact ⟨Finset.mem_Ioc.mpr ⟨by omega, hq.1.1.2⟩, hq.2⟩
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.2.pos
    calc ((S.filter (fun q => p ∣ q)).card : ℝ) ≤ ((N / p : ℕ) : ℝ) := by exact_mod_cast hcard
      _ ≤ (N : ℝ) / p := Nat.cast_div_le
      _ ≤ 2 * Q / p := by
        gcongr
        exact Nat.floor_le (by linarith)
  have hsum2 : ∑ p ∈ P, (1 : ℝ) / p * (2 * Q / p) ≤ 2 * Q := by
    have e : ∑ p ∈ P, (1 : ℝ) / p * (2 * Q / p) = 2 * Q * ∑ p ∈ P, ((p : ℝ) ^ 2)⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    rw [e]
    have h1 : ∑ p ∈ P, ((p : ℝ) ^ 2)⁻¹ ≤ ∑ i ∈ Finset.Ioo 1 (N + 1), ((i : ℝ) ^ 2)⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        rw [hP, Finset.mem_filter, Finset.mem_range] at hp
        rw [Finset.mem_Ioo]
        exact ⟨hp.2.one_lt, hp.1⟩
      · intros
        positivity
    have h2 : ∑ i ∈ Finset.Ioo 1 (N + 1), ((i : ℝ) ^ 2)⁻¹ ≤ 2 / ((1 : ℕ) + 1) := sum_Ioo_inv_sq_le 1 (N + 1)
    have h3 : ∑ p ∈ P, ((p : ℝ) ^ 2)⁻¹ ≤ 1 := by
      have : (2 : ℝ) / ((1 : ℕ) + 1) = 1 := by norm_num
      linarith
    nlinarith
  rw [step1, step2]
  calc ∑ p ∈ P, (1 : ℝ) / p * ((S.filter (fun q => p ∣ q)).card : ℝ)
      ≤ ∑ p ∈ P, (1 : ℝ) / p * (2 * Q / p) := by
        apply Finset.sum_le_sum
        intro p hp
        have hp0 : (0 : ℝ) < p := by
          rw [hP, Finset.mem_filter] at hp
          exact_mod_cast hp.2.pos
        exact mul_le_mul_of_nonneg_left (step3 p hp) (by positivity)
    _ ≤ 2 * Q := hsum2

-- N27 good_denominators [extremal_averaging]
theorem good_denominators : ∃ M0 cW Q0 : ℝ, 0 < cW ∧ ∀ Q : ℝ, Q0 ≤ Q →
    ∃ F : Finset ℕ, (∀ q ∈ F, Q ≤ q ∧ (q : ℝ) ≤ 2 * Q ∧ q % 4619990760 = 1 ∧ Squarefree q ∧
      ∑ p ∈ q.primeFactors, (1 : ℝ) / p ≤ M0) ∧ cW * Q ≤ F.card := by
  obtain ⟨csf, Q1, hcsf, hF⟩ := sqfree_progression_count
  obtain ⟨CH, Q2, hH⟩ := H_sum_bound
  have hmax : 0 < max CH 1 := by positivity
  set M0 := 2 * max CH 1 / csf with hM0
  have hM0pos : 0 < M0 := by positivity
  refine ⟨M0, csf / 2, max Q1 (max Q2 1), by positivity, ?_⟩
  intro Q hQ
  have hQ1 : Q1 ≤ Q := le_trans (le_max_left _ _) hQ
  have hQ2 : Q2 ≤ Q := le_trans (le_max_of_le_right (le_max_left _ _)) hQ
  have hQ3 : 1 ≤ Q := le_trans (le_max_of_le_right (le_max_right _ _)) hQ
  obtain ⟨F0, hF0, hcard⟩ := hF Q hQ1
  have hsum := hH Q hQ2
  refine ⟨F0.filter (fun q : ℕ => ∑ p ∈ q.primeFactors, (1 : ℝ) / p ≤ M0), ?_, ?_⟩
  · intro q hq
    rw [Finset.mem_filter] at hq
    obtain ⟨h1, h2, h3, h4⟩ := hF0 q hq.1
    exact ⟨h1, h2, h3, h4, hq.2⟩
  · set Bad := F0.filter (fun q : ℕ => ¬ ∑ p ∈ q.primeFactors, (1 : ℝ) / p ≤ M0) with hBad
    have hsplit : (F0.filter (fun q : ℕ => ∑ p ∈ q.primeFactors, (1 : ℝ) / p ≤ M0)).card + Bad.card
        = F0.card := Finset.card_filter_add_card_filter_not _
    have hBadsub : Bad ⊆ (Finset.Icc ⌈Q⌉₊ ⌊2 * Q⌋₊).filter (fun q => q % 4619990760 = 1) := by
      intro q hq
      rw [Finset.mem_filter] at hq ⊢
      obtain ⟨h1, h2, h3, -⟩ := hF0 q hq.1
      exact ⟨Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr h1, Nat.le_floor h2⟩, h3⟩
    have h1 : M0 * Bad.card ≤ ∑ q ∈ Bad, ∑ p ∈ q.primeFactors, (1 : ℝ) / p := by
      calc M0 * Bad.card = ∑ q ∈ Bad, M0 := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        _ ≤ ∑ q ∈ Bad, ∑ p ∈ q.primeFactors, (1 : ℝ) / p := by
          apply Finset.sum_le_sum
          intro q hq
          rw [Finset.mem_filter] at hq
          exact le_of_lt (not_le.mp hq.2)
    have h2 : ∑ q ∈ Bad, ∑ p ∈ q.primeFactors, (1 : ℝ) / p ≤
        ∑ q ∈ (Finset.Icc ⌈Q⌉₊ ⌊2 * Q⌋₊).filter (fun q => q % 4619990760 = 1),
          ∑ p ∈ q.primeFactors, (1 : ℝ) / p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hBadsub
      intro q _ _
      positivity
    have hCH : CH * Q ≤ max CH 1 * Q := mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
    have h4 : 2 * max CH 1 / csf * Bad.card ≤ max CH 1 * Q := by rw [← hM0]; linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ hcsf] at h4
    have h5 : 2 * max CH 1 * (Bad.card : ℝ) ≤ 2 * max CH 1 * (csf * Q / 2) := by linarith
    have hBadle : (Bad.card : ℝ) ≤ csf * Q / 2 := le_of_mul_le_mul_left h5 (by positivity)
    have hsplit' : (F0.card : ℝ) =
        ((F0.filter (fun q : ℕ => ∑ p ∈ q.primeFactors, (1 : ℝ) / p ≤ M0)).card : ℝ) + Bad.card := by
      exact_mod_cast hsplit.symm
    linarith

-- N28 residue_blocks [extremal_averaging]
theorem residue_blocks (m : ℕ) [NeZero m] (Ω : Finset (ZMod m × ZMod m × ZMod m))
    (a1 a2 a3 : ℤ) (L1 L2 L3 : ℕ) :
    Ω.card * ((L1 / m - 1) * (L2 / m - 1) * (L3 / m - 1)) ≤
      ((Finset.Ico a1 (a1 + L1) ×ˢ (Finset.Ico a2 (a2 + L2) ×ˢ Finset.Ico a3 (a3 + L3))).filter
        (fun x => ((x.1 : ZMod m), (x.2.1 : ZMod m), (x.2.2 : ZMod m)) ∈ Ω)).card := by
  classical
  -- Each residue class mod m occurs at least L/m times in an interval of length L, so the box contains at
  -- least ⌊L1/m⌋⌊L2/m⌋⌊L3/m⌋ points over each residue triple in Ω. Injection:
  -- (ω, k1, k2, k3) ↦ (a1 + ((ω1 - a1) mod m) + m k1, …) from Ω × range(L1/m-1) × range(L2/m-1) × range(L3/m-1).
  have hm : (0 : ℤ) < m := by exact_mod_cast (NeZero.pos m)
  let lift : ℤ → ZMod m → ℕ → ℤ := fun a ω k => a + ((ω.val : ℤ) - a) % m + m * k
  have lift_mem : ∀ (a : ℤ) (ω : ZMod m) (L k : ℕ), k < L / m - 1 → lift a ω k ∈ Finset.Ico a (a + L) := by
    intro a ω L k hk
    simp only [lift, Finset.mem_Ico]
    have h1 := Int.emod_nonneg ((ω.val : ℤ) - a) hm.ne'
    have h2 := Int.emod_lt_of_pos ((ω.val : ℤ) - a) hm
    have h3 : (k : ℤ) + 1 ≤ ((L / m : ℕ) : ℤ) := by
      have : k + 1 ≤ L / m := by omega
      exact_mod_cast this
    have h4 : ((L / m : ℕ) : ℤ) * m ≤ L := by
      have := Nat.div_mul_le_self L m
      exact_mod_cast this
    have h5 : (m : ℤ) * ((k : ℤ) + 1) ≤ (m : ℤ) * ((L / m : ℕ) : ℤ) := mul_le_mul_of_nonneg_left h3 hm.le
    have hk0 : (0 : ℤ) ≤ (m : ℤ) * k := by positivity
    constructor
    · linarith
    · linarith
  have lift_res : ∀ (a : ℤ) (ω : ZMod m) (k : ℕ), ((lift a ω k : ℤ) : ZMod m) = ω := by
    intro a ω k
    simp only [lift]
    push_cast
    simp [ZMod.natCast_self, ZMod.natCast_zmod_val]
  have hinj_coord : ∀ (a : ℤ) (ω ω' : ZMod m) (k k' : ℕ), lift a ω k = lift a ω' k' → ω = ω' ∧ k = k' := by
    intro a ω ω' k k' h
    have hres : ω = ω' := by rw [← lift_res a ω k, h, lift_res]
    subst hres
    refine ⟨rfl, ?_⟩
    simp only [lift] at h
    have h' : (m : ℤ) * k = m * k' := by linarith
    have := mul_left_cancel₀ hm.ne' h'
    exact_mod_cast this
  calc Ω.card * ((L1 / m - 1) * (L2 / m - 1) * (L3 / m - 1))
      = (Ω ×ˢ (Finset.range (L1 / m - 1) ×ˢ
          (Finset.range (L2 / m - 1) ×ˢ Finset.range (L3 / m - 1)))).card := by
        simp only [Finset.card_product, Finset.card_range]; ring
    _ ≤ _ := by
        apply Finset.card_le_card_of_injOn
          (fun ωk => (lift a1 ωk.1.1 ωk.2.1, lift a2 ωk.1.2.1 ωk.2.2.1, lift a3 ωk.1.2.2 ωk.2.2.2))
        · intro ωk hωk
          simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hωk
          obtain ⟨hΩ, hk1, hk2, hk3⟩ := hωk
          simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product]
          refine ⟨⟨lift_mem _ _ _ _ hk1, lift_mem _ _ _ _ hk2, lift_mem _ _ _ _ hk3⟩, ?_⟩
          simp only [lift_res]
          exact hΩ
        · intro x _ y _ hxy
          simp only [Prod.mk.injEq] at hxy
          obtain ⟨h1, h2, h3⟩ := hxy
          obtain ⟨e1, f1⟩ := hinj_coord _ _ _ _ _ h1
          obtain ⟨e2, f2⟩ := hinj_coord _ _ _ _ _ h2
          obtain ⟨e3, f3⟩ := hinj_coord _ _ _ _ _ h3
          ext <;> assumption

-- N29 helper
lemma ld_exp_le (y : ℝ) (h0 : 0 ≤ y) (h1 : y ≤ 1 / 2) : Real.exp (-(2 * y)) ≤ 1 - y := by
  have h2 : 1 + 2 * y ≤ Real.exp (2 * y) := by have := Real.add_one_le_exp (2 * y); linarith
  have h3 : 0 < 1 + 2 * y := by linarith
  rw [Real.exp_neg]
  calc (Real.exp (2 * y))⁻¹ ≤ (1 + 2 * y)⁻¹ := inv_anti₀ h3 h2
    _ ≤ 1 - y := by
      rw [← one_div, div_le_iff₀ h3]
      nlinarith

-- N29 helper
lemma ld_card_le_of_injOn {α β : Type*} [Fintype β] (S : Finset α) (f : α → β) (hf : Set.InjOn f S) :
    S.card ≤ Fintype.card β := by
  have := Finset.card_le_card_of_injOn (t := Finset.univ) f
    (by intro x _; exact Finset.mem_coe.mpr (Finset.mem_univ _)) hf
  simpa using this

-- N29 helper
lemma ld_ge13 (p : ℕ) (hp : p.Prime) (hpW : ¬ p ∣ 4619990760) : 13 ≤ p := by
  by_contra h
  push_neg at h
  interval_cases p <;> (revert hp hpW; norm_num)

-- N29 helper
lemma ld_unit (p n : ℕ) (hn : n ∣ 4619990760) (hpW : ¬ p ∣ 4619990760) : ((n : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact fun h => hpW (h.trans hn)

-- N29 helper
lemma ld_count_q (p : ℕ) [hp : Fact p.Prime] (hpW : ¬ p ∣ 4619990760) :
    (p : ℝ) ^ 3 * Real.exp (-(12 / p)) ≤ ((Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p =>
      (4619990760 * x.1) * (4619990760 * x.2.1) * (4619990760 * x.2.2) *
        (462 * (4619990760 * x.2.2) + 15 * (4619990760 * x.1)) *
        (31 * (4619990760 * x.1) - 462 * (4619990760 * x.2.1)) *
        (15 * (4619990760 * x.2.1) + 31 * (4619990760 * x.2.2)) ≠ 0)).card : ℝ) := by
  have h13 := ld_ge13 p hp.out hpW
  have hw : (4619990760 : ZMod p) ≠ 0 := by exact_mod_cast ld_unit p 4619990760 dvd_rfl hpW
  have h462 : (462 : ZMod p) ≠ 0 := by exact_mod_cast ld_unit p 462 (by norm_num) hpW
  have h31 : (31 : ZMod p) ≠ 0 := by exact_mod_cast ld_unit p 31 (by norm_num) hpW
  have hc2 : Fintype.card (ZMod p × ZMod p) = p ^ 2 := by rw [Fintype.card_prod, ZMod.card]; ring
  have b1 : (Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p => x.1 = 0)).card ≤ p ^ 2 := by
    rw [← hc2]
    apply ld_card_le_of_injOn _ (fun x : ZMod p × ZMod p × ZMod p => (x.2.1, x.2.2))
    rintro ⟨a, b, c⟩ hx ⟨a', b', c'⟩ hy hxy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at hx hy hxy
    obtain ⟨rfl, rfl⟩ := hxy
    rw [hx, hy]
  have b2 : (Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p => x.2.1 = 0)).card ≤ p ^ 2 := by
    rw [← hc2]
    apply ld_card_le_of_injOn _ (fun x : ZMod p × ZMod p × ZMod p => (x.1, x.2.2))
    rintro ⟨a, b, c⟩ hx ⟨a', b', c'⟩ hy hxy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at hx hy hxy
    obtain ⟨rfl, rfl⟩ := hxy
    rw [hx, hy]
  have b3 : (Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p => x.2.2 = 0)).card ≤ p ^ 2 := by
    rw [← hc2]
    apply ld_card_le_of_injOn _ (fun x : ZMod p × ZMod p × ZMod p => (x.1, x.2.1))
    rintro ⟨a, b, c⟩ hx ⟨a', b', c'⟩ hy hxy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at hx hy hxy
    obtain ⟨rfl, rfl⟩ := hxy
    rw [hx, hy]
  have b4 : (Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p => 462 * x.2.2 + 15 * x.1 = 0)).card ≤
      p ^ 2 := by
    rw [← hc2]
    apply ld_card_le_of_injOn _ (fun x : ZMod p × ZMod p × ZMod p => (x.1, x.2.1))
    rintro ⟨a, b, c⟩ hx ⟨a', b', c'⟩ hy hxy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at hx hy hxy
    obtain ⟨rfl, rfl⟩ := hxy
    have : c = c' := mul_left_cancel₀ h462 (by linear_combination hx - hy)
    rw [this]
  have b5 : (Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p => 31 * x.1 - 462 * x.2.1 = 0)).card ≤
      p ^ 2 := by
    rw [← hc2]
    apply ld_card_le_of_injOn _ (fun x : ZMod p × ZMod p × ZMod p => (x.1, x.2.2))
    rintro ⟨a, b, c⟩ hx ⟨a', b', c'⟩ hy hxy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at hx hy hxy
    obtain ⟨rfl, rfl⟩ := hxy
    have : b = b' := mul_left_cancel₀ h462 (by linear_combination hy - hx)
    rw [this]
  have b6 : (Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p => 15 * x.2.1 + 31 * x.2.2 = 0)).card ≤
      p ^ 2 := by
    rw [← hc2]
    apply ld_card_le_of_injOn _ (fun x : ZMod p × ZMod p × ZMod p => (x.1, x.2.1))
    rintro ⟨a, b, c⟩ hx ⟨a', b', c'⟩ hy hxy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at hx hy hxy
    obtain ⟨rfl, rfl⟩ := hxy
    have : c = c' := mul_left_cancel₀ h31 (by linear_combination hx - hy)
    rw [this]
  have hsub : Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p =>
      ¬ ((4619990760 * x.1) * (4619990760 * x.2.1) * (4619990760 * x.2.2) *
        (462 * (4619990760 * x.2.2) + 15 * (4619990760 * x.1)) *
        (31 * (4619990760 * x.1) - 462 * (4619990760 * x.2.1)) *
        (15 * (4619990760 * x.2.1) + 31 * (4619990760 * x.2.2)) ≠ 0)) ⊆
      Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p => x.1 = 0) ∪
      Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p => x.2.1 = 0) ∪
      Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p => x.2.2 = 0) ∪
      Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p => 462 * x.2.2 + 15 * x.1 = 0) ∪
      Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p => 31 * x.1 - 462 * x.2.1 = 0) ∪
      Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p => 15 * x.2.1 + 31 * x.2.2 = 0) := by
    rintro ⟨a, b, c⟩ hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hx
    have h' : a * b * c * (462 * c + 15 * a) * (31 * a - 462 * b) * (15 * b + 31 * c) = 0 := by
      have e : (4619990760 : ZMod p) ^ 6 *
          (a * b * c * (462 * c + 15 * a) * (31 * a - 462 * b) * (15 * b + 31 * c)) = 0 := by
        linear_combination hx
      exact (mul_eq_zero.mp e).resolve_left (pow_ne_zero _ hw)
    simp only [mul_eq_zero] at h'
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hbad := Finset.card_le_card hsub
  have u1 := Finset.card_union_le
    (Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p => x.1 = 0) ∪
      Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p => x.2.1 = 0) ∪
      Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p => x.2.2 = 0) ∪
      Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p => 462 * x.2.2 + 15 * x.1 = 0) ∪
      Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p => 31 * x.1 - 462 * x.2.1 = 0))
    (Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p => 15 * x.2.1 + 31 * x.2.2 = 0))
  have u2 := Finset.card_union_le
    (Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p => x.1 = 0) ∪
      Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p => x.2.1 = 0) ∪
      Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p => x.2.2 = 0) ∪
      Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p => 462 * x.2.2 + 15 * x.1 = 0))
    (Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p => 31 * x.1 - 462 * x.2.1 = 0))
  have u3 := Finset.card_union_le
    (Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p => x.1 = 0) ∪
      Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p => x.2.1 = 0) ∪
      Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p => x.2.2 = 0))
    (Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p => 462 * x.2.2 + 15 * x.1 = 0))
  have u4 := Finset.card_union_le
    (Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p => x.1 = 0) ∪
      Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p => x.2.1 = 0))
    (Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p => x.2.2 = 0))
  have u5 := Finset.card_union_le
    (Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p => x.1 = 0))
    (Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p => x.2.1 = 0))
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (ZMod p × ZMod p × ZMod p)))
    (fun x : ZMod p × ZMod p × ZMod p =>
      (4619990760 * x.1) * (4619990760 * x.2.1) * (4619990760 * x.2.2) *
        (462 * (4619990760 * x.2.2) + 15 * (4619990760 * x.1)) *
        (31 * (4619990760 * x.1) - 462 * (4619990760 * x.2.1)) *
        (15 * (4619990760 * x.2.1) + 31 * (4619990760 * x.2.2)) ≠ 0)
  have hU : (Finset.univ : Finset (ZMod p × ZMod p × ZMod p)).card = p ^ 3 := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_prod, ZMod.card]; ring
  rw [hU] at hsplit
  set G := (Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p =>
      (4619990760 * x.1) * (4619990760 * x.2.1) * (4619990760 * x.2.2) *
        (462 * (4619990760 * x.2.2) + 15 * (4619990760 * x.1)) *
        (31 * (4619990760 * x.1) - 462 * (4619990760 * x.2.1)) *
        (15 * (4619990760 * x.2.1) + 31 * (4619990760 * x.2.2)) ≠ 0)).card with hG
  have hGn : p ^ 3 ≤ G + 6 * p ^ 2 := by omega
  have hGr : (p : ℝ) ^ 3 ≤ G + 6 * (p : ℝ) ^ 2 := by exact_mod_cast hGn
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp13 : (13 : ℝ) ≤ p := by exact_mod_cast h13
  have hy : Real.exp (-(2 * (6 / (p : ℝ)))) ≤ 1 - 6 / p :=
    ld_exp_le _ (by positivity) (by rw [div_le_iff₀ hp0]; linarith)
  have e2 : -(12 / (p : ℝ)) = -(2 * (6 / (p : ℝ))) := by ring
  rw [e2]
  calc (p : ℝ) ^ 3 * Real.exp (-(2 * (6 / (p : ℝ)))) ≤ (p : ℝ) ^ 3 * (1 - 6 / p) :=
        mul_le_mul_of_nonneg_left hy (by positivity)
    _ = (p : ℝ) ^ 3 - 6 * (p : ℝ) ^ 2 := by
        have : (p : ℝ) ^ 3 * (6 / p) = 6 * (p : ℝ) ^ 2 := by
          rw [mul_div_assoc', div_eq_iff hp0.ne']; ring
        rw [mul_sub, mul_one, this]
    _ ≤ G := by linarith

-- N29 helper
lemma ld_count_P (p : ℕ) [hp : Fact p.Prime] (hpW : ¬ p ∣ 4619990760) (qz : ZMod p) :
    (p : ℝ) ^ 3 * Real.exp (-(6 / (p : ℝ) ^ 2)) ≤ ((Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p =>
      ¬ ((4619990760 * x.1 = 0 ∧ 462 * (4619990760 * x.2.1) + qz = 0) ∨
         (4619990760 * x.1 = 0 ∧ 462 * (4619990760 * x.2.2) + qz = 0) ∨
         (31 * (4619990760 * x.1) - 462 * (4619990760 * x.2.1) - qz = 0 ∧
          15 * (4619990760 * x.1) + 462 * (4619990760 * x.2.2) + qz = 0)))).card : ℝ) := by
  have h13 := ld_ge13 p hp.out hpW
  have hw : (4619990760 : ZMod p) ≠ 0 := by exact_mod_cast ld_unit p 4619990760 dvd_rfl hpW
  have h462 : (462 : ZMod p) ≠ 0 := by exact_mod_cast ld_unit p 462 (by norm_num) hpW
  have h462w : (462 : ZMod p) * 4619990760 ≠ 0 := mul_ne_zero h462 hw
  have hc1 : Fintype.card (ZMod p) = p := ZMod.card p
  have b1 : (Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p =>
      4619990760 * x.1 = 0 ∧ 462 * (4619990760 * x.2.1) + qz = 0)).card ≤ p := by
    refine le_trans (ld_card_le_of_injOn _ (fun x : ZMod p × ZMod p × ZMod p => x.2.2) ?_) hc1.le
    rintro ⟨a, b, c⟩ hx ⟨a', b', c'⟩ hy hxy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy hxy
    subst hxy
    have ha : a = 0 := (mul_eq_zero.mp hx.1).resolve_left hw
    have ha' : a' = 0 := (mul_eq_zero.mp hy.1).resolve_left hw
    have hb : b = b' := mul_left_cancel₀ h462w (by linear_combination hx.2 - hy.2)
    rw [ha, ha', hb]
  have b2 : (Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p =>
      4619990760 * x.1 = 0 ∧ 462 * (4619990760 * x.2.2) + qz = 0)).card ≤ p := by
    refine le_trans (ld_card_le_of_injOn _ (fun x : ZMod p × ZMod p × ZMod p => x.2.1) ?_) hc1.le
    rintro ⟨a, b, c⟩ hx ⟨a', b', c'⟩ hy hxy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy hxy
    subst hxy
    have ha : a = 0 := (mul_eq_zero.mp hx.1).resolve_left hw
    have ha' : a' = 0 := (mul_eq_zero.mp hy.1).resolve_left hw
    have hc : c = c' := mul_left_cancel₀ h462w (by linear_combination hx.2 - hy.2)
    rw [ha, ha', hc]
  have b3 : (Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p =>
      31 * (4619990760 * x.1) - 462 * (4619990760 * x.2.1) - qz = 0 ∧
      15 * (4619990760 * x.1) + 462 * (4619990760 * x.2.2) + qz = 0)).card ≤ p := by
    refine le_trans (ld_card_le_of_injOn _ (fun x : ZMod p × ZMod p × ZMod p => x.1) ?_) hc1.le
    rintro ⟨a, b, c⟩ hx ⟨a', b', c'⟩ hy hxy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy hxy
    subst hxy
    have hb : b = b' := mul_left_cancel₀ h462w (by linear_combination hy.1 - hx.1)
    have hc : c = c' := mul_left_cancel₀ h462w (by linear_combination hx.2 - hy.2)
    rw [hb, hc]
  have hsub : Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p =>
      ¬ ¬ ((4619990760 * x.1 = 0 ∧ 462 * (4619990760 * x.2.1) + qz = 0) ∨
         (4619990760 * x.1 = 0 ∧ 462 * (4619990760 * x.2.2) + qz = 0) ∨
         (31 * (4619990760 * x.1) - 462 * (4619990760 * x.2.1) - qz = 0 ∧
          15 * (4619990760 * x.1) + 462 * (4619990760 * x.2.2) + qz = 0))) ⊆
      Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p =>
        4619990760 * x.1 = 0 ∧ 462 * (4619990760 * x.2.1) + qz = 0) ∪
      Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p =>
        4619990760 * x.1 = 0 ∧ 462 * (4619990760 * x.2.2) + qz = 0) ∪
      Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p =>
        31 * (4619990760 * x.1) - 462 * (4619990760 * x.2.1) - qz = 0 ∧
        15 * (4619990760 * x.1) + 462 * (4619990760 * x.2.2) + qz = 0) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hx
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hbad := Finset.card_le_card hsub
  have u1 := Finset.card_union_le
    (Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p =>
        4619990760 * x.1 = 0 ∧ 462 * (4619990760 * x.2.1) + qz = 0) ∪
      Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p =>
        4619990760 * x.1 = 0 ∧ 462 * (4619990760 * x.2.2) + qz = 0))
    (Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p =>
        31 * (4619990760 * x.1) - 462 * (4619990760 * x.2.1) - qz = 0 ∧
        15 * (4619990760 * x.1) + 462 * (4619990760 * x.2.2) + qz = 0))
  have u2 := Finset.card_union_le
    (Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p =>
        4619990760 * x.1 = 0 ∧ 462 * (4619990760 * x.2.1) + qz = 0))
    (Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p =>
        4619990760 * x.1 = 0 ∧ 462 * (4619990760 * x.2.2) + qz = 0))
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (ZMod p × ZMod p × ZMod p)))
    (fun x : ZMod p × ZMod p × ZMod p =>
      ¬ ((4619990760 * x.1 = 0 ∧ 462 * (4619990760 * x.2.1) + qz = 0) ∨
         (4619990760 * x.1 = 0 ∧ 462 * (4619990760 * x.2.2) + qz = 0) ∨
         (31 * (4619990760 * x.1) - 462 * (4619990760 * x.2.1) - qz = 0 ∧
          15 * (4619990760 * x.1) + 462 * (4619990760 * x.2.2) + qz = 0)))
  have hU : (Finset.univ : Finset (ZMod p × ZMod p × ZMod p)).card = p ^ 3 := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_prod, ZMod.card]; ring
  rw [hU] at hsplit
  set G := (Finset.univ.filter (fun x : ZMod p × ZMod p × ZMod p =>
      ¬ ((4619990760 * x.1 = 0 ∧ 462 * (4619990760 * x.2.1) + qz = 0) ∨
         (4619990760 * x.1 = 0 ∧ 462 * (4619990760 * x.2.2) + qz = 0) ∨
         (31 * (4619990760 * x.1) - 462 * (4619990760 * x.2.1) - qz = 0 ∧
          15 * (4619990760 * x.1) + 462 * (4619990760 * x.2.2) + qz = 0)))).card with hG
  have hGn : p ^ 3 ≤ G + 3 * p := by omega
  have hGr : (p : ℝ) ^ 3 ≤ G + 3 * (p : ℝ) := by exact_mod_cast hGn
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp13 : (13 : ℝ) ≤ p := by exact_mod_cast h13
  have hy : Real.exp (-(2 * (3 / (p : ℝ) ^ 2))) ≤ 1 - 3 / (p : ℝ) ^ 2 :=
    ld_exp_le _ (by positivity) (by rw [div_le_iff₀ (by positivity)]; nlinarith)
  have e2 : -(6 / (p : ℝ) ^ 2) = -(2 * (3 / (p : ℝ) ^ 2)) := by ring
  rw [e2]
  calc (p : ℝ) ^ 3 * Real.exp (-(2 * (3 / (p : ℝ) ^ 2))) ≤ (p : ℝ) ^ 3 * (1 - 3 / (p : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hy (by positivity)
    _ = (p : ℝ) ^ 3 - 3 * (p : ℝ) := by
        have : (p : ℝ) ^ 3 * (3 / (p : ℝ) ^ 2) = 3 * (p : ℝ) := by
          rw [mul_div_assoc', div_eq_iff (pow_ne_zero 2 hp0.ne')]; ring
        rw [mul_sub, mul_one, this]
    _ ≤ G := by linarith

-- N29 local_density [case_split]
theorem local_density (M0 : ℝ) : ∃ ϑ : ℝ, 0 < ϑ ∧ ∀ (q P m : ℕ), Squarefree q → q % 4619990760 = 1 →
    ∑ p ∈ q.primeFactors, (1 : ℝ) / p ≤ M0 →
    m = q * ∏ p ∈ (Finset.range (P + 1)).filter (fun p => p.Prime ∧ ¬ p ∣ 4619990760 * q), p →
    ∃ Ω : Finset (ZMod m × ZMod m × ZMod m), ϑ * (m : ℝ) ^ 3 ≤ Ω.card ∧
      ∀ a b c : ℤ, ((a : ZMod m), (b : ZMod m), (c : ZMod m)) ∈ Ω →
        (∀ p : ℕ, p.Prime → p ∣ q →
          ¬ (p : ℤ) ∣ (4619990760 * a) * (4619990760 * b) * (4619990760 * c) *
            (462 * (4619990760 * c) + 15 * (4619990760 * a)) * (31 * (4619990760 * a) - 462 * (4619990760 * b)) *
            (15 * (4619990760 * b) + 31 * (4619990760 * c))) ∧
        (∀ p : ℕ, p.Prime → p ≤ P → ¬ p ∣ 4619990760 * q →
          ¬ (((p : ℤ) ∣ 4619990760 * a ∧ (p : ℤ) ∣ 462 * (4619990760 * b) + q) ∨
             ((p : ℤ) ∣ 4619990760 * a ∧ (p : ℤ) ∣ 462 * (4619990760 * c) + q) ∨
             ((p : ℤ) ∣ 31 * (4619990760 * a) - 462 * (4619990760 * b) - q ∧
              (p : ℤ) ∣ 15 * (4619990760 * a) + 462 * (4619990760 * c) + q))) := by
  -- Route: CRT. T = primes of q ∪ the primes ≤ P off Wq; ZMod m ≃ Π_{p ∈ T} ZMod p (ZMod.prodEquivPi);
  -- Ω = preimage of the product of the local good sets; local counts p³ e^{-12/p} (p ∣ q) and p³ e^{-6/p²}.
  refine ⟨Real.exp (-(12 * M0 + 1)), Real.exp_pos _, ?_⟩
  intro q P m hsq hqW hH hm
  set S := (Finset.range (P + 1)).filter (fun p => p.Prime ∧ ¬ p ∣ 4619990760 * q) with hS
  set T := q.primeFactors ∪ S with hT
  have hq0 : q ≠ 0 := by rintro rfl; simp at hqW
  have hqpW : ∀ p, p.Prime → p ∣ q → ¬ p ∣ 4619990760 := by
    intro p hp hpq hpW
    have h1 : p ∣ q % 4619990760 := (Nat.dvd_mod_iff hpW).mpr hpq
    rw [hqW] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hdisj : Disjoint q.primeFactors S := by
    rw [Finset.disjoint_left]
    intro p hp hpS
    rw [hS, Finset.mem_filter] at hpS
    exact hpS.2.2 (dvd_mul_of_dvd_right (Nat.dvd_of_mem_primeFactors hp) _)
  have hTprime : ∀ p ∈ T, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact Nat.prime_of_mem_primeFactors h
    · exact (Finset.mem_filter.mp h).2.1
  have hTW : ∀ p ∈ T, ¬ p ∣ 4619990760 := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact hqpW p (Nat.prime_of_mem_primeFactors h) (Nat.dvd_of_mem_primeFactors h)
    · exact fun hW => (Finset.mem_filter.mp h).2.2 (dvd_mul_of_dvd_left hW _)
  have hmT : m = ∏ p ∈ T, p := by
    rw [hm, hT, Finset.prod_union hdisj, Nat.prod_primeFactors_of_squarefree hsq]
  have hcop : Pairwise (Function.onFun Nat.Coprime fun i : T => (i : ℕ)) := by
    intro i j hij
    exact (Nat.coprime_primes (hTprime _ i.2) (hTprime _ j.2)).mpr (fun h => hij (Subtype.ext h))
  have hm' : m = ∏ i : T, (i : ℕ) := hmT.trans (Finset.prod_coe_sort T (fun p => p)).symm
  obtain ⟨e, he⟩ : ∃ e : ZMod m ≃+* ((i : T) → ZMod (i : ℕ)),
      ∀ (a : ℤ) (i : T), e (a : ZMod m) i = (a : ZMod (i : ℕ)) :=
    ⟨(ZMod.ringEquivCongr hm').trans (ZMod.prodEquivPi (fun i : T => (i : ℕ)) hcop),
      fun a i => by rw [map_intCast]; rfl⟩
  haveI hNZ : ∀ i : T, NeZero (i : ℕ) := fun i => ⟨(hTprime _ i.2).ne_zero⟩
  obtain ⟨E, hE⟩ : ∃ E : ZMod m × ZMod m × ZMod m ≃
      ((i : T) → ZMod (i : ℕ) × ZMod (i : ℕ) × ZMod (i : ℕ)),
      ∀ ω i, E ω i = (e ω.1 i, e ω.2.1 i, e ω.2.2 i) :=
    ⟨{ toFun := fun ω i => (e ω.1 i, e ω.2.1 i, e ω.2.2 i)
       invFun := fun f => (e.symm (fun i => (f i).1), e.symm (fun i => (f i).2.1),
         e.symm (fun i => (f i).2.2))
       left_inv := by intro ω; simp
       right_inv := by intro f; funext i; simp }, fun _ _ => rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : (i : T) → Finset (ZMod (i : ℕ) × ZMod (i : ℕ) × ZMod (i : ℕ)), ∀ i, G i =
      if (i : ℕ) ∣ q then Finset.univ.filter (fun x : ZMod (i : ℕ) × ZMod (i : ℕ) × ZMod (i : ℕ) =>
        (4619990760 * x.1) * (4619990760 * x.2.1) * (4619990760 * x.2.2) *
          (462 * (4619990760 * x.2.2) + 15 * (4619990760 * x.1)) *
          (31 * (4619990760 * x.1) - 462 * (4619990760 * x.2.1)) *
          (15 * (4619990760 * x.2.1) + 31 * (4619990760 * x.2.2)) ≠ 0)
      else Finset.univ.filter (fun x : ZMod (i : ℕ) × ZMod (i : ℕ) × ZMod (i : ℕ) =>
        ¬ ((4619990760 * x.1 = 0 ∧ 462 * (4619990760 * x.2.1) + (q : ZMod (i : ℕ)) = 0) ∨
           (4619990760 * x.1 = 0 ∧ 462 * (4619990760 * x.2.2) + (q : ZMod (i : ℕ)) = 0) ∨
           (31 * (4619990760 * x.1) - 462 * (4619990760 * x.2.1) - (q : ZMod (i : ℕ)) = 0 ∧
            15 * (4619990760 * x.1) + 462 * (4619990760 * x.2.2) + (q : ZMod (i : ℕ)) = 0))) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℕ → ℝ, ∀ p, y p = if p ∣ q then 12 / (p : ℝ) else 6 / (p : ℝ) ^ 2 :=
    ⟨_, fun _ => rfl⟩
  refine ⟨(Fintype.piFinset G).map E.symm.toEmbedding, ?_, ?_⟩
  · rw [Finset.card_map, Fintype.card_piFinset]
    push_cast
    have hb : ∀ i : T, ((i : ℕ) : ℝ) ^ 3 * Real.exp (-(y (i : ℕ))) ≤ ((G i).card : ℝ) := by
      intro i
      haveI : Fact (i : ℕ).Prime := ⟨hTprime _ i.2⟩
      rw [hy, hG i]
      split_ifs with h
      · exact ld_count_q _ (hTW _ i.2)
      · exact ld_count_P _ (hTW _ i.2) _
    have hprod : ∏ i : T, (((i : ℕ) : ℝ) ^ 3 * Real.exp (-(y (i : ℕ)))) ≤ ∏ i : T, ((G i).card : ℝ) :=
      Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ => hb i)
    have hsplit : ∏ i : T, (((i : ℕ) : ℝ) ^ 3 * Real.exp (-(y (i : ℕ)))) =
        (m : ℝ) ^ 3 * Real.exp (-(∑ i : T, y (i : ℕ))) := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow, ← Finset.sum_neg_distrib, Real.exp_sum]
      congr 1
      rw [hm']
      push_cast
      rfl
    have hsum : ∑ i : T, y (i : ℕ) ≤ 12 * M0 + 1 := by
      rw [Finset.sum_coe_sort T y, hT, Finset.sum_union hdisj]
      have h1 : ∑ p ∈ q.primeFactors, y p = 12 * ∑ p ∈ q.primeFactors, (1 : ℝ) / p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        rw [hy, if_pos (Nat.dvd_of_mem_primeFactors hp)]
        ring
      have h2 : ∑ p ∈ S, y p = 6 * ∑ p ∈ S, ((p : ℝ) ^ 2)⁻¹ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        have hpq : ¬ p ∣ q := fun h => (Finset.mem_filter.mp hp).2.2 (dvd_mul_of_dvd_right h _)
        rw [hy, if_neg hpq]
        ring
      have h3 : ∑ p ∈ S, ((p : ℝ) ^ 2)⁻¹ ≤ ∑ i ∈ Finset.Ioo 12 (P + 1), ((i : ℝ) ^ 2)⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          have hp' := Finset.mem_filter.mp hp
          have h13 := ld_ge13 p hp'.2.1 (fun hW => hp'.2.2 (dvd_mul_of_dvd_left hW _))
          have hpr := Finset.mem_range.mp hp'.1
          rw [Finset.mem_Ioo]
          omega
        · intro i _ _; positivity
      have h4 : ∑ i ∈ Finset.Ioo 12 (P + 1), ((i : ℝ) ^ 2)⁻¹ ≤ 2 / ((12 : ℕ) + 1) :=
        sum_Ioo_inv_sq_le 12 (P + 1)
      norm_num at h4
      rw [h1, h2]
      linarith
    have hm3 : (0 : ℝ) ≤ (m : ℝ) ^ 3 := by positivity
    calc Real.exp (-(12 * M0 + 1)) * (m : ℝ) ^ 3 ≤ (m : ℝ) ^ 3 * Real.exp (-(∑ i : T, y (i : ℕ))) := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hm3
      _ = ∏ i : T, (((i : ℕ) : ℝ) ^ 3 * Real.exp (-(y (i : ℕ)))) := hsplit.symm
      _ ≤ ∏ i : T, ((G i).card : ℝ) := hprod
  · intro a b c hmem
    rw [Finset.mem_map_equiv, Equiv.symm_symm, Fintype.mem_piFinset] at hmem
    refine ⟨?_, ?_⟩
    · intro p hp hpq
      have hpT : p ∈ T := Finset.mem_union_left _ (Nat.mem_primeFactors.mpr ⟨hp, hpq, hq0⟩)
      have h1 := hmem ⟨p, hpT⟩
      rw [hE, hG, if_pos (show ((⟨p, hpT⟩ : T) : ℕ) ∣ q from hpq)] at h1
      simp only [he, Finset.mem_filter, Finset.mem_univ, true_and] at h1
      intro hdvd
      apply h1
      have h2 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd
      push_cast at h2
      exact h2
    · intro p hp hpP hpWq
      have hpq : ¬ p ∣ q := fun h => hpWq (dvd_mul_of_dvd_right h _)
      have hpS : p ∈ S := by
        rw [hS, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hp, hpWq⟩
      have hpT : p ∈ T := Finset.mem_union_right _ hpS
      have h1 := hmem ⟨p, hpT⟩
      rw [hE, hG, if_neg (show ¬ ((⟨p, hpT⟩ : T) : ℕ) ∣ q from hpq)] at h1
      simp only [he, Finset.mem_filter, Finset.mem_univ, true_and] at h1
      intro hdvd
      apply h1
      simp only [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hdvd
      push_cast at hdvd
      exact hdvd

-- N30 helper
lemma lpt_class (u v p : ℤ) (hp : 0 < p) (huv : u ≤ v) (S : Finset ℤ) (hS : ∀ x ∈ S, u ≤ x ∧ x < v)
    (hmod : ∀ x ∈ S, ∀ y ∈ S, p ∣ x - y) : (S.card : ℝ) ≤ ((v - u : ℤ) : ℝ) / p + 1 := by
  have hcard : S.card ≤ (Finset.Ico (0 : ℤ) ((v - u) / p + 1)).card := by
    apply Finset.card_le_card_of_injOn (fun x => (x - u) / p)
    · intro x hx
      have h := hS x hx
      rw [Finset.coe_Ico, Set.mem_Ico]
      show 0 ≤ (x - u) / p ∧ (x - u) / p < (v - u) / p + 1
      constructor
      · exact Int.ediv_nonneg (by linarith) hp.le
      · have : (x - u) / p ≤ (v - u) / p := Int.ediv_le_ediv hp (by linarith)
        linarith
    · intro x hx y hy hxy
      have hxy' : (x - u) / p = (y - u) / p := hxy
      have h1 : (x - u) % p = (y - u) % p := by
        have : (x - u) ≡ (y - u) [ZMOD p] := Int.modEq_iff_dvd.mpr (by
          have := hmod y hy x hx
          have e : y - u - (x - u) = y - x := by ring
          rw [e]; exact this)
        exact this
      have e1 := Int.emod_add_mul_ediv (x - u) p
      have e2 := Int.emod_add_mul_ediv (y - u) p
      rw [hxy', h1] at e1
      linarith
  rw [Int.card_Ico] at hcard
  have hK : 0 ≤ (v - u) / p := Int.ediv_nonneg (by linarith) hp.le
  have h3 : (S.card : ℤ) ≤ (v - u) / p + 1 := by
    have : ((S.card : ℕ) : ℤ) ≤ (((v - u) / p + 1 - 0).toNat : ℤ) := by exact_mod_cast hcard
    rw [Int.toNat_of_nonneg (by linarith)] at this
    linarith
  have h4 : p * ((v - u) / p) ≤ v - u := by
    have := Int.emod_add_mul_ediv (v - u) p
    have := Int.emod_nonneg (v - u) hp.ne'
    linarith
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have h5 : (((v - u) / p : ℤ) : ℝ) ≤ ((v - u : ℤ) : ℝ) / p := by
    rw [le_div_iff₀ hpR]
    have : ((p * ((v - u) / p) : ℤ) : ℝ) ≤ ((v - u : ℤ) : ℝ) := by exact_mod_cast h4
    push_cast at this ⊢
    linarith
  have h6 : (S.card : ℝ) ≤ (((v - u) / p + 1 : ℤ) : ℝ) := by exact_mod_cast h3
  push_cast at h6
  linarith

-- N30 helper: 1 + log N ≤ 3 log(qZ)
lemma lpt_log (q Z : ℝ) (N : ℕ) (hq : 2 ≤ q) (hZ : 100 ≤ Z) (hN : (N : ℝ) ≤ 40 * q * Z ^ 2) (hN1 : 1 ≤ N) :
    1 + Real.log N ≤ 3 * Real.log (q * Z) := by
  have hq0 : 0 < q := by linarith
  have hZ0 : 0 < Z := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have h1 : Real.log N ≤ Real.log (40 * q * Z ^ 2) := Real.log_le_log hN0 hN
  have h2 : Real.log (40 * q * Z ^ 2) = Real.log 40 + Real.log q + 2 * Real.log Z := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
      Real.log_pow]
    push_cast; ring
  have h3 : Real.log (q * Z) = Real.log q + Real.log Z := Real.log_mul hq0.ne' hZ0.ne'
  have hlq : 0 ≤ Real.log q := Real.log_nonneg (by linarith)
  have h4 : 1 + Real.log 40 ≤ Real.log (q * Z) := by
    have he : Real.exp 1 ≤ 5 := by have := Real.exp_one_lt_d9; linarith
    have h5 : 1 ≤ Real.log 5 := by rw [Real.le_log_iff_exp_le (by norm_num)]; exact he
    have h6 : Real.log 200 = Real.log 40 + Real.log 5 := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
    have h8 : (2 : ℝ) * 100 ≤ q * Z := mul_le_mul hq hZ (by norm_num) (by linarith)
    have h7 : Real.log 200 ≤ Real.log (q * Z) := Real.log_le_log (by norm_num) (by linarith)
    linarith
  linarith

-- N30 large_prime_tail [extremal_averaging]
set_option maxHeartbeats 400000 in
theorem large_prime_tail : ∃ Ct : ℝ, ∀ (q P : ℕ) (Z : ℝ), 2 ≤ q → 100 ≤ Z → 1 ≤ P →
    ∀ F : Finset (ℤ × ℤ × ℤ), (∀ t ∈ F, (q : ℝ) * Z ^ 2 ≤ t.1 ∧ (t.1 : ℝ) < 2 * q * Z ^ 2 ∧
        (q : ℝ) * Z ≤ t.2.1 ∧ (t.2.1 : ℝ) < 2 * q * Z ∧ (q : ℝ) * Z ≤ t.2.2 ∧ (t.2.2 : ℝ) < 2 * q * Z ∧
        ∃ p : ℕ, p.Prime ∧ P < p ∧ ¬ p ∣ 4619990760 * q ∧
          (((p : ℤ) ∣ t.1 ∧ (p : ℤ) ∣ 462 * t.2.1 + q) ∨ ((p : ℤ) ∣ t.1 ∧ (p : ℤ) ∣ 462 * t.2.2 + q) ∨
           ((p : ℤ) ∣ 31 * t.1 - 462 * t.2.1 - q ∧ (p : ℤ) ∣ 15 * t.1 + 462 * t.2.2 + q))) →
      (F.card : ℝ) ≤ Ct * ((q : ℝ) ^ 3 * Z ^ 4 / P + (q : ℝ) ^ 2 * Z ^ 3 * Real.log (q * Z) + (q : ℝ) ^ 2 * Z ^ 4) := by
  -- Route: union over primes P < p ≤ 40 q Z² of the three bad systems; each is a product (or a fibred product
  -- over a) of single residue classes in intervals; ∑ 1/p² ≤ 2/P, ∑ 1/p ≤ 1 + log N ≤ 3 log(qZ), #p ≤ N.
  refine ⟨10 ^ 6, ?_⟩
  intro q P Z hq hZ hP F hF
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hPR : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hZ0 : 0 < Z := by linarith
  have hq0 : (0 : ℝ) < q := by linarith
  have hqZ : 0 < (q : ℝ) * Z := by positivity
  have hqZ2 : 0 < (q : ℝ) * Z ^ 2 := by positivity
  have hZ2 : 10000 ≤ Z ^ 2 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 100) hZ 2
    norm_num at this; linarith
  have hqZb : 200 ≤ (q : ℝ) * Z := by
    have := mul_le_mul hqR hZ (by norm_num) (by linarith); linarith
  have hqZ2b : 20000 ≤ (q : ℝ) * Z ^ 2 := by
    have := mul_le_mul hqR hZ2 (by norm_num) (by linarith); linarith
  have hZZ : (q : ℝ) * Z ≤ (q : ℝ) * Z ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ Z by linarith) hqZ.le
    have h2 : (q : ℝ) * Z * Z = (q : ℝ) * Z ^ 2 := by ring
    linarith
  set a0 : ℤ := ⌈(q : ℝ) * Z ^ 2⌉ with ha0
  set a1 : ℤ := ⌈2 * (q : ℝ) * Z ^ 2⌉ with ha1
  set b0 : ℤ := ⌈(q : ℝ) * Z⌉ with hb0
  set b1 : ℤ := ⌈2 * (q : ℝ) * Z⌉ with hb1
  set N : ℕ := ⌊40 * (q : ℝ) * Z ^ 2⌋₊ with hN
  set Pr := (Finset.Icc (P + 1) N).filter (fun p => p.Prime ∧ ¬ p ∣ 4619990760 * q) with hPr
  set IA := Finset.Ico a0 a1 with hIA
  set IB := Finset.Ico b0 b1 with hIB
  have ha0l : (q : ℝ) * Z ^ 2 ≤ a0 := Int.le_ceil _
  have ha0u : (a0 : ℝ) < (q : ℝ) * Z ^ 2 + 1 := Int.ceil_lt_add_one _
  have ha1l : 2 * (q : ℝ) * Z ^ 2 ≤ a1 := Int.le_ceil _
  have ha1u : (a1 : ℝ) < 2 * (q : ℝ) * Z ^ 2 + 1 := Int.ceil_lt_add_one _
  have hb0l : (q : ℝ) * Z ≤ b0 := Int.le_ceil _
  have hb0u : (b0 : ℝ) < (q : ℝ) * Z + 1 := Int.ceil_lt_add_one _
  have hb1l : 2 * (q : ℝ) * Z ≤ b1 := Int.le_ceil _
  have hb1u : (b1 : ℝ) < 2 * (q : ℝ) * Z + 1 := Int.ceil_lt_add_one _
  have hab : a0 ≤ a1 := by
    have : (a0 : ℝ) ≤ a1 := by linarith
    exact_mod_cast this
  have hbb : b0 ≤ b1 := by
    have : (b0 : ℝ) ≤ b1 := by linarith
    exact_mod_cast this
  set LA : ℝ := ((a1 - a0 : ℤ) : ℝ) with hLA
  set LB : ℝ := ((b1 - b0 : ℤ) : ℝ) with hLB
  have hLA0 : 0 ≤ LA := by rw [hLA]; push_cast; linarith [(show (a0 : ℝ) ≤ a1 by exact_mod_cast hab)]
  have hLB0 : 0 ≤ LB := by rw [hLB]; push_cast; linarith [(show (b0 : ℝ) ≤ b1 by exact_mod_cast hbb)]
  have hLA1 : LA ≤ 2 * (q : ℝ) * Z ^ 2 := by rw [hLA]; push_cast; linarith
  have hLB1 : LB ≤ 2 * (q : ℝ) * Z := by rw [hLB]; push_cast; linarith
  have hIAc : (IA.card : ℝ) = LA := by
    have : (IA.card : ℤ) = a1 - a0 := by rw [hIA, Int.card_Ico, Int.toNat_of_nonneg (by linarith)]
    rw [hLA, ← this]; push_cast; rfl
  have hIBc : (IB.card : ℝ) = LB := by
    have : (IB.card : ℤ) = b1 - b0 := by rw [hIB, Int.card_Ico, Int.toNat_of_nonneg (by linarith)]
    rw [hLB, ← this]; push_cast; rfl
  have hNle : (N : ℝ) ≤ 40 * (q : ℝ) * Z ^ 2 := Nat.floor_le (by positivity)
  have hN1 : 1 ≤ N := by
    rw [hN]; apply Nat.le_floor; push_cast; linarith
  -- every element of F is in one of the bad sets of some prime in Pr
  have hsub : F ⊆ Pr.biUnion (fun p =>
      (IA.filter (fun a => (p : ℤ) ∣ a)) ×ˢ ((IB.filter (fun b => (p : ℤ) ∣ 462 * b + q)) ×ˢ IB) ∪
      (IA.filter (fun a => (p : ℤ) ∣ a)) ×ˢ (IB ×ˢ (IB.filter (fun b => (p : ℤ) ∣ 462 * b + q))) ∪
      IA.biUnion (fun a => ({a} : Finset ℤ) ×ˢ ((IB.filter (fun b => (p : ℤ) ∣ 31 * a - 462 * b - q)) ×ˢ
        (IB.filter (fun c => (p : ℤ) ∣ 15 * a + 462 * c + q))))) := by
    rintro ⟨a, b, c⟩ ht
    obtain ⟨hA1, hA2, hB1, hB2, hC1, hC2, p, hp, hPp, hpWq, hbad⟩ := hF _ ht
    simp only at hA1 hA2 hB1 hB2 hC1 hC2 hbad
    have haI : a ∈ IA := Finset.mem_Ico.mpr ⟨Int.ceil_le.mpr hA1, Int.lt_ceil.mpr hA2⟩
    have hbI : b ∈ IB := Finset.mem_Ico.mpr ⟨Int.ceil_le.mpr hB1, Int.lt_ceil.mpr hB2⟩
    have hcI : c ∈ IB := Finset.mem_Ico.mpr ⟨Int.ceil_le.mpr hC1, Int.lt_ceil.mpr hC2⟩
    have hapos : (0 : ℝ) < a := by linarith
    have hcpos : (0 : ℝ) < c := by linarith
    have hpN : p ≤ N := by
      rw [hN]
      apply Nat.le_floor
      rcases hbad with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h1⟩
      · have h2 : (p : ℤ) ≤ a := Int.le_of_dvd (by exact_mod_cast hapos) h1
        have h3 : (p : ℝ) ≤ a := by exact_mod_cast h2
        linarith
      · have h2 : (p : ℤ) ≤ a := Int.le_of_dvd (by exact_mod_cast hapos) h1
        have h3 : (p : ℝ) ≤ a := by exact_mod_cast h2
        linarith
      · have hpos : (0 : ℤ) < 15 * a + 462 * c + q := by
          have : (0 : ℝ) < 15 * a + 462 * c + q := by linarith
          exact_mod_cast this
        have h2 : (p : ℤ) ≤ 15 * a + 462 * c + q := Int.le_of_dvd hpos h1
        have h3 : (p : ℝ) ≤ 15 * a + 462 * c + q := by exact_mod_cast h2
        have e1 : 100 * ((q : ℝ) * Z) ≤ (q : ℝ) * Z ^ 2 := by
          have h4 := mul_le_mul_of_nonneg_left hZ hqZ.le
          have h5 : (q : ℝ) * Z * Z = (q : ℝ) * Z ^ 2 := by ring
          linarith
        have e2 : (q : ℝ) * 10000 ≤ (q : ℝ) * Z ^ 2 := mul_le_mul_of_nonneg_left hZ2 hq0.le
        linarith
    rw [Finset.mem_biUnion]
    refine ⟨p, ?_, ?_⟩
    · rw [hPr, Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨by omega, hpN⟩, hp, hpWq⟩
    · rcases hbad with h | h | h
      · apply Finset.mem_union_left; apply Finset.mem_union_left
        simp only [Finset.mem_product, Finset.mem_filter]; exact ⟨⟨haI, h.1⟩, ⟨hbI, h.2⟩, hcI⟩
      · apply Finset.mem_union_left; apply Finset.mem_union_right
        simp only [Finset.mem_product, Finset.mem_filter]; exact ⟨⟨haI, h.1⟩, hbI, ⟨hcI, h.2⟩⟩
      · apply Finset.mem_union_right
        rw [Finset.mem_biUnion]
        refine ⟨a, haI, ?_⟩
        simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_singleton]
        exact ⟨trivial, ⟨hbI, h.1⟩, ⟨hcI, h.2⟩⟩
  -- per-prime bound
  have hper : ∀ p ∈ Pr, (((IA.filter (fun a => (p : ℤ) ∣ a)) ×ˢ ((IB.filter (fun b => (p : ℤ) ∣ 462 * b + q)) ×ˢ IB) ∪
      (IA.filter (fun a => (p : ℤ) ∣ a)) ×ˢ (IB ×ˢ (IB.filter (fun b => (p : ℤ) ∣ 462 * b + q))) ∪
      IA.biUnion (fun a => ({a} : Finset ℤ) ×ˢ ((IB.filter (fun b => (p : ℤ) ∣ 31 * a - 462 * b - q)) ×ˢ
        (IB.filter (fun c => (p : ℤ) ∣ 15 * a + 462 * c + q))))).card : ℝ) ≤
      3 * LA * LB ^ 2 * ((p : ℝ) ^ 2)⁻¹ + (4 * LA * LB + 2 * LB ^ 2) * (p : ℝ)⁻¹ + (2 * LB + LA) := by
    intro p hpP
    rw [hPr, Finset.mem_filter] at hpP
    obtain ⟨-, hp, hpWq⟩ := hpP
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have h462 : ¬ (p : ℤ) ∣ 462 := by
      intro h
      have h' : p ∣ 462 := by exact_mod_cast h
      exact hpWq (h'.trans (Dvd.dvd.mul_right (by norm_num : 462 ∣ 4619990760) q))
    have cl : ∀ x y : ℤ, (p : ℤ) ∣ 462 * (x - y) → (p : ℤ) ∣ x - y :=
      fun x y h => (hpZ.dvd_or_dvd h).resolve_left h462
    have cA : ((IA.filter (fun a => (p : ℤ) ∣ a)).card : ℝ) ≤ LA / p + 1 := by
      apply lpt_class a0 a1 p hp0 hab
      · intro x hx; exact Finset.mem_Ico.mp (Finset.mem_filter.mp hx).1
      · intro x hx y hy; exact dvd_sub (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
    have cB : ((IB.filter (fun b => (p : ℤ) ∣ 462 * b + q)).card : ℝ) ≤ LB / p + 1 := by
      apply lpt_class b0 b1 p hp0 hbb
      · intro x hx; exact Finset.mem_Ico.mp (Finset.mem_filter.mp hx).1
      · intro x hx y hy
        apply cl
        have := dvd_sub (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
        convert this using 1; ring
    have cB3 : ∀ a : ℤ, ((IB.filter (fun b => (p : ℤ) ∣ 31 * a - 462 * b - q)).card : ℝ) ≤ LB / p + 1 := by
      intro a
      apply lpt_class b0 b1 p hp0 hbb
      · intro x hx; exact Finset.mem_Ico.mp (Finset.mem_filter.mp hx).1
      · intro x hx y hy
        apply cl
        have := dvd_sub (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hx).2
        convert this using 1; ring
    have cC3 : ∀ a : ℤ, ((IB.filter (fun c => (p : ℤ) ∣ 15 * a + 462 * c + q)).card : ℝ) ≤ LB / p + 1 := by
      intro a
      apply lpt_class b0 b1 p hp0 hbb
      · intro x hx; exact Finset.mem_Ico.mp (Finset.mem_filter.mp hx).1
      · intro x hx y hy
        apply cl
        have := dvd_sub (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
        convert this using 1; ring
    have n1 : (((IA.filter (fun a => (p : ℤ) ∣ a)) ×ˢ ((IB.filter (fun b => (p : ℤ) ∣ 462 * b + q)) ×ˢ IB)).card : ℝ)
        ≤ (LA / p + 1) * (LB / p + 1) * LB := by
      rw [Finset.card_product, Finset.card_product]
      push_cast
      rw [hIBc, ← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ hLB0
      exact mul_le_mul cA cB (by positivity) (by positivity)
    have n2 : (((IA.filter (fun a => (p : ℤ) ∣ a)) ×ˢ (IB ×ˢ (IB.filter (fun b => (p : ℤ) ∣ 462 * b + q)))).card : ℝ)
        ≤ (LA / p + 1) * (LB / p + 1) * LB := by
      rw [Finset.card_product, Finset.card_product]
      push_cast
      rw [hIBc]
      calc ((IA.filter (fun a => (p : ℤ) ∣ a)).card : ℝ) * (LB * ((IB.filter (fun b => (p : ℤ) ∣ 462 * b + q)).card : ℝ))
          = ((IA.filter (fun a => (p : ℤ) ∣ a)).card : ℝ) * ((IB.filter (fun b => (p : ℤ) ∣ 462 * b + q)).card : ℝ) * LB := by ring
        _ ≤ (LA / p + 1) * (LB / p + 1) * LB :=
          mul_le_mul_of_nonneg_right (mul_le_mul cA cB (by positivity) (by positivity)) hLB0
    have n3 : ((IA.biUnion (fun a => ({a} : Finset ℤ) ×ˢ ((IB.filter (fun b => (p : ℤ) ∣ 31 * a - 462 * b - q)) ×ˢ
        (IB.filter (fun c => (p : ℤ) ∣ 15 * a + 462 * c + q))))).card : ℝ) ≤ LA * (LB / p + 1) ^ 2 := by
      have h1 := Finset.card_biUnion_le (s := IA) (t := fun a => ({a} : Finset ℤ) ×ˢ
        ((IB.filter (fun b => (p : ℤ) ∣ 31 * a - 462 * b - q)) ×ˢ (IB.filter (fun c => (p : ℤ) ∣ 15 * a + 462 * c + q))))
      have h1' : ((IA.biUnion (fun a => ({a} : Finset ℤ) ×ˢ ((IB.filter (fun b => (p : ℤ) ∣ 31 * a - 462 * b - q)) ×ˢ
          (IB.filter (fun c => (p : ℤ) ∣ 15 * a + 462 * c + q))))).card : ℝ) ≤
          ∑ a ∈ IA, ((({a} : Finset ℤ) ×ˢ ((IB.filter (fun b => (p : ℤ) ∣ 31 * a - 462 * b - q)) ×ˢ
            (IB.filter (fun c => (p : ℤ) ∣ 15 * a + 462 * c + q)))).card : ℝ) := by
        exact_mod_cast h1
      refine h1'.trans ?_
      calc ∑ a ∈ IA, ((({a} : Finset ℤ) ×ˢ ((IB.filter (fun b => (p : ℤ) ∣ 31 * a - 462 * b - q)) ×ˢ
            (IB.filter (fun c => (p : ℤ) ∣ 15 * a + 462 * c + q)))).card : ℝ)
          ≤ ∑ a ∈ IA, (LB / p + 1) ^ 2 := by
            apply Finset.sum_le_sum
            intro a _
            rw [Finset.card_product, Finset.card_product, Finset.card_singleton]
            push_cast
            rw [one_mul, sq]
            exact mul_le_mul (cB3 a) (cC3 a) (by positivity) (by positivity)
        _ = LA * (LB / p + 1) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul, hIAc]
    have u1 := Finset.card_union_le
      ((IA.filter (fun a => (p : ℤ) ∣ a)) ×ˢ ((IB.filter (fun b => (p : ℤ) ∣ 462 * b + q)) ×ˢ IB) ∪
        (IA.filter (fun a => (p : ℤ) ∣ a)) ×ˢ (IB ×ˢ (IB.filter (fun b => (p : ℤ) ∣ 462 * b + q))))
      (IA.biUnion (fun a => ({a} : Finset ℤ) ×ˢ ((IB.filter (fun b => (p : ℤ) ∣ 31 * a - 462 * b - q)) ×ˢ
        (IB.filter (fun c => (p : ℤ) ∣ 15 * a + 462 * c + q)))))
    have u2 := Finset.card_union_le
      ((IA.filter (fun a => (p : ℤ) ∣ a)) ×ˢ ((IB.filter (fun b => (p : ℤ) ∣ 462 * b + q)) ×ˢ IB))
      ((IA.filter (fun a => (p : ℤ) ∣ a)) ×ˢ (IB ×ˢ (IB.filter (fun b => (p : ℤ) ∣ 462 * b + q))))
    have u1' : (((IA.filter (fun a => (p : ℤ) ∣ a)) ×ˢ ((IB.filter (fun b => (p : ℤ) ∣ 462 * b + q)) ×ˢ IB) ∪
      (IA.filter (fun a => (p : ℤ) ∣ a)) ×ˢ (IB ×ˢ (IB.filter (fun b => (p : ℤ) ∣ 462 * b + q))) ∪
      IA.biUnion (fun a => ({a} : Finset ℤ) ×ˢ ((IB.filter (fun b => (p : ℤ) ∣ 31 * a - 462 * b - q)) ×ˢ
        (IB.filter (fun c => (p : ℤ) ∣ 15 * a + 462 * c + q))))).card : ℝ) ≤
        (((IA.filter (fun a => (p : ℤ) ∣ a)) ×ˢ ((IB.filter (fun b => (p : ℤ) ∣ 462 * b + q)) ×ˢ IB)).card : ℝ) +
        (((IA.filter (fun a => (p : ℤ) ∣ a)) ×ˢ (IB ×ˢ (IB.filter (fun b => (p : ℤ) ∣ 462 * b + q)))).card : ℝ) +
        ((IA.biUnion (fun a => ({a} : Finset ℤ) ×ˢ ((IB.filter (fun b => (p : ℤ) ∣ 31 * a - 462 * b - q)) ×ˢ
          (IB.filter (fun c => (p : ℤ) ∣ 15 * a + 462 * c + q))))).card : ℝ) := by
      exact_mod_cast u1.trans (Nat.add_le_add_right u2 _)
    have e : 2 * ((LA / p + 1) * (LB / p + 1) * LB) + LA * (LB / p + 1) ^ 2 =
        3 * LA * LB ^ 2 * ((p : ℝ) ^ 2)⁻¹ + (4 * LA * LB + 2 * LB ^ 2) * (p : ℝ)⁻¹ + (2 * LB + LA) := by
      ring
    linarith
  -- sum over primes
  have hF1 : (F.card : ℝ) ≤ ∑ p ∈ Pr, (3 * LA * LB ^ 2 * ((p : ℝ) ^ 2)⁻¹ +
      (4 * LA * LB + 2 * LB ^ 2) * (p : ℝ)⁻¹ + (2 * LB + LA)) := by
    have h1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    have h1' : (F.card : ℝ) ≤ ∑ p ∈ Pr, ((((IA.filter (fun a => (p : ℤ) ∣ a)) ×ˢ ((IB.filter (fun b => (p : ℤ) ∣ 462 * b + q)) ×ˢ IB) ∪
      (IA.filter (fun a => (p : ℤ) ∣ a)) ×ˢ (IB ×ˢ (IB.filter (fun b => (p : ℤ) ∣ 462 * b + q))) ∪
      IA.biUnion (fun a => ({a} : Finset ℤ) ×ˢ ((IB.filter (fun b => (p : ℤ) ∣ 31 * a - 462 * b - q)) ×ˢ
        (IB.filter (fun c => (p : ℤ) ∣ 15 * a + 462 * c + q))))).card : ℕ) : ℝ) := by
      exact_mod_cast h1
    exact h1'.trans (Finset.sum_le_sum hper)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul] at hF1
  have s2 : ∑ p ∈ Pr, ((p : ℝ) ^ 2)⁻¹ ≤ 2 / P := by
    calc ∑ p ∈ Pr, ((p : ℝ) ^ 2)⁻¹ ≤ ∑ i ∈ Finset.Ioo P (N + 1), ((i : ℝ) ^ 2)⁻¹ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp
            rw [hPr, Finset.mem_filter, Finset.mem_Icc] at hp
            rw [Finset.mem_Ioo]
            omega
          · intro i _ _; positivity
      _ ≤ 2 / ((P : ℝ) + 1) := sum_Ioo_inv_sq_le P (N + 1)
      _ ≤ 2 / P := by
          apply div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  have s1 : ∑ p ∈ Pr, (p : ℝ)⁻¹ ≤ 1 + Real.log N := by
    calc ∑ p ∈ Pr, (p : ℝ)⁻¹ ≤ ∑ i ∈ Finset.Icc 1 N, (i : ℝ)⁻¹ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp
            rw [hPr, Finset.mem_filter, Finset.mem_Icc] at hp
            rw [Finset.mem_Icc]
            omega
          · intro i _ _; positivity
      _ = (harmonic N : ℝ) := by rw [harmonic_eq_sum_Icc]; push_cast; rfl
      _ ≤ 1 + Real.log N := harmonic_le_one_add_log N
  have s0 : (Pr.card : ℝ) ≤ N := by
    have : Pr.card ≤ N := (Finset.card_filter_le _ _).trans (by rw [Nat.card_Icc]; omega)
    exact_mod_cast this
  have hlog := lpt_log q Z N hqR hZ hNle hN1
  have hlogqZ : 0 ≤ Real.log ((q : ℝ) * Z) := Real.log_nonneg (by linarith)
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  -- size bounds for the coefficients
  have k2 : 3 * LA * LB ^ 2 ≤ 24 * ((q : ℝ) ^ 3 * Z ^ 4) := by
    have : LB ^ 2 ≤ (2 * (q : ℝ) * Z) ^ 2 := pow_le_pow_left₀ hLB0 hLB1 2
    have h2 : LA * LB ^ 2 ≤ (2 * (q : ℝ) * Z ^ 2) * (2 * (q : ℝ) * Z) ^ 2 :=
      mul_le_mul hLA1 this (by positivity) (by positivity)
    have h3 : (2 * (q : ℝ) * Z ^ 2) * (2 * (q : ℝ) * Z) ^ 2 = 8 * ((q : ℝ) ^ 3 * Z ^ 4) := by ring
    have h4 : 3 * LA * LB ^ 2 = 3 * (LA * LB ^ 2) := by ring
    linarith
  have k1 : 4 * LA * LB + 2 * LB ^ 2 ≤ 24 * ((q : ℝ) ^ 2 * Z ^ 3) := by
    have h1 : LA * LB ≤ (2 * (q : ℝ) * Z ^ 2) * (2 * (q : ℝ) * Z) := mul_le_mul hLA1 hLB1 hLB0 (by positivity)
    have h2 : LB ^ 2 ≤ (2 * (q : ℝ) * Z) ^ 2 := pow_le_pow_left₀ hLB0 hLB1 2
    have h3 : (q : ℝ) ^ 2 * Z ^ 2 ≤ (q : ℝ) ^ 2 * Z ^ 3 := by
      have : Z ^ 2 ≤ Z ^ 3 := by
        rw [pow_succ]; exact le_mul_of_one_le_right (sq_nonneg Z) (by linarith)
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have e1 : (2 * (q : ℝ) * Z ^ 2) * (2 * (q : ℝ) * Z) = 4 * ((q : ℝ) ^ 2 * Z ^ 3) := by ring
    have e2 : (2 * (q : ℝ) * Z) ^ 2 = 4 * ((q : ℝ) ^ 2 * Z ^ 2) := by ring
    have e3 : 4 * LA * LB = 4 * (LA * LB) := by ring
    linarith
  have k0 : 2 * LB + LA ≤ 6 * ((q : ℝ) * Z ^ 2) := by linarith
  have t2 : 3 * LA * LB ^ 2 * ∑ p ∈ Pr, ((p : ℝ) ^ 2)⁻¹ ≤ 48 * ((q : ℝ) ^ 3 * Z ^ 4 / P) := by
    have hs0 : 0 ≤ ∑ p ∈ Pr, ((p : ℝ) ^ 2)⁻¹ := Finset.sum_nonneg (fun i _ => by positivity)
    calc 3 * LA * LB ^ 2 * ∑ p ∈ Pr, ((p : ℝ) ^ 2)⁻¹ ≤ 24 * ((q : ℝ) ^ 3 * Z ^ 4) * (2 / P) :=
          mul_le_mul k2 s2 hs0 (by positivity)
      _ = 48 * ((q : ℝ) ^ 3 * Z ^ 4 / P) := by ring
  have t1 : (4 * LA * LB + 2 * LB ^ 2) * ∑ p ∈ Pr, (p : ℝ)⁻¹ ≤
      72 * ((q : ℝ) ^ 2 * Z ^ 3 * Real.log ((q : ℝ) * Z)) := by
    have hs0 : 0 ≤ ∑ p ∈ Pr, (p : ℝ)⁻¹ := Finset.sum_nonneg (fun i _ => by positivity)
    calc (4 * LA * LB + 2 * LB ^ 2) * ∑ p ∈ Pr, (p : ℝ)⁻¹ ≤ 24 * ((q : ℝ) ^ 2 * Z ^ 3) * (3 * Real.log ((q : ℝ) * Z)) :=
          mul_le_mul k1 (s1.trans hlog) hs0 (by positivity)
      _ = 72 * ((q : ℝ) ^ 2 * Z ^ 3 * Real.log ((q : ℝ) * Z)) := by ring
  have t0 : (2 * LB + LA) * (Pr.card : ℝ) ≤ 240 * ((q : ℝ) ^ 2 * Z ^ 4) := by
    calc (2 * LB + LA) * (Pr.card : ℝ) ≤ 6 * ((q : ℝ) * Z ^ 2) * (40 * (q : ℝ) * Z ^ 2) :=
          mul_le_mul k0 (s0.trans hNle) (by positivity) (by positivity)
      _ = 240 * ((q : ℝ) ^ 2 * Z ^ 4) := by ring
  have hX : 0 ≤ (q : ℝ) ^ 3 * Z ^ 4 / P := by positivity
  have hY : 0 ≤ (q : ℝ) ^ 2 * Z ^ 3 * Real.log ((q : ℝ) * Z) := by positivity
  have hW : 0 ≤ (q : ℝ) ^ 2 * Z ^ 4 := by positivity
  linarith

-- N31 helper
lemma ps_floor (L m : ℕ) (hm : 0 < m) : (L : ℝ) / m - 2 ≤ ((L / m - 1 : ℕ) : ℝ) := by
  have h1 := Nat.div_add_mod L m
  have h2 := Nat.mod_lt L hm
  have h3 : L < m * (L / m + 1) := by rw [mul_add, mul_one]; omega
  have h4 : (L : ℝ) < (m : ℝ) * (((L / m : ℕ) : ℝ) + 1) := by exact_mod_cast h3
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h5 : (L : ℝ) / m < ((L / m : ℕ) : ℝ) + 1 := by rw [div_lt_iff₀ hmR]; linarith
  have h6 : L / m ≤ (L / m - 1) + 1 := by omega
  have h7 : ((L / m : ℕ) : ℝ) ≤ ((L / m - 1 : ℕ) : ℝ) + 1 := by exact_mod_cast h6
  linarith

-- N31 helper: log x ≤ 2 √x
lemma ps_log (x : ℝ) (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have h1 : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx.le
  have h2 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx)
  linarith

-- N31 parameter_sieve [assembly]
set_option maxHeartbeats 400000 in
theorem parameter_sieve (Good : ℝ → ℕ → ℤ → ℤ → ℤ → Prop)
    (hGood : ∀ Z q A B C, Good Z q A B C ↔
      ((4619990760 : ℤ) ∣ A ∧ (4619990760 : ℤ) ∣ B ∧ (4619990760 : ℤ) ∣ C ∧
       (q : ℝ) * Z ^ 2 ≤ A ∧ (A : ℝ) < 2 * q * Z ^ 2 ∧
       (q : ℝ) * Z ≤ B ∧ (B : ℝ) < 2 * q * Z ∧
       (q : ℝ) * Z ≤ C ∧ (C : ℝ) < 2 * q * Z ∧
       (∀ p : ℕ, p.Prime → p ∣ q →
         ¬ (p : ℤ) ∣ A * B * C * (462 * C + 15 * A) * (31 * A - 462 * B) * (15 * B + 31 * C)) ∧
       (∀ p : ℕ, p.Prime → ¬ p ∣ 4619990760 * q →
         ¬ (((p : ℤ) ∣ A ∧ (p : ℤ) ∣ 462 * B + q) ∨ ((p : ℤ) ∣ A ∧ (p : ℤ) ∣ 462 * C + q) ∨
           ((p : ℤ) ∣ 31 * A - 462 * B - q ∧ (p : ℤ) ∣ 15 * A + 462 * C + q))))) (M0 : ℝ) :
    ∃ Z0 q0 c2 : ℝ, 100 ≤ Z0 ∧ 0 < c2 ∧ ∀ (q : ℕ) (Z : ℝ),
      Squarefree q → q % 4619990760 = 1 → ∑ p ∈ q.primeFactors, (1 : ℝ) / p ≤ M0 → q0 ≤ q → Z0 ≤ Z →
      ∃ F : Finset (ℤ × ℤ × ℤ), (∀ t ∈ F, Good Z q t.1 t.2.1 t.2.2) ∧ c2 * (q : ℝ) ^ 3 * Z ^ 4 ≤ F.card := by
  -- Route: residue_blocks on the box a ∈ [⌈qZ²/W⌉, +⌊qZ²/W⌋-1), b, c ∈ [⌈qZ/W⌉, +⌊qZ/W⌋-1) with the residue set
  -- of local_density mod m = q·M_P gives ≥ ϑ (qZ²/2W)(qZ/2W)² triples; remove the large-prime tail
  -- (large_prime_tail) with P, q0, Z0 chosen so each tail term is ≤ a quarter of the main term.
  classical
  obtain ⟨ϑ, hϑ, hloc⟩ := local_density M0
  obtain ⟨Ct, htail⟩ := large_prime_tail
  set W : ℝ := 4619990760 with hW
  have hW0 : (0 : ℝ) < W := by rw [hW]; norm_num
  set K : ℝ := ϑ / (8 * W ^ 3) with hK
  have hK0 : 0 < K := by positivity
  set C' : ℝ := max Ct 1 with hC'
  have hC'1 : 1 ≤ C' := le_max_right _ _
  have hCtC : Ct ≤ C' := le_max_left _ _
  set P : ℕ := ⌈4 * C' / K⌉₊ + 1 with hP
  set MP : ℕ := ∏ p ∈ (Finset.range (P + 1)).filter Nat.Prime, p with hMP
  have hMP1 : 1 ≤ MP := Finset.one_le_prod' (fun p hp => (Finset.mem_filter.mp hp).2.one_lt.le)
  refine ⟨max 100 (max (4 * W * (1 + MP)) ((8 * C' / K) ^ 2)), 4 * C' / K + 2, K / 4,
    le_max_left _ _, by positivity, ?_⟩
  intro q Z hsq hqW hH hq0 hZ0
  have hZ100 : 100 ≤ Z := le_trans (le_max_left _ _) hZ0
  have hZW : 4 * W * (1 + MP) ≤ Z := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hZ0
  have hZC : (8 * C' / K) ^ 2 ≤ Z := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hZ0
  have hqC : 4 * C' / K + 2 ≤ (q : ℝ) := hq0
  have hCK : 0 ≤ 4 * C' / K := by positivity
  have hq2 : 2 ≤ q := by
    have : (2 : ℝ) ≤ q := by linarith
    exact_mod_cast this
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  have hq0' : (0 : ℝ) < q := by linarith
  have hZ0' : 0 < Z := by linarith
  have hP1 : 1 ≤ P := by rw [hP]; omega
  have hPR : 4 * C' / K ≤ (P : ℝ) := by
    rw [hP]; push_cast; linarith [Nat.le_ceil (4 * C' / K)]
  -- the modulus
  set S := (Finset.range (P + 1)).filter (fun p => p.Prime ∧ ¬ p ∣ 4619990760 * q) with hS
  set m : ℕ := q * ∏ p ∈ S, p with hm
  obtain ⟨Ω, hΩc, hΩ⟩ := hloc q P m hsq hqW hH hm
  have hSle : ∏ p ∈ S, p ≤ MP := by
    rw [hMP]
    apply Finset.prod_le_prod_of_subset_of_one_le
    · intro p hp
      rw [hS, Finset.mem_filter] at hp
      exact Finset.mem_filter.mpr ⟨hp.1, hp.2.1⟩
    · intro p hp _
      exact (Finset.mem_filter.mp hp).2.one_lt.le
  have hSpos : 0 < ∏ p ∈ S, p := Finset.prod_pos (fun p hp => (Finset.mem_filter.mp hp).2.1.pos)
  have hm0 : 0 < m := Nat.mul_pos (by omega) hSpos
  haveI : NeZero m := ⟨hm0.ne'⟩
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hmq : (m : ℝ) ≤ q * MP := by
    have : m ≤ q * MP := Nat.mul_le_mul_left q hSle
    exact_mod_cast this
  have hMPR : (1 : ℝ) ≤ MP := by exact_mod_cast hMP1
  -- block parameters
  set x1 : ℝ := (q : ℝ) * Z ^ 2 / W with hx1
  set x2 : ℝ := (q : ℝ) * Z / W with hx2
  have hx12 : x1 = x2 * Z := by rw [hx1, hx2]; ring
  have hx2big : 4 * q * (1 + MP) ≤ x2 := by
    rw [hx2, le_div_iff₀ hW0]
    have := mul_le_mul_of_nonneg_left hZW hq0'.le
    linarith
  have hx2pos : 8 ≤ x2 := by nlinarith
  have hx1x2 : x2 ≤ x1 := by rw [hx12]; nlinarith
  set a1 : ℤ := ⌈x1⌉ with ha1
  set a2 : ℤ := ⌈x2⌉ with ha2
  set L1 : ℕ := ⌊x1⌋₊ - 1 with hL1
  set L2 : ℕ := ⌊x2⌋₊ - 1 with hL2
  have hf1 : 1 ≤ ⌊x1⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hf2 : 1 ≤ ⌊x2⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hL1R : (L1 : ℝ) = (⌊x1⌋₊ : ℝ) - 1 := by rw [hL1, Nat.cast_sub hf1, Nat.cast_one]
  have hL2R : (L2 : ℝ) = (⌊x2⌋₊ : ℝ) - 1 := by rw [hL2, Nat.cast_sub hf2, Nat.cast_one]
  have hfl1 : (⌊x1⌋₊ : ℝ) ≤ x1 := Nat.floor_le (by linarith)
  have hfl2 : (⌊x2⌋₊ : ℝ) ≤ x2 := Nat.floor_le (by linarith)
  have hfu1 : x1 < (⌊x1⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x1
  have hfu2 : x2 < (⌊x2⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x2
  have hc1l : x1 ≤ (a1 : ℝ) := Int.le_ceil x1
  have hc1u : (a1 : ℝ) < x1 + 1 := Int.ceil_lt_add_one x1
  have hc2l : x2 ≤ (a2 : ℝ) := Int.le_ceil x2
  have hc2u : (a2 : ℝ) < x2 + 1 := Int.ceil_lt_add_one x2
  -- the box and its residue-good part
  set B := ((Finset.Ico a1 (a1 + L1) ×ˢ (Finset.Ico a2 (a2 + L2) ×ˢ Finset.Ico a2 (a2 + L2))).filter
        (fun x => ((x.1 : ZMod m), (x.2.1 : ZMod m), (x.2.2 : ZMod m)) ∈ Ω)) with hB
  have hblock : Ω.card * ((L1 / m - 1) * (L2 / m - 1) * (L2 / m - 1)) ≤ B.card :=
    residue_blocks m Ω a1 a2 a2 L1 L2 L2
  -- box bounds for W·x
  have hbox : ∀ x ∈ B, (q : ℝ) * Z ^ 2 ≤ ((4619990760 * x.1 : ℤ) : ℝ) ∧
      ((4619990760 * x.1 : ℤ) : ℝ) < 2 * q * Z ^ 2 ∧
      (q : ℝ) * Z ≤ ((4619990760 * x.2.1 : ℤ) : ℝ) ∧ ((4619990760 * x.2.1 : ℤ) : ℝ) < 2 * q * Z ∧
      (q : ℝ) * Z ≤ ((4619990760 * x.2.2 : ℤ) : ℝ) ∧ ((4619990760 * x.2.2 : ℤ) : ℝ) < 2 * q * Z := by
    intro x hx
    rw [hB, Finset.mem_filter, Finset.mem_product, Finset.mem_product, Finset.mem_Ico, Finset.mem_Ico,
      Finset.mem_Ico] at hx
    obtain ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩⟩, -⟩ := hx
    have r1 : (a1 : ℝ) ≤ x.1 := by exact_mod_cast h1
    have r2 : (x.1 : ℝ) + 1 ≤ a1 + L1 := by
      have : x.1 + 1 ≤ a1 + L1 := h2
      exact_mod_cast this
    have r3 : (a2 : ℝ) ≤ x.2.1 := by exact_mod_cast h3
    have r4 : (x.2.1 : ℝ) + 1 ≤ a2 + L2 := by
      have : x.2.1 + 1 ≤ a2 + L2 := h4
      exact_mod_cast this
    have r5 : (a2 : ℝ) ≤ x.2.2 := by exact_mod_cast h5
    have r6 : (x.2.2 : ℝ) + 1 ≤ a2 + L2 := by
      have : x.2.2 + 1 ≤ a2 + L2 := h6
      exact_mod_cast this
    have e1 : W * x1 = (q : ℝ) * Z ^ 2 := by rw [hx1, mul_comm]; exact div_mul_cancel₀ _ hW0.ne'
    have e2 : W * x2 = (q : ℝ) * Z := by rw [hx2, mul_comm]; exact div_mul_cancel₀ _ hW0.ne'
    push_cast
    rw [← hW]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := mul_le_mul_of_nonneg_left (hc1l.trans r1) hW0.le
      linarith
    · have hlt : (x.1 : ℝ) < 2 * x1 := by linarith
      have := mul_lt_mul_of_pos_left hlt hW0
      linarith
    · have := mul_le_mul_of_nonneg_left (hc2l.trans r3) hW0.le
      linarith
    · have hlt : (x.2.1 : ℝ) < 2 * x2 := by linarith
      have := mul_lt_mul_of_pos_left hlt hW0
      linarith
    · have := mul_le_mul_of_nonneg_left (hc2l.trans r5) hW0.le
      linarith
    · have hlt : (x.2.2 : ℝ) < 2 * x2 := by linarith
      have := mul_lt_mul_of_pos_left hlt hW0
      linarith
  -- main term
  have hmain : K * (q : ℝ) ^ 3 * Z ^ 4 ≤ B.card := by
    have g1 := ps_floor L1 m hm0
    have g2 := ps_floor L2 m hm0
    have hd1 : x1 / 2 ≤ (L1 : ℝ) - 2 * m := by linarith
    have hd2 : x2 / 2 ≤ (L2 : ℝ) - 2 * m := by linarith
    have k1 : x1 / 2 / m ≤ ((L1 / m - 1 : ℕ) : ℝ) := by
      have : x1 / 2 / m ≤ (L1 : ℝ) / m - 2 := by
        rw [div_le_iff₀ hmR, sub_mul, div_mul_cancel₀ _ hmR.ne']; linarith
      linarith
    have k2 : x2 / 2 / m ≤ ((L2 / m - 1 : ℕ) : ℝ) := by
      have : x2 / 2 / m ≤ (L2 : ℝ) / m - 2 := by
        rw [div_le_iff₀ hmR, sub_mul, div_mul_cancel₀ _ hmR.ne']; linarith
      linarith
    have p1 : 0 ≤ x1 / 2 / m := div_nonneg (div_nonneg (by linarith) (by norm_num)) hmR.le
    have p2 : 0 ≤ x2 / 2 / m := div_nonneg (div_nonneg (by linarith) (by norm_num)) hmR.le
    have hprod : (x1 / 2 / m) * (x2 / 2 / m) * (x2 / 2 / m) ≤
        ((L1 / m - 1 : ℕ) : ℝ) * ((L2 / m - 1 : ℕ) : ℝ) * ((L2 / m - 1 : ℕ) : ℝ) :=
      mul_le_mul (mul_le_mul k1 k2 p2 (by positivity)) k2 p2 (by positivity)
    have hblockR : (Ω.card : ℝ) * (((L1 / m - 1 : ℕ) : ℝ) * ((L2 / m - 1 : ℕ) : ℝ) * ((L2 / m - 1 : ℕ) : ℝ)) ≤
        B.card := by exact_mod_cast hblock
    have hstep : ϑ * (m : ℝ) ^ 3 * ((x1 / 2 / m) * (x2 / 2 / m) * (x2 / 2 / m)) ≤ B.card :=
      le_trans (mul_le_mul hΩc hprod (mul_nonneg (mul_nonneg p1 p2) p2) (by positivity)) hblockR
    have heq : ϑ * (m : ℝ) ^ 3 * ((x1 / 2 / m) * (x2 / 2 / m) * (x2 / 2 / m)) = K * (q : ℝ) ^ 3 * Z ^ 4 := by
      rw [hK, hx1, hx2]
      field_simp [hW0.ne', hmR.ne']
      ring
    linarith
  -- the tail and the final set
  set F0 := B.filter (fun x => ∀ p : ℕ, p.Prime → P < p → ¬ p ∣ 4619990760 * q →
      ¬ (((p : ℤ) ∣ 4619990760 * x.1 ∧ (p : ℤ) ∣ 462 * (4619990760 * x.2.1) + q) ∨
         ((p : ℤ) ∣ 4619990760 * x.1 ∧ (p : ℤ) ∣ 462 * (4619990760 * x.2.2) + q) ∨
         ((p : ℤ) ∣ 31 * (4619990760 * x.1) - 462 * (4619990760 * x.2.1) - q ∧
          (p : ℤ) ∣ 15 * (4619990760 * x.1) + 462 * (4619990760 * x.2.2) + q))) with hF0
  set Bad := B.filter (fun x => ¬ ∀ p : ℕ, p.Prime → P < p → ¬ p ∣ 4619990760 * q →
      ¬ (((p : ℤ) ∣ 4619990760 * x.1 ∧ (p : ℤ) ∣ 462 * (4619990760 * x.2.1) + q) ∨
         ((p : ℤ) ∣ 4619990760 * x.1 ∧ (p : ℤ) ∣ 462 * (4619990760 * x.2.2) + q) ∨
         ((p : ℤ) ∣ 31 * (4619990760 * x.1) - 462 * (4619990760 * x.2.1) - q ∧
          (p : ℤ) ∣ 15 * (4619990760 * x.1) + 462 * (4619990760 * x.2.2) + q))) with hBad
  have hsplit := Finset.card_filter_add_card_filter_not (s := B) (fun x : ℤ × ℤ × ℤ =>
      ∀ p : ℕ, p.Prime → P < p → ¬ p ∣ 4619990760 * q →
      ¬ (((p : ℤ) ∣ 4619990760 * x.1 ∧ (p : ℤ) ∣ 462 * (4619990760 * x.2.1) + q) ∨
         ((p : ℤ) ∣ 4619990760 * x.1 ∧ (p : ℤ) ∣ 462 * (4619990760 * x.2.2) + q) ∨
         ((p : ℤ) ∣ 31 * (4619990760 * x.1) - 462 * (4619990760 * x.2.1) - q ∧
          (p : ℤ) ∣ 15 * (4619990760 * x.1) + 462 * (4619990760 * x.2.2) + q)))
  have hsplit' : F0.card + Bad.card = B.card := by rw [hF0, hBad]; exact hsplit
  set φ : ℤ × ℤ × ℤ → ℤ × ℤ × ℤ := fun x => (4619990760 * x.1, 4619990760 * x.2.1, 4619990760 * x.2.2) with hφ
  have hinj : Function.Injective φ := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    simp only [hφ, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    have e1 : a = a' := mul_left_cancel₀ (by norm_num) h1
    have e2 : b = b' := mul_left_cancel₀ (by norm_num) h2
    have e3 : c = c' := mul_left_cancel₀ (by norm_num) h3
    rw [e1, e2, e3]
  have htl := htail q P Z hq2 hZ100 hP1 (Bad.image φ) (by
    intro t ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hxB, hxbad⟩ := Finset.mem_filter.mp hx
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hbox x hxB
    push_neg at hxbad
    obtain ⟨p, hp, hPp, hpWq, hb⟩ := hxbad
    exact ⟨b1, b2, b3, b4, b5, b6, p, hp, hPp, hpWq, hb⟩)
  rw [Finset.card_image_of_injective _ hinj] at htl
  -- the tail is at most three quarters of the main term
  have hlogx : Real.log ((q : ℝ) * Z) ≤ 2 * Real.sqrt ((q : ℝ) * Z) := ps_log _ (by positivity)
  have hsq1 : 8 * C' / K ≤ Real.sqrt ((q : ℝ) * Z) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    have : Z ≤ (q : ℝ) * Z := le_mul_of_one_le_left hZ0'.le (by linarith)
    linarith
  have hsqqZ : Real.sqrt ((q : ℝ) * Z) * Real.sqrt ((q : ℝ) * Z) = (q : ℝ) * Z :=
    Real.mul_self_sqrt (by positivity)
  have hlog0 : 0 ≤ Real.log ((q : ℝ) * Z) := Real.log_nonneg (by
    have : Z ≤ (q : ℝ) * Z := le_mul_of_one_le_left hZ0'.le (by linarith)
    linarith)
  have hsqrt0 : 0 ≤ Real.sqrt ((q : ℝ) * Z) := Real.sqrt_nonneg _
  have hq3 : 0 ≤ (q : ℝ) ^ 3 * Z ^ 4 := by positivity
  have hPpos : (0 : ℝ) < P := by exact_mod_cast hP1
  have tA : Ct * ((q : ℝ) ^ 3 * Z ^ 4 / P) ≤ K / 4 * ((q : ℝ) ^ 3 * Z ^ 4) := by
    have h1 : Ct * ((q : ℝ) ^ 3 * Z ^ 4 / P) ≤ C' * ((q : ℝ) ^ 3 * Z ^ 4 / P) :=
      mul_le_mul_of_nonneg_right hCtC (by positivity)
    have h2 : C' / P ≤ K / 4 := by
      rw [div_le_iff₀ hPpos]
      have : 4 * C' / K * K = 4 * C' := div_mul_cancel₀ _ hK0.ne'
      have h5 := mul_le_mul_of_nonneg_left hPR hK0.le
      linarith
    have h3 : C' * ((q : ℝ) ^ 3 * Z ^ 4 / P) = C' / P * ((q : ℝ) ^ 3 * Z ^ 4) := by ring
    have h4 := mul_le_mul_of_nonneg_right h2 hq3
    linarith
  have tC : Ct * ((q : ℝ) ^ 2 * Z ^ 4) ≤ K / 4 * ((q : ℝ) ^ 3 * Z ^ 4) := by
    have h1 : Ct * ((q : ℝ) ^ 2 * Z ^ 4) ≤ C' * ((q : ℝ) ^ 2 * Z ^ 4) :=
      mul_le_mul_of_nonneg_right hCtC (by positivity)
    have h2 : C' ≤ K / 4 * q := by
      have : 4 * C' / K * K = 4 * C' := div_mul_cancel₀ _ hK0.ne'
      have h5 := mul_le_mul_of_nonneg_left hqC hK0.le
      linarith
    have h4 := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ (q : ℝ) ^ 2 * Z ^ 4)
    have h5 : K / 4 * q * ((q : ℝ) ^ 2 * Z ^ 4) = K / 4 * ((q : ℝ) ^ 3 * Z ^ 4) := by ring
    linarith
  have tB : Ct * ((q : ℝ) ^ 2 * Z ^ 3 * Real.log ((q : ℝ) * Z)) ≤ K / 4 * ((q : ℝ) ^ 3 * Z ^ 4) := by
    have h1 : Ct * ((q : ℝ) ^ 2 * Z ^ 3 * Real.log ((q : ℝ) * Z)) ≤
        C' * ((q : ℝ) ^ 2 * Z ^ 3 * Real.log ((q : ℝ) * Z)) :=
      mul_le_mul_of_nonneg_right hCtC (mul_nonneg (by positivity) hlog0)
    have h2 : C' * Real.log ((q : ℝ) * Z) ≤ K / 4 * ((q : ℝ) * Z) := by
      have h8 : 8 * C' / K * K = 8 * C' := div_mul_cancel₀ _ hK0.ne'
      have h9 : 8 * C' ≤ K * Real.sqrt ((q : ℝ) * Z) := by
        have := mul_le_mul_of_nonneg_left hsq1 hK0.le
        linarith
      have h10 := mul_le_mul_of_nonneg_right h9 hsqrt0
      have h11 := mul_le_mul_of_nonneg_left hlogx (by linarith : (0 : ℝ) ≤ C')
      have h12 : K * Real.sqrt ((q : ℝ) * Z) * Real.sqrt ((q : ℝ) * Z) = K * ((q : ℝ) * Z) := by
        rw [mul_assoc, hsqqZ]
      linarith
    have h4 := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ (q : ℝ) ^ 2 * Z ^ 3)
    have h5 : C' * ((q : ℝ) ^ 2 * Z ^ 3 * Real.log ((q : ℝ) * Z)) =
        C' * Real.log ((q : ℝ) * Z) * ((q : ℝ) ^ 2 * Z ^ 3) := by ring
    have h6 : K / 4 * ((q : ℝ) * Z) * ((q : ℝ) ^ 2 * Z ^ 3) = K / 4 * ((q : ℝ) ^ 3 * Z ^ 4) := by ring
    linarith
  have htl' : (Bad.card : ℝ) ≤ 3 * (K / 4) * ((q : ℝ) ^ 3 * Z ^ 4) := by
    have : Ct * ((q : ℝ) ^ 3 * Z ^ 4 / P + (q : ℝ) ^ 2 * Z ^ 3 * Real.log ((q : ℝ) * Z) + (q : ℝ) ^ 2 * Z ^ 4) =
        Ct * ((q : ℝ) ^ 3 * Z ^ 4 / P) + Ct * ((q : ℝ) ^ 2 * Z ^ 3 * Real.log ((q : ℝ) * Z)) +
        Ct * ((q : ℝ) ^ 2 * Z ^ 4) := by ring
    linarith
  refine ⟨F0.image φ, ?_, ?_⟩
  · intro t ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hxB, hxgood⟩ := Finset.mem_filter.mp hx
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hbox x hxB
    have hxΩ := (Finset.mem_filter.mp hxB).2
    obtain ⟨hq, hP⟩ := hΩ x.1 x.2.1 x.2.2 hxΩ
    rw [hGood]
    simp only [hφ]
    refine ⟨dvd_mul_right _ _, dvd_mul_right _ _, dvd_mul_right _ _, b1, b2, b3, b4, b5, b6, hq, ?_⟩
    intro p hp hpWq
    by_cases hpP : p ≤ P
    · exact hP p hp hpP hpWq
    · exact hxgood p hp (by omega) hpWq
  · rw [Finset.card_image_of_injective _ hinj]
    have hsplitR : (F0.card : ℝ) + Bad.card = B.card := by exact_mod_cast hsplit'
    have e : K / 4 * (q : ℝ) ^ 3 * Z ^ 4 = K * (q : ℝ) ^ 3 * Z ^ 4 - 3 * (K / 4) * ((q : ℝ) ^ 3 * Z ^ 4) := by ring
    linarith

-- N32 planes_meet_once [algebraic_identity]
set_option maxHeartbeats 400000 in
theorem planes_meet_once (OnPl : ℤ → ℤ → ℤ → ℤ → (Fin 6 → ℤ) → Prop)
    (hOnPl : ∀ q A B C (x : Fin 6 → ℤ), OnPl q A B C x ↔
      (q * (x 1 - x 4) = 31 * A * (x 2 - x 4) + 462 * B * x 4 ∧
       q * (x 3 - x 4) = -15 * A * (x 0 - x 4) + 462 * C * x 4 ∧
       q * (x 4 + 1) = -(15 * B * (x 0 - x 4) + 31 * C * (x 2 - x 4)) ∧
       508 * x 5 = 15 * (x 0 + x 1) + 31 * (x 2 + x 3) - 508 * x 4 - 462))
    (q q' A B C A' B' C' : ℤ) (x x' : Fin 6 → ℤ) (hq : 0 < q) (hq' : 0 < q')
    (hA : IsCoprime A q) (hB : IsCoprime B q) (hC : IsCoprime C q)
    (hA' : IsCoprime A' q') (hB' : IsCoprime B' q') (hC' : IsCoprime C' q')
    (hne : (q, A, B, C) ≠ (q', A', B', C'))
    (h1 : OnPl q A B C x) (h2 : OnPl q A B C x') (h3 : OnPl q' A' B' C' x) (h4 : OnPl q' A' B' C' x') :
    x = x' := by
  rw [hOnPl] at h1 h2 h3 h4
  obtain ⟨e1, e2, e3, e4⟩ := h1
  obtain ⟨e1', e2', e3', e4'⟩ := h2
  obtain ⟨f1, f2, f3, f4⟩ := h3
  obtain ⟨f1', f2', f3', f4'⟩ := h4
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq'R : (0 : ℝ) < q' := by exact_mod_cast hq'
  have ca1 : (q : ℝ) * ((x 1 : ℝ) - x 4) = 31 * A * ((x 2 : ℝ) - x 4) + 462 * B * (x 4 : ℝ) := by exact_mod_cast e1
  have ca2 : (q : ℝ) * ((x 3 : ℝ) - x 4) = -15 * A * ((x 0 : ℝ) - x 4) + 462 * C * (x 4 : ℝ) := by exact_mod_cast e2
  have ca3 : (q : ℝ) * ((x 4 : ℝ) + 1) = -(15 * B * ((x 0 : ℝ) - x 4) + 31 * C * ((x 2 : ℝ) - x 4)) := by exact_mod_cast e3
  have Ea1 : (x 1 : ℝ) - x 4 = 31 * ((A : ℝ) / q) * ((x 2 : ℝ) - x 4) + 462 * ((B : ℝ) / q) * (x 4 : ℝ) := by
    rw [show 31 * ((A : ℝ) / q) * ((x 2 : ℝ) - x 4) + 462 * ((B : ℝ) / q) * (x 4 : ℝ) = (31 * A * ((x 2 : ℝ) - x 4) + 462 * B * (x 4 : ℝ)) / q by ring, eq_div_iff hqR.ne']
    linear_combination ca1
  have Ea2 : (x 3 : ℝ) - x 4 = -15 * ((A : ℝ) / q) * ((x 0 : ℝ) - x 4) + 462 * ((C : ℝ) / q) * (x 4 : ℝ) := by
    rw [show -15 * ((A : ℝ) / q) * ((x 0 : ℝ) - x 4) + 462 * ((C : ℝ) / q) * (x 4 : ℝ) = (-15 * A * ((x 0 : ℝ) - x 4) + 462 * C * (x 4 : ℝ)) / q by ring, eq_div_iff hqR.ne']
    linear_combination ca2
  have Ea3 : (x 4 : ℝ) + 1 = -(15 * ((B : ℝ) / q) * ((x 0 : ℝ) - x 4) + 31 * ((C : ℝ) / q) * ((x 2 : ℝ) - x 4)) := by
    rw [show -(15 * ((B : ℝ) / q) * ((x 0 : ℝ) - x 4) + 31 * ((C : ℝ) / q) * ((x 2 : ℝ) - x 4)) = (-(15 * B * ((x 0 : ℝ) - x 4) + 31 * C * ((x 2 : ℝ) - x 4))) / q by ring, eq_div_iff hqR.ne']
    linear_combination ca3
  have cb1 : (q : ℝ) * ((x' 1 : ℝ) - x' 4) = 31 * A * ((x' 2 : ℝ) - x' 4) + 462 * B * (x' 4 : ℝ) := by exact_mod_cast e1'
  have cb2 : (q : ℝ) * ((x' 3 : ℝ) - x' 4) = -15 * A * ((x' 0 : ℝ) - x' 4) + 462 * C * (x' 4 : ℝ) := by exact_mod_cast e2'
  have cb3 : (q : ℝ) * ((x' 4 : ℝ) + 1) = -(15 * B * ((x' 0 : ℝ) - x' 4) + 31 * C * ((x' 2 : ℝ) - x' 4)) := by exact_mod_cast e3'
  have Eb1 : (x' 1 : ℝ) - x' 4 = 31 * ((A : ℝ) / q) * ((x' 2 : ℝ) - x' 4) + 462 * ((B : ℝ) / q) * (x' 4 : ℝ) := by
    rw [show 31 * ((A : ℝ) / q) * ((x' 2 : ℝ) - x' 4) + 462 * ((B : ℝ) / q) * (x' 4 : ℝ) = (31 * A * ((x' 2 : ℝ) - x' 4) + 462 * B * (x' 4 : ℝ)) / q by ring, eq_div_iff hqR.ne']
    linear_combination cb1
  have Eb2 : (x' 3 : ℝ) - x' 4 = -15 * ((A : ℝ) / q) * ((x' 0 : ℝ) - x' 4) + 462 * ((C : ℝ) / q) * (x' 4 : ℝ) := by
    rw [show -15 * ((A : ℝ) / q) * ((x' 0 : ℝ) - x' 4) + 462 * ((C : ℝ) / q) * (x' 4 : ℝ) = (-15 * A * ((x' 0 : ℝ) - x' 4) + 462 * C * (x' 4 : ℝ)) / q by ring, eq_div_iff hqR.ne']
    linear_combination cb2
  have Eb3 : (x' 4 : ℝ) + 1 = -(15 * ((B : ℝ) / q) * ((x' 0 : ℝ) - x' 4) + 31 * ((C : ℝ) / q) * ((x' 2 : ℝ) - x' 4)) := by
    rw [show -(15 * ((B : ℝ) / q) * ((x' 0 : ℝ) - x' 4) + 31 * ((C : ℝ) / q) * ((x' 2 : ℝ) - x' 4)) = (-(15 * B * ((x' 0 : ℝ) - x' 4) + 31 * C * ((x' 2 : ℝ) - x' 4))) / q by ring, eq_div_iff hqR.ne']
    linear_combination cb3
  have cc1 : (q' : ℝ) * ((x 1 : ℝ) - x 4) = 31 * A' * ((x 2 : ℝ) - x 4) + 462 * B' * (x 4 : ℝ) := by exact_mod_cast f1
  have cc2 : (q' : ℝ) * ((x 3 : ℝ) - x 4) = -15 * A' * ((x 0 : ℝ) - x 4) + 462 * C' * (x 4 : ℝ) := by exact_mod_cast f2
  have cc3 : (q' : ℝ) * ((x 4 : ℝ) + 1) = -(15 * B' * ((x 0 : ℝ) - x 4) + 31 * C' * ((x 2 : ℝ) - x 4)) := by exact_mod_cast f3
  have Ec1 : (x 1 : ℝ) - x 4 = 31 * ((A' : ℝ) / q') * ((x 2 : ℝ) - x 4) + 462 * ((B' : ℝ) / q') * (x 4 : ℝ) := by
    rw [show 31 * ((A' : ℝ) / q') * ((x 2 : ℝ) - x 4) + 462 * ((B' : ℝ) / q') * (x 4 : ℝ) = (31 * A' * ((x 2 : ℝ) - x 4) + 462 * B' * (x 4 : ℝ)) / q' by ring, eq_div_iff hq'R.ne']
    linear_combination cc1
  have Ec2 : (x 3 : ℝ) - x 4 = -15 * ((A' : ℝ) / q') * ((x 0 : ℝ) - x 4) + 462 * ((C' : ℝ) / q') * (x 4 : ℝ) := by
    rw [show -15 * ((A' : ℝ) / q') * ((x 0 : ℝ) - x 4) + 462 * ((C' : ℝ) / q') * (x 4 : ℝ) = (-15 * A' * ((x 0 : ℝ) - x 4) + 462 * C' * (x 4 : ℝ)) / q' by ring, eq_div_iff hq'R.ne']
    linear_combination cc2
  have Ec3 : (x 4 : ℝ) + 1 = -(15 * ((B' : ℝ) / q') * ((x 0 : ℝ) - x 4) + 31 * ((C' : ℝ) / q') * ((x 2 : ℝ) - x 4)) := by
    rw [show -(15 * ((B' : ℝ) / q') * ((x 0 : ℝ) - x 4) + 31 * ((C' : ℝ) / q') * ((x 2 : ℝ) - x 4)) = (-(15 * B' * ((x 0 : ℝ) - x 4) + 31 * C' * ((x 2 : ℝ) - x 4))) / q' by ring, eq_div_iff hq'R.ne']
    linear_combination cc3
  have cd1 : (q' : ℝ) * ((x' 1 : ℝ) - x' 4) = 31 * A' * ((x' 2 : ℝ) - x' 4) + 462 * B' * (x' 4 : ℝ) := by exact_mod_cast f1'
  have cd2 : (q' : ℝ) * ((x' 3 : ℝ) - x' 4) = -15 * A' * ((x' 0 : ℝ) - x' 4) + 462 * C' * (x' 4 : ℝ) := by exact_mod_cast f2'
  have cd3 : (q' : ℝ) * ((x' 4 : ℝ) + 1) = -(15 * B' * ((x' 0 : ℝ) - x' 4) + 31 * C' * ((x' 2 : ℝ) - x' 4)) := by exact_mod_cast f3'
  have Ed1 : (x' 1 : ℝ) - x' 4 = 31 * ((A' : ℝ) / q') * ((x' 2 : ℝ) - x' 4) + 462 * ((B' : ℝ) / q') * (x' 4 : ℝ) := by
    rw [show 31 * ((A' : ℝ) / q') * ((x' 2 : ℝ) - x' 4) + 462 * ((B' : ℝ) / q') * (x' 4 : ℝ) = (31 * A' * ((x' 2 : ℝ) - x' 4) + 462 * B' * (x' 4 : ℝ)) / q' by ring, eq_div_iff hq'R.ne']
    linear_combination cd1
  have Ed2 : (x' 3 : ℝ) - x' 4 = -15 * ((A' : ℝ) / q') * ((x' 0 : ℝ) - x' 4) + 462 * ((C' : ℝ) / q') * (x' 4 : ℝ) := by
    rw [show -15 * ((A' : ℝ) / q') * ((x' 0 : ℝ) - x' 4) + 462 * ((C' : ℝ) / q') * (x' 4 : ℝ) = (-15 * A' * ((x' 0 : ℝ) - x' 4) + 462 * C' * (x' 4 : ℝ)) / q' by ring, eq_div_iff hq'R.ne']
    linear_combination cd2
  have Ed3 : (x' 4 : ℝ) + 1 = -(15 * ((B' : ℝ) / q') * ((x' 0 : ℝ) - x' 4) + 31 * ((C' : ℝ) / q') * ((x' 2 : ℝ) - x' 4)) := by
    rw [show -(15 * ((B' : ℝ) / q') * ((x' 0 : ℝ) - x' 4) + 31 * ((C' : ℝ) / q') * ((x' 2 : ℝ) - x' 4)) = (-(15 * B' * ((x' 0 : ℝ) - x' 4) + 31 * C' * ((x' 2 : ℝ) - x' 4))) / q' by ring, eq_div_iff hq'R.ne']
    linear_combination cd3
  obtain ⟨Δα, hΔα⟩ : ∃ d : ℝ, d = (A : ℝ) / q - (A' : ℝ) / q' := ⟨_, rfl⟩
  obtain ⟨Δβ, hΔβ⟩ : ∃ d : ℝ, d = (B : ℝ) / q - (B' : ℝ) / q' := ⟨_, rfl⟩
  obtain ⟨Δγ, hΔγ⟩ : ∃ d : ℝ, d = (C : ℝ) / q - (C' : ℝ) / q' := ⟨_, rfl⟩
  have D1 : 31 * Δα * ((x 2 : ℝ) - x 4) + 462 * Δβ * (x 4 : ℝ) = 0 := by
    linear_combination Ec1 - Ea1 + 31 * ((x 2 : ℝ) - x 4) * hΔα + 462 * (x 4 : ℝ) * hΔβ
  have D2 : -15 * Δα * ((x 0 : ℝ) - x 4) + 462 * Δγ * (x 4 : ℝ) = 0 := by
    linear_combination Ec2 - Ea2 - 15 * ((x 0 : ℝ) - x 4) * hΔα + 462 * (x 4 : ℝ) * hΔγ
  have D3 : 15 * Δβ * ((x 0 : ℝ) - x 4) + 31 * Δγ * ((x 2 : ℝ) - x 4) = 0 := by
    linear_combination Ea3 - Ec3 + 15 * ((x 0 : ℝ) - x 4) * hΔβ + 31 * ((x 2 : ℝ) - x 4) * hΔγ
  have D1' : 31 * Δα * ((x' 2 : ℝ) - x' 4) + 462 * Δβ * (x' 4 : ℝ) = 0 := by
    linear_combination Ed1 - Eb1 + 31 * ((x' 2 : ℝ) - x' 4) * hΔα + 462 * (x' 4 : ℝ) * hΔβ
  have D2' : -15 * Δα * ((x' 0 : ℝ) - x' 4) + 462 * Δγ * (x' 4 : ℝ) = 0 := by
    linear_combination Ed2 - Eb2 - 15 * ((x' 0 : ℝ) - x' 4) * hΔα + 462 * (x' 4 : ℝ) * hΔγ
  have D3' : 15 * Δβ * ((x' 0 : ℝ) - x' 4) + 31 * Δγ * ((x' 2 : ℝ) - x' 4) = 0 := by
    linear_combination Eb3 - Ed3 + 15 * ((x' 0 : ℝ) - x' 4) * hΔβ + 31 * ((x' 2 : ℝ) - x' 4) * hΔγ
  -- reduce to the three free coordinates
  suffices hs : (x 0 : ℝ) - x 4 = x' 0 - x' 4 ∧ (x 2 : ℝ) - x 4 = x' 2 - x' 4 ∧ (x 4 : ℝ) = x' 4 by
    obtain ⟨hu, hv, hw⟩ := hs
    have h4 : x 4 = x' 4 := by exact_mod_cast hw
    have h0 : x 0 = x' 0 := by
      have : (x 0 : ℝ) = x' 0 := by linarith
      exact_mod_cast this
    have h2 : x 2 = x' 2 := by
      have : (x 2 : ℝ) = x' 2 := by linarith
      exact_mod_cast this
    have h1 : x 1 = x' 1 := by
      have : q * (x 1 - x 4) = q * (x' 1 - x' 4) := by rw [e1, e1', h2, h4]
      have := mul_left_cancel₀ hq.ne' this
      omega
    have h3 : x 3 = x' 3 := by
      have : q * (x 3 - x 4) = q * (x' 3 - x' 4) := by rw [e2, e2', h0, h4]
      have := mul_left_cancel₀ hq.ne' this
      omega
    have h5 : x 5 = x' 5 := by omega
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  by_cases hΔ : Δα = 0 ∧ Δβ = 0 ∧ Δγ = 0
  · -- the planes coincide: contradiction with hne
    exfalso
    obtain ⟨hα0, hβ0, hγ0⟩ := hΔ
    have hAq : (A : ℝ) * q' = A' * q := by
      rw [hα0] at hΔα
      field_simp at hΔα
      linear_combination -hΔα
    have hBq : (B : ℝ) * q' = B' * q := by
      rw [hβ0] at hΔβ
      field_simp at hΔβ
      linear_combination -hΔβ
    have hCq : (C : ℝ) * q' = C' * q := by
      rw [hγ0] at hΔγ
      field_simp at hΔγ
      linear_combination -hΔγ
    have hAqZ : A * q' = A' * q := by exact_mod_cast hAq
    have hBqZ : B * q' = B' * q := by exact_mod_cast hBq
    have hCqZ : C * q' = C' * q := by exact_mod_cast hCq
    have hqq' : q ∣ q' := hA.symm.dvd_of_dvd_mul_right ⟨A', by rw [mul_comm q' A, hAqZ]; ring⟩
    have hq'q : q' ∣ q := hA'.symm.dvd_of_dvd_mul_right ⟨A, by rw [mul_comm q A', ← hAqZ]; ring⟩
    have hqe : q = q' := Int.dvd_antisymm hq.le hq'.le hqq' hq'q
    subst hqe
    have hAe : A = A' := mul_right_cancel₀ hq.ne' hAqZ
    have hBe : B = B' := mul_right_cancel₀ hq.ne' hBqZ
    have hCe : C = C' := mul_right_cancel₀ hq.ne' hCqZ
    exact hne (by rw [hAe, hBe, hCe])
  · by_cases hα : Δα ≠ 0
    · -- w (Δα + 462(βΔγ - γΔβ)) = -Δα at both points
      have T : (x 4 : ℝ) * (Δα + 462 * ((B : ℝ) / q * Δγ - (C : ℝ) / q * Δβ)) + Δα = 0 := by
        linear_combination Δα * Ea3 + ((B : ℝ) / q) * D2 - ((C : ℝ) / q) * D1
      have T' : (x' 4 : ℝ) * (Δα + 462 * ((B : ℝ) / q * Δγ - (C : ℝ) / q * Δβ)) + Δα = 0 := by
        linear_combination Δα * Eb3 + ((B : ℝ) / q) * D2' - ((C : ℝ) / q) * D1'
      have hw : (x 4 : ℝ) = x' 4 := by
        have : ((x 4 : ℝ) - x' 4) * (Δα + 462 * ((B : ℝ) / q * Δγ - (C : ℝ) / q * Δβ)) = 0 := by
          linear_combination T - T'
        rcases mul_eq_zero.mp this with h | h
        · linarith
        · exfalso; apply hα; rw [h] at T; linarith
      have hu : (x 0 : ℝ) - x 4 = x' 0 - x' 4 := by
        have : (15 * Δα) * ((x 0 : ℝ) - x 4) = (15 * Δα) * (x' 0 - x' 4) := by
          linear_combination -D2 + D2' + 462 * Δγ * hw
        exact mul_left_cancel₀ (mul_ne_zero (by norm_num) hα) this
      have hv : (x 2 : ℝ) - x 4 = x' 2 - x' 4 := by
        have : (31 * Δα) * ((x 2 : ℝ) - x 4) = (31 * Δα) * (x' 2 - x' 4) := by
          linear_combination D1 - D1' - 462 * Δβ * hw
        exact mul_left_cancel₀ (mul_ne_zero (by norm_num) hα) this
      exact ⟨hu, hv, hw⟩
    · push Not at hα
      by_cases hβ : Δβ ≠ 0
      · have hw0 : (x 4 : ℝ) = 0 := by
          have : (462 * Δβ) * (x 4 : ℝ) = 0 := by linear_combination D1 - 31 * ((x 2 : ℝ) - x 4) * hα
          exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero (by norm_num) hβ)
        have hw0' : (x' 4 : ℝ) = 0 := by
          have : (462 * Δβ) * (x' 4 : ℝ) = 0 := by linear_combination D1' - 31 * ((x' 2 : ℝ) - x' 4) * hα
          exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero (by norm_num) hβ)
        have T : ((x 2 : ℝ) - x 4) * (31 * ((B : ℝ) / q * Δγ - (C : ℝ) / q * Δβ)) - Δβ = 0 := by
          linear_combination -Δβ * Ea3 + ((B : ℝ) / q) * D3 + Δβ * hw0
        have T' : ((x' 2 : ℝ) - x' 4) * (31 * ((B : ℝ) / q * Δγ - (C : ℝ) / q * Δβ)) - Δβ = 0 := by
          linear_combination -Δβ * Eb3 + ((B : ℝ) / q) * D3' + Δβ * hw0'
        have hv : (x 2 : ℝ) - x 4 = x' 2 - x' 4 := by
          have : (((x 2 : ℝ) - x 4) - (x' 2 - x' 4)) * (31 * ((B : ℝ) / q * Δγ - (C : ℝ) / q * Δβ)) = 0 := by
            linear_combination T - T'
          rcases mul_eq_zero.mp this with h | h
          · linarith
          · exfalso; apply hβ; rw [h] at T; linarith
        have hu : (x 0 : ℝ) - x 4 = x' 0 - x' 4 := by
          have : (15 * Δβ) * ((x 0 : ℝ) - x 4) = (15 * Δβ) * (x' 0 - x' 4) := by
            linear_combination D3 - D3' - 31 * Δγ * hv
          exact mul_left_cancel₀ (mul_ne_zero (by norm_num) hβ) this
        exact ⟨hu, hv, by rw [hw0, hw0']⟩
      · push Not at hβ
        have hγ : Δγ ≠ 0 := by
          intro hγ0
          exact hΔ ⟨hα, hβ, hγ0⟩
        have hw0 : (x 4 : ℝ) = 0 := by
          have : (462 * Δγ) * (x 4 : ℝ) = 0 := by linear_combination D2 + 15 * ((x 0 : ℝ) - x 4) * hα
          exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero (by norm_num) hγ)
        have hw0' : (x' 4 : ℝ) = 0 := by
          have : (462 * Δγ) * (x' 4 : ℝ) = 0 := by linear_combination D2' + 15 * ((x' 0 : ℝ) - x' 4) * hα
          exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero (by norm_num) hγ)
        have hv0 : (x 2 : ℝ) - x 4 = 0 := by
          have : (31 * Δγ) * ((x 2 : ℝ) - x 4) = 0 := by linear_combination D3 - 15 * ((x 0 : ℝ) - x 4) * hβ
          exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero (by norm_num) hγ)
        have hv0' : (x' 2 : ℝ) - x' 4 = 0 := by
          have : (31 * Δγ) * ((x' 2 : ℝ) - x' 4) = 0 := by linear_combination D3' - 15 * ((x' 0 : ℝ) - x' 4) * hβ
          exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero (by norm_num) hγ)
        -- E3: 1 = -15 (B/q) u at both points
        have T : 15 * ((B : ℝ) / q) * ((x 0 : ℝ) - x 4) = -1 := by
          linear_combination Ea3 - 31 * ((C : ℝ) / q) * hv0 - hw0
        have T' : 15 * ((B : ℝ) / q) * ((x' 0 : ℝ) - x' 4) = -1 := by
          linear_combination Eb3 - 31 * ((C : ℝ) / q) * hv0' - hw0'
        have hB0 : (B : ℝ) / q ≠ 0 := by
          intro h0; rw [h0] at T; norm_num at T
        have hu : (x 0 : ℝ) - x 4 = x' 0 - x' 4 := by
          have : (15 * ((B : ℝ) / q)) * ((x 0 : ℝ) - x 4) = (15 * ((B : ℝ) / q)) * (x' 0 - x' 4) := by
            linear_combination T - T'
          exact mul_left_cancel₀ (mul_ne_zero (by norm_num) hB0) this
        exact ⟨hu, by rw [hv0, hv0'], by rw [hw0, hw0']⟩

-- N33 union_card_bound [extremal_averaging]
theorem union_card_bound {ι α : Type*} [DecidableEq α] (s : Finset ι) (f : ι → Finset α)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (f i ∩ f j).card ≤ 1) :
    ∑ i ∈ s, (f i).card ≤ (s.biUnion f).card + s.card.choose 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.biUnion_insert, Finset.card_insert_of_notMem ha]
    have ih' := ih (fun i hi j hj hij => h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij)
    -- card (f a ∩ biUnion) ≤ s.card
    have hinter : (f a ∩ s.biUnion f).card ≤ s.card := by
      rw [Finset.inter_biUnion]
      calc (s.biUnion fun j => f a ∩ f j).card ≤ ∑ j ∈ s, (f a ∩ f j).card := Finset.card_biUnion_le
        _ ≤ ∑ j ∈ s, 1 := by
            apply Finset.sum_le_sum
            intro j hj
            have hne : a ≠ j := fun h' => ha (h' ▸ hj)
            exact h a (Finset.mem_insert_self a s) j (Finset.mem_insert_of_mem hj) hne
        _ = s.card := by simp
    have hunion := Finset.card_union_add_card_inter (f a) (s.biUnion f)
    have hch : (s.card + 1).choose 2 = s.card + s.card.choose 2 := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
    rw [hch]
    omega

-- N34 lattice_reduction [algebraic_identity]
theorem lattice_reduction {ι : Type*} [Fintype ι] (p : ℕ) (L L' : AddSubgroup (ι → ℤ)) (hle : L' ≤ L)
    (hp : ¬ p ∣ L'.relIndex L) :
    (∀ x ∈ L, ∃ y ∈ L', ∃ z ∈ L, x = y + p • z) ∧
    (∀ y ∈ L', (∃ z ∈ L, y = p • z) → ∃ z' ∈ L', y = p • z') := by
  classical
  set m := L'.relIndex L with hm
  have hmem : ∀ x ∈ L, m • x ∈ L' := by
    intro x hx
    have h := AddSubgroup.nsmul_index_mem (L'.addSubgroupOf L) (⟨x, hx⟩ : L)
    rw [AddSubgroup.mem_addSubgroupOf] at h
    rw [hm, AddSubgroup.relIndex]
    simpa using h
  -- Bezout step. NOTE: this is where the statement fails as drawn: `p` is an arbitrary natural number,
  -- not assumed prime, so `¬ p ∣ m` does not give coprimality (p = 4, m = 2; or p = 0 with m ≠ 0).
  have hcop : IsCoprime (m : ℤ) (p : ℤ) := by
    sorry
  obtain ⟨a, b, hab⟩ := hcop
  constructor
  · intro x hx
    refine ⟨a • (m • x), L'.zsmul_mem (hmem x hx) a, b • x, L.zsmul_mem hx b, ?_⟩
    rw [show a • (m • x) + p • (b • x) = (a * (m : ℤ) + (p : ℤ) * b) • x by
      rw [add_zsmul, mul_zsmul, mul_zsmul, natCast_zsmul, natCast_zsmul],
      show a * (m : ℤ) + (p : ℤ) * b = 1 by rw [mul_comm (p : ℤ) b]; exact hab, one_zsmul]
  · rintro y hy ⟨z, hz, hyz⟩
    refine ⟨z, ?_, hyz⟩
    have hz' : z = a • (m • z) + b • y := by
      rw [hyz, show a • (m • z) + b • (p • z) = (a * (m : ℤ) + b * (p : ℤ)) • z by
        rw [add_zsmul, mul_zsmul, mul_zsmul, natCast_zsmul, natCast_zsmul], hab, one_zsmul]
    rw [hz']
    exact L'.add_mem (L'.zsmul_mem (hmem z hz) a) (L'.zsmul_mem hy b)

lemma zero_set_card_le (p : ℕ) (hp : p.Prime) (a : ℤ) (b : Fin 2 → ℤ)
    (hnz : ¬ ((p : ℤ) ∣ a ∧ ∀ j, (p : ℤ) ∣ b j)) :
    ((Fintype.piFinset fun _ : Fin 2 => Finset.range p).filter
      fun n => (p : ℤ) ∣ a + ∑ j, b j * (n j : ℤ)).card ≤ p := by
  classical
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  -- the key cancellation: two zero points agreeing in one coordinate agree in the other
  have cancel : ∀ (k : Fin 2) (n m : Fin 2 → ℕ), ¬ (p : ℤ) ∣ b k → n k < p → m k < p →
      (p : ℤ) ∣ b k * ((n k : ℤ) - m k) → n k = m k := by
    intro k n m hk hn hm hd
    have hd' : (p : ℤ) ∣ (n k : ℤ) - m k := (hpZ.dvd_or_dvd hd).resolve_left hk
    obtain ⟨t, ht⟩ := hd'
    have h1 : (n k : ℤ) - m k < p := by omega
    have h2 : -(p : ℤ) < (n k : ℤ) - m k := by omega
    have ht0 : t = 0 := by
      rcases lt_trichotomy t 0 with h | h | h
      · nlinarith
      · exact h
      · nlinarith
    rw [ht0, mul_zero] at ht
    omega
  by_cases h0 : (p : ℤ) ∣ b 0
  · by_cases h1 : (p : ℤ) ∣ b 1
    · have ha : ¬ (p : ℤ) ∣ a := fun ha => hnz ⟨ha, fun j => by fin_cases j <;> assumption⟩
      have hempty : ((Fintype.piFinset fun _ : Fin 2 => Finset.range p).filter
          fun n => (p : ℤ) ∣ a + ∑ j, b j * (n j : ℤ)) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro n _ hdiv
        apply ha
        have hs : (p : ℤ) ∣ ∑ j, b j * (n j : ℤ) :=
          Finset.dvd_sum fun j _ => Dvd.dvd.mul_right (by fin_cases j <;> assumption) _
        have := Int.dvd_sub hdiv hs
        simpa using this
      rw [hempty]
      simp
    · -- project onto coordinate 0
      calc _ ≤ (Finset.range p).card := by
            apply Finset.card_le_card_of_injOn (fun n => n 0)
            · intro n hn
              simp only [Finset.coe_filter, Set.mem_ofPred_eq, Fintype.mem_piFinset] at hn
              exact hn.1 0
            · intro n hn m hm hnm
              simp only [Finset.coe_filter, Set.mem_ofPred_eq, Fintype.mem_piFinset] at hn hm
              simp only at hnm
              have hd : (p : ℤ) ∣ b 1 * ((n 1 : ℤ) - m 1) := by
                have h := Int.dvd_sub hn.2 hm.2
                rw [Fin.sum_univ_two, Fin.sum_univ_two, hnm] at h
                have e : a + (b 0 * (m 0 : ℤ) + b 1 * (n 1 : ℤ)) - (a + (b 0 * (m 0 : ℤ) + b 1 * (m 1 : ℤ)))
                    = b 1 * ((n 1 : ℤ) - m 1) := by ring
                rwa [e] at h
              have := cancel 1 n m h1 (Finset.mem_range.mp (hn.1 1)) (Finset.mem_range.mp (hm.1 1)) hd
              funext j
              fin_cases j
              · exact hnm
              · exact this
        _ = p := Finset.card_range p
  · -- project onto coordinate 1
    calc _ ≤ (Finset.range p).card := by
          apply Finset.card_le_card_of_injOn (fun n => n 1)
          · intro n hn
            simp only [Finset.coe_filter, Set.mem_ofPred_eq, Fintype.mem_piFinset] at hn
            exact hn.1 1
          · intro n hn m hm hnm
            simp only [Finset.coe_filter, Set.mem_ofPred_eq, Fintype.mem_piFinset] at hn hm
            simp only at hnm
            have hd : (p : ℤ) ∣ b 0 * ((n 0 : ℤ) - m 0) := by
              have h := Int.dvd_sub hn.2 hm.2
              rw [Fin.sum_univ_two, Fin.sum_univ_two, hnm] at h
              have e : a + (b 0 * (n 0 : ℤ) + b 1 * (m 1 : ℤ)) - (a + (b 0 * (m 0 : ℤ) + b 1 * (m 1 : ℤ)))
                  = b 0 * ((n 0 : ℤ) - m 0) := by ring
              rwa [e] at h
            have := cancel 0 n m h0 (Finset.mem_range.mp (hn.1 0)) (Finset.mem_range.mp (hm.1 0)) hd
            funext j
            fin_cases j
            · exact this
            · exact hnm
      _ = p := Finset.card_range p

-- N35 nonzero_forms_count [extremal_averaging]
theorem nonzero_forms_count (p : ℕ) (hp : p.Prime) (c : Fin 6 → ℤ) (L : Fin 6 → Fin 2 → ℤ)
    (hnz : ∀ i, ¬ ((p : ℤ) ∣ c i ∧ ∀ j, (p : ℤ) ∣ L i j)) :
    p ^ 2 - 6 * p ≤ ((Fintype.piFinset fun _ : Fin 2 => Finset.range p).filter
      (fun n => ∀ i, ¬ (p : ℤ) ∣ c i + ∑ j, L i j * (n j : ℤ))).card := by
  classical
  set U := (Fintype.piFinset fun _ : Fin 2 => Finset.range p) with hU
  have hUcard : U.card = p ^ 2 := by rw [hU, Fintype.card_piFinset]; simp
  have hcompl : U.filter (fun n => ¬ ∀ i, ¬ (p : ℤ) ∣ c i + ∑ j, L i j * (n j : ℤ)) ⊆
      Finset.univ.biUnion (fun i : Fin 6 => U.filter (fun n => (p : ℤ) ∣ c i + ∑ j, L i j * (n j : ℤ))) := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hn1, hn2⟩ := hn
    push Not at hn2
    obtain ⟨i, hi⟩ := hn2
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hn1, hi⟩⟩
  have hbad : (U.filter (fun n => ¬ ∀ i, ¬ (p : ℤ) ∣ c i + ∑ j, L i j * (n j : ℤ))).card ≤ 6 * p := by
    calc _ ≤ (Finset.univ.biUnion (fun i : Fin 6 =>
          U.filter (fun n => (p : ℤ) ∣ c i + ∑ j, L i j * (n j : ℤ)))).card := Finset.card_le_card hcompl
      _ ≤ ∑ i : Fin 6, (U.filter (fun n => (p : ℤ) ∣ c i + ∑ j, L i j * (n j : ℤ))).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ i : Fin 6, p := Finset.sum_le_sum (fun i _ => zero_set_card_le p hp (c i) (L i) (hnz i))
      _ = 6 * p := by simp
  have hsplit : (U.filter (fun n => ∀ i, ¬ (p : ℤ) ∣ c i + ∑ j, L i j * (n j : ℤ))).card +
      (U.filter (fun n => ¬ ∀ i, ¬ (p : ℤ) ∣ c i + ∑ j, L i j * (n j : ℤ))).card = U.card :=
    Finset.card_filter_add_card_filter_not _
  generalize hP : p ^ 2 = P at hUcard ⊢
  omega

-- N36 local_W [assembly]
theorem local_W (OnPl : ℤ → ℤ → ℤ → ℤ → (Fin 6 → ℤ) → Prop)
    (hOnPl : ∀ q A B C (x : Fin 6 → ℤ), OnPl q A B C x ↔
      (q * (x 1 - x 4) = 31 * A * (x 2 - x 4) + 462 * B * x 4 ∧
       q * (x 3 - x 4) = -15 * A * (x 0 - x 4) + 462 * C * x 4 ∧
       q * (x 4 + 1) = -(15 * B * (x 0 - x 4) + 31 * C * (x 2 - x 4)) ∧
       508 * x 5 = 15 * (x 0 + x 1) + 31 * (x 2 + x 3) - 508 * x 4 - 462))
    (q : ℕ) (A B C : ℤ) (hq1 : 1 ≤ q) (hqW : q % 4619990760 = 1) (hA : (4619990760 : ℤ) ∣ A) (hB : (4619990760 : ℤ) ∣ B) (hC : (4619990760 : ℤ) ∣ C)
    (hCq : IsCoprime C (q : ℤ)) (c : Fin 6 → ℤ) (L : Fin 6 → Fin 2 → ℤ)
    (hpar : ∀ n : Fin 2 → ℤ, OnPl q A B C (fun i => c i + ∑ j, L i j * n j))
    (hsurj : ∀ x, OnPl q A B C x → ∃ n : Fin 2 → ℤ, x = fun i => c i + ∑ j, L i j * n j) :
    ∀ p : ℕ, p.Prime → p ∣ 4619990760 →
      ∃ n : Fin 2 → ℕ, (∀ j, n j < p) ∧ ∀ i, ¬ (p : ℤ) ∣ c i + ∑ j, L i j * (n j : ℤ) := by
  intro p hp hpW
  obtain ⟨x, hx, hunit⟩ := local_witness OnPl hOnPl q A B C hq1 hqW hA hB hC hCq
  obtain ⟨n₀, hn₀⟩ := hsurj x hx
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  refine ⟨fun j => (n₀ j % (p : ℤ)).toNat, fun j => ?_, fun i hdiv => ?_⟩
  · show (n₀ j % (p : ℤ)).toNat < p
    have h1 := Int.emod_lt_of_pos (n₀ j) hp0
    have h2 := Int.emod_nonneg (n₀ j) hp0.ne'
    omega
  · apply hunit p hp hpW i
    have hcast : ∀ j, (((n₀ j % (p : ℤ)).toNat : ℕ) : ℤ) = n₀ j % p := fun j =>
      Int.toNat_of_nonneg (Int.emod_nonneg _ hp0.ne')
    simp only [hcast] at hdiv
    have hXY : (p : ℤ) ∣ (c i + ∑ j, L i j * (n₀ j % p)) - (c i + ∑ j, L i j * n₀ j) := by
      have : (c i + ∑ j, L i j * (n₀ j % p)) - (c i + ∑ j, L i j * n₀ j) =
          ∑ j, L i j * (n₀ j % p - n₀ j) := by
        simp only [mul_sub, Finset.sum_sub_distrib]; ring
      rw [this]
      apply Finset.dvd_sum
      intro j _
      apply Dvd.dvd.mul_left
      rw [Int.emod_def]
      exact ⟨-(n₀ j / p), by ring⟩
    have hfin := Int.dvd_sub hdiv hXY
    rw [sub_sub_cancel] at hfin
    rw [hn₀]
    exact hfin

-- N37 local_away [two_structure_coupling]
theorem local_away (OnPl : ℤ → ℤ → ℤ → ℤ → (Fin 6 → ℤ) → Prop)
    (hOnPl : ∀ q A B C (x : Fin 6 → ℤ), OnPl q A B C x ↔
      (q * (x 1 - x 4) = 31 * A * (x 2 - x 4) + 462 * B * x 4 ∧
       q * (x 3 - x 4) = -15 * A * (x 0 - x 4) + 462 * C * x 4 ∧
       q * (x 4 + 1) = -(15 * B * (x 0 - x 4) + 31 * C * (x 2 - x 4)) ∧
       508 * x 5 = 15 * (x 0 + x 1) + 31 * (x 2 + x 3) - 508 * x 4 - 462))
    (Good : ℝ → ℕ → ℤ → ℤ → ℤ → Prop)
    (hGood : ∀ Z q A B C, Good Z q A B C ↔
      ((4619990760 : ℤ) ∣ A ∧ (4619990760 : ℤ) ∣ B ∧ (4619990760 : ℤ) ∣ C ∧
       (q : ℝ) * Z ^ 2 ≤ A ∧ (A : ℝ) < 2 * q * Z ^ 2 ∧
       (q : ℝ) * Z ≤ B ∧ (B : ℝ) < 2 * q * Z ∧
       (q : ℝ) * Z ≤ C ∧ (C : ℝ) < 2 * q * Z ∧
       (∀ p : ℕ, p.Prime → p ∣ q →
         ¬ (p : ℤ) ∣ A * B * C * (462 * C + 15 * A) * (31 * A - 462 * B) * (15 * B + 31 * C)) ∧
       (∀ p : ℕ, p.Prime → ¬ p ∣ 4619990760 * q →
         ¬ (((p : ℤ) ∣ A ∧ (p : ℤ) ∣ 462 * B + q) ∨ ((p : ℤ) ∣ A ∧ (p : ℤ) ∣ 462 * C + q) ∨
           ((p : ℤ) ∣ 31 * A - 462 * B - q ∧ (p : ℤ) ∣ 15 * A + 462 * C + q)))))
    (q : ℕ) (A B C : ℤ) (Z : ℝ)
    (hq1 : 1 ≤ q) (hqW : q % 4619990760 = 1) (hZ : 100 ≤ Z) (hG : Good Z q A B C)
    (c : Fin 6 → ℤ) (L : Fin 6 → Fin 2 → ℤ)
    (hpar : ∀ n : Fin 2 → ℤ, OnPl q A B C (fun i => c i + ∑ j, L i j * n j))
    (hsurj : ∀ x, OnPl q A B C x → ∃ n : Fin 2 → ℤ, x = fun i => c i + ∑ j, L i j * n j)
    (hdet : ∃ δ : ℕ, δ ∣ 508 ∧
      |15 * (L 0 0 - L 4 0) * (31 * (L 2 1 - L 4 1)) - 15 * (L 0 1 - L 4 1) * (31 * (L 2 0 - L 4 0))|
        = 465 * (q : ℤ) ^ 2 * δ) :
    ∀ p : ℕ, p.Prime → ¬ p ∣ 4619990760 * q → ∀ i, ¬ ((p : ℤ) ∣ c i ∧ ∀ j, (p : ℤ) ∣ L i j) := by
  intro p hp hpWq i ⟨hci, hLi⟩
  obtain ⟨hWA, hWB, hWC, -, -, -, -, -, -, -, hgood⟩ := (hGood Z q A B C).mp hG
  have hbad := hgood p hp hpWq
  obtain ⟨δ, hδ, hdet'⟩ := hdet
  haveI := Fact.mk hp
  have hpW : ¬ p ∣ 4619990760 := fun h => hpWq (Dvd.dvd.mul_right h q)
  have hpq : ¬ p ∣ q := fun h => hpWq (Dvd.dvd.mul_left h _)
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  -- numerals that are units mod p
  have hnum : ∀ k : ℕ, k ∣ 4619990760 → (k : ZMod p) ≠ 0 := fun k hk h =>
    hpW ((ZMod.natCast_eq_zero_iff k p).mp h |>.trans hk)
  have hq0 : (q : ZMod p) ≠ 0 := fun h => hpq ((ZMod.natCast_eq_zero_iff q p).mp h)
  have h15 : (15 : ZMod p) ≠ 0 := by have := hnum 15 (by norm_num); exact_mod_cast this
  have h31 : (31 : ZMod p) ≠ 0 := by have := hnum 31 (by norm_num); exact_mod_cast this
  -- the determinant is a unit mod p
  have hDp : ¬ (p : ℤ) ∣ 15 * (L 0 0 - L 4 0) * (31 * (L 2 1 - L 4 1)) -
      15 * (L 0 1 - L 4 1) * (31 * (L 2 0 - L 4 0)) := by
    intro h
    have h' := (dvd_abs (p : ℤ) _).mpr h
    rw [hdet'] at h'
    rcases hpZ.dvd_or_dvd h' with h1 | h1
    · rcases hpZ.dvd_or_dvd h1 with h2 | h2
      · exact hpW ((Int.natCast_dvd_natCast.mp (h2 : (p : ℤ) ∣ ((465 : ℕ) : ℤ))).trans (by norm_num))
      · exact hpq (Int.natCast_dvd_natCast.mp (hpZ.dvd_of_dvd_pow h2))
    · exact hpW ((Int.natCast_dvd_natCast.mp h1).trans (hδ.trans (by norm_num)))
  have hd : ((L 0 0 : ZMod p) - L 4 0) * ((L 2 1 : ZMod p) - L 4 1) -
      ((L 0 1 : ZMod p) - L 4 1) * ((L 2 0 : ZMod p) - L 4 0) ≠ 0 := by
    intro h
    apply hDp
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    linear_combination 465 * h
  -- the plane over ZMod p
  set X : (Fin 2 → ZMod p) → Fin 6 → ZMod p := fun m i => (c i : ZMod p) + ∑ j, (L i j : ZMod p) * m j
    with hXdef
  have hE : ∀ m : Fin 2 → ZMod p,
      (q : ZMod p) * (X m 1 - X m 4) = 31 * A * (X m 2 - X m 4) + 462 * B * X m 4 ∧
      (q : ZMod p) * (X m 3 - X m 4) = -15 * A * (X m 0 - X m 4) + 462 * C * X m 4 ∧
      (q : ZMod p) * (X m 4 + 1) = -(15 * B * (X m 0 - X m 4) + 31 * C * (X m 2 - X m 4)) ∧
      508 * X m 5 = 15 * (X m 0 + X m 1) + 31 * (X m 2 + X m 3) - 508 * X m 4 - 462 := by
    intro m
    obtain ⟨e1, e2, e3, e4⟩ := (hOnPl q A B C _).mp (hpar (fun j => ((m j).cast : ℤ)))
    have hX : ∀ i, X m i = ((c i + ∑ j, L i j * ((m j).cast : ℤ) : ℤ) : ZMod p) := by
      intro i
      simp [hXdef, ZMod.intCast_zmod_cast]
    have e1' := congrArg (Int.cast : ℤ → ZMod p) e1
    have e2' := congrArg (Int.cast : ℤ → ZMod p) e2
    have e3' := congrArg (Int.cast : ℤ → ZMod p) e3
    have e4' := congrArg (Int.cast : ℤ → ZMod p) e4
    simp only [hX]
    push_cast at e1' e2' e3' e4' ⊢
    exact ⟨e1', e2', e3', e4'⟩
  have hzero : ∀ m, X m i = 0 := by
    intro m
    have hc : (c i : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hci
    have hL : ∀ j, (L i j : ZMod p) = 0 := fun j => (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (hLi j)
    simp [hXdef, hc, hL]
  -- every (u, v) ∈ (ZMod p)² is attained
  have hpoint : ∀ t0 t1 : ZMod p, ∃ m : Fin 2 → ZMod p, X m 0 - X m 4 = t0 ∧ X m 2 - X m 4 = t1 := by
    intro t0 t1
    obtain ⟨e, he⟩ : ∃ e : ZMod p, e * (((L 0 0 : ZMod p) - L 4 0) * ((L 2 1 : ZMod p) - L 4 1) -
        ((L 0 1 : ZMod p) - L 4 1) * ((L 2 0 : ZMod p) - L 4 0)) = 1 := ⟨_, inv_mul_cancel₀ hd⟩
    refine ⟨![e * (((L 2 1 : ZMod p) - L 4 1) * (t0 - ((c 0 : ZMod p) - c 4)) -
        ((L 0 1 : ZMod p) - L 4 1) * (t1 - ((c 2 : ZMod p) - c 4))),
      e * (-((L 2 0 : ZMod p) - L 4 0) * (t0 - ((c 0 : ZMod p) - c 4)) +
        ((L 0 0 : ZMod p) - L 4 0) * (t1 - ((c 2 : ZMod p) - c 4)))], ?_, ?_⟩
    · simp only [hXdef, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      linear_combination (t0 - ((c 0 : ZMod p) - c 4)) * he
    · simp only [hXdef, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      linear_combination (t1 - ((c 2 : ZMod p) - c 4)) * he
  -- the three sample points
  obtain ⟨m0, hu0, hv0⟩ := hpoint 0 0
  obtain ⟨m1, hu1, hv1⟩ := hpoint 1 0
  obtain ⟨m2, hu2, hv2⟩ := hpoint 0 1
  obtain ⟨e1, e2, e3, e4⟩ := hE m0
  obtain ⟨f1, f2, f3, f4⟩ := hE m1
  obtain ⟨g1, g2, g3, g4⟩ := hE m2
  have z0 := hzero m0
  have z1 := hzero m1
  have z2 := hzero m2
  have hx4 : X m0 4 = -1 := by
    rw [hu0, hv0] at e3
    have : (q : ZMod p) * (X m0 4 + 1) = 0 := by rw [e3]; ring
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hq0
    · linear_combination h
  have hx0 : X m0 0 = -1 := by linear_combination hu0 + hx4
  have hx2 : X m0 2 = -1 := by linear_combination hv0 + hx4
  have hy0 : X m1 0 = X m1 4 + 1 := by linear_combination hu1
  have hy2 : X m1 2 = X m1 4 := by linear_combination hv1
  have hw0 : X m2 0 = X m2 4 := by linear_combination hu2
  have hw2 : X m2 2 = X m2 4 + 1 := by linear_combination hv2
  clear hpoint hE hzero
  fin_cases i
  · -- i = 0 : X0 ≡ 0 forces X4(m0) = 0, then q = 0
    simp only [Fin.zero_eta, Fin.isValue] at z0
    exact one_ne_zero (by linear_combination hx0 - z0 : (1 : ZMod p) = 0)
  · -- i = 1
    simp only [Fin.mk_one, Fin.isValue] at z0 z2
    rw [z0, hv0, hx4] at e1
    have hB : 462 * (B : ZMod p) + q = 0 := by linear_combination e1
    rw [z2, hv2] at g1
    have h31A : 31 * (A : ZMod p) = 0 := by linear_combination -g1 - (X m2 4) * hB
    have hA : (A : ZMod p) = 0 := (mul_eq_zero.mp h31A).resolve_left h31
    exact hbad (Or.inl ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd A p).mp hA,
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp (by push_cast; exact hB)⟩)
  · -- i = 2
    simp only [Fin.reduceFinMk, Fin.isValue] at z0
    exact one_ne_zero (by linear_combination hx2 - z0 : (1 : ZMod p) = 0)
  · -- i = 3
    simp only [Fin.reduceFinMk, Fin.isValue] at z0 z1
    rw [z0, hu0, hx4] at e2
    have hC : 462 * (C : ZMod p) + q = 0 := by linear_combination e2
    rw [z1, hu1] at f2
    have h15A : 15 * (A : ZMod p) = 0 := by linear_combination f2 + (X m1 4) * hC
    have hA : (A : ZMod p) = 0 := (mul_eq_zero.mp h15A).resolve_left h15
    exact hbad (Or.inr (Or.inl ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd A p).mp hA,
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp (by push_cast; exact hC)⟩))
  · -- i = 4
    simp only [Fin.reduceFinMk, Fin.isValue] at z0
    exact one_ne_zero (by linear_combination hx4 - z0 : (1 : ZMod p) = 0)
  · -- i = 5
    simp only [Fin.reduceFinMk, Fin.isValue] at z0 z1 z2
    rw [hx2, hx4] at e1
    rw [hx0, hx4] at e2
    rw [hx0, hx2, hx4, z0] at e4
    have hstar : 6930 * (B : ZMod p) + 14322 * C + 46 * q = 0 := by
      linear_combination 15 * e1 + 31 * e2 + (q : ZMod p) * e4
    rw [hv1] at f1
    rw [hu1] at f2
    rw [hu1, hv1] at f3
    rw [hy0, hy2, z1] at f4
    have hG1 : 15 * (31 * (A : ZMod p) - 462 * B - q) = 0 := by
      linear_combination (q : ZMod p) * f4 + 15 * f1 + 31 * f2 + (X m1 4) * hstar - 462 * f3
    rw [hv2] at g1
    rw [hu2] at g2
    rw [hu2, hv2] at g3
    rw [hw0, hw2, z2] at g4
    have hG2 : 31 * (15 * (A : ZMod p) + 462 * C + q) = 0 := by
      linear_combination -((q : ZMod p) * g4 + 15 * g1 + 31 * g2 + (X m2 4) * hstar - 462 * g3)
    have hG1' := (mul_eq_zero.mp hG1).resolve_left h15
    have hG2' := (mul_eq_zero.mp hG2).resolve_left h31
    exact hbad (Or.inr (Or.inr ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp (by push_cast; exact hG1'),
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp (by push_cast; exact hG2')⟩))

-- N38 local_denominator [two_structure_coupling]
theorem local_denominator (OnPl : ℤ → ℤ → ℤ → ℤ → (Fin 6 → ℤ) → Prop)
    (hOnPl : ∀ q A B C (x : Fin 6 → ℤ), OnPl q A B C x ↔
      (q * (x 1 - x 4) = 31 * A * (x 2 - x 4) + 462 * B * x 4 ∧
       q * (x 3 - x 4) = -15 * A * (x 0 - x 4) + 462 * C * x 4 ∧
       q * (x 4 + 1) = -(15 * B * (x 0 - x 4) + 31 * C * (x 2 - x 4)) ∧
       508 * x 5 = 15 * (x 0 + x 1) + 31 * (x 2 + x 3) - 508 * x 4 - 462))
    (Good : ℝ → ℕ → ℤ → ℤ → ℤ → Prop)
    (hGood : ∀ Z q A B C, Good Z q A B C ↔
      ((4619990760 : ℤ) ∣ A ∧ (4619990760 : ℤ) ∣ B ∧ (4619990760 : ℤ) ∣ C ∧
       (q : ℝ) * Z ^ 2 ≤ A ∧ (A : ℝ) < 2 * q * Z ^ 2 ∧
       (q : ℝ) * Z ≤ B ∧ (B : ℝ) < 2 * q * Z ∧
       (q : ℝ) * Z ≤ C ∧ (C : ℝ) < 2 * q * Z ∧
       (∀ p : ℕ, p.Prime → p ∣ q →
         ¬ (p : ℤ) ∣ A * B * C * (462 * C + 15 * A) * (31 * A - 462 * B) * (15 * B + 31 * C)) ∧
       (∀ p : ℕ, p.Prime → ¬ p ∣ 4619990760 * q →
         ¬ (((p : ℤ) ∣ A ∧ (p : ℤ) ∣ 462 * B + q) ∨ ((p : ℤ) ∣ A ∧ (p : ℤ) ∣ 462 * C + q) ∨
           ((p : ℤ) ∣ 31 * A - 462 * B - q ∧ (p : ℤ) ∣ 15 * A + 462 * C + q)))))
    (q : ℕ) (A B C : ℤ) (Z : ℝ)
    (hq1 : 1 ≤ q) (hqW : q % 4619990760 = 1) (hZ : 100 ≤ Z) (hG : Good Z q A B C)
    (hsq : Squarefree q)
    (c : Fin 6 → ℤ) (L : Fin 6 → Fin 2 → ℤ)
    (hpar : ∀ n : Fin 2 → ℤ, OnPl q A B C (fun i => c i + ∑ j, L i j * n j))
    (hsurj : ∀ x, OnPl q A B C x → ∃ n : Fin 2 → ℤ, x = fun i => c i + ∑ j, L i j * n j) :
    ∀ p : ℕ, p.Prime → p ∣ q → ∀ i, ¬ ((p : ℤ) ∣ c i ∧ ∀ j, (p : ℤ) ∣ L i j) := by
  -- For p ∣ q (squarefree q, so p ∥ q): the lattice of plane points has index q²δ in the projected
  -- coordinates; lattice_reduction with the sublattice pΓ … shows the forms mod p are determined by the
  -- special fibre, where x4 ≡ -1 and the coordinate forms are non-constant in the free coordinates because
  -- p ∤ A B C (462C + 15A)(31A - 462B)(15B + 31C) from Good. Left open.
  intro p hp hpq i ⟨hci, hLi⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, hdiv, -⟩ := (hGood Z q A B C).mp hG
  have hprod := hdiv p hp hpq
  sorry

-- N39 fc_lattice [algebraic_identity]
theorem fc_lattice (OnPl : ℤ → ℤ → ℤ → ℤ → (Fin 6 → ℤ) → Prop)
    (hOnPl : ∀ q A B C (x : Fin 6 → ℤ), OnPl q A B C x ↔
      (q * (x 1 - x 4) = 31 * A * (x 2 - x 4) + 462 * B * x 4 ∧
       q * (x 3 - x 4) = -15 * A * (x 0 - x 4) + 462 * C * x 4 ∧
       q * (x 4 + 1) = -(15 * B * (x 0 - x 4) + 31 * C * (x 2 - x 4)) ∧
       508 * x 5 = 15 * (x 0 + x 1) + 31 * (x 2 + x 3) - 508 * x 4 - 462))
    (Good : ℝ → ℕ → ℤ → ℤ → ℤ → Prop)
    (hGood : ∀ Z q A B C, Good Z q A B C ↔
      ((4619990760 : ℤ) ∣ A ∧ (4619990760 : ℤ) ∣ B ∧ (4619990760 : ℤ) ∣ C ∧
       (q : ℝ) * Z ^ 2 ≤ A ∧ (A : ℝ) < 2 * q * Z ^ 2 ∧
       (q : ℝ) * Z ≤ B ∧ (B : ℝ) < 2 * q * Z ∧
       (q : ℝ) * Z ≤ C ∧ (C : ℝ) < 2 * q * Z ∧
       (∀ p : ℕ, p.Prime → p ∣ q →
         ¬ (p : ℤ) ∣ A * B * C * (462 * C + 15 * A) * (31 * A - 462 * B) * (15 * B + 31 * C)) ∧
       (∀ p : ℕ, p.Prime → ¬ p ∣ 4619990760 * q →
         ¬ (((p : ℤ) ∣ A ∧ (p : ℤ) ∣ 462 * B + q) ∨ ((p : ℤ) ∣ A ∧ (p : ℤ) ∣ 462 * C + q) ∨
           ((p : ℤ) ∣ 31 * A - 462 * B - q ∧ (p : ℤ) ∣ 15 * A + 462 * C + q)))))
    (q : ℕ) (A B C : ℤ) (Z : ℝ)
    (hq1 : 1 ≤ q) (hqW : q % 4619990760 = 1) (hZ : 100 ≤ Z) (hG : Good Z q A B C)
    (c : Fin 6 → ℤ) (L : Fin 6 → Fin 2 → ℤ)
    (hpar : ∀ n : Fin 2 → ℤ, OnPl q A B C (fun i => c i + ∑ j, L i j * n j))
    (hsurj : ∀ x, OnPl q A B C x → ∃ n : Fin 2 → ℤ, x = fun i => c i + ∑ j, L i j * n j)
    (hdet : ∃ δ : ℕ, δ ∣ 508 ∧
      |15 * (L 0 0 - L 4 0) * (31 * (L 2 1 - L 4 1)) - 15 * (L 0 1 - L 4 1) * (31 * (L 2 0 - L 4 0))|
        = 465 * (q : ℤ) ^ 2 * δ) :
    ∀ i j : Fin 6, i ≠ j → L i 0 * L j 1 - L i 1 * L j 0 ≠ 0 := by
  intro i j hij
  obtain ⟨δ, hδ, hdet'⟩ := hdet
  obtain ⟨-, -, -, hA1, hA2, hB1, hB2, hC1, hC2, -, -⟩ := (hGood Z q A B C).mp hG
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hqZ : (q : ℤ) ≠ 0 := by omega
  have hq0' : (0 : ℝ) < ((q : ℤ) : ℝ) := by exact_mod_cast hq1
  have hqq : ((q : ℤ) : ℝ) = (q : ℝ) := Int.cast_natCast q
  -- the real parameters
  have hα1 : Z ^ 2 ≤ (A : ℝ) / ((q : ℤ) : ℝ) := by rw [le_div_iff₀ hq0', hqq]; linarith
  have hα2 : (A : ℝ) / ((q : ℤ) : ℝ) ≤ 2 * Z ^ 2 := by rw [div_le_iff₀ hq0', hqq]; linarith
  have hβ1 : Z ≤ (B : ℝ) / ((q : ℤ) : ℝ) := by rw [le_div_iff₀ hq0', hqq]; linarith
  have hβ2 : (B : ℝ) / ((q : ℤ) : ℝ) ≤ 2 * Z := by rw [div_le_iff₀ hq0', hqq]; linarith
  have hγ1 : Z ≤ (C : ℝ) / ((q : ℤ) : ℝ) := by rw [le_div_iff₀ hq0', hqq]; linarith
  have hγ2 : (C : ℝ) / ((q : ℤ) : ℝ) ≤ 2 * Z := by rw [div_le_iff₀ hq0', hqq]; linarith
  generalize hαdef : (A : ℝ) / ((q : ℤ) : ℝ) = α at hα1 hα2
  generalize hβdef : (B : ℝ) / ((q : ℤ) : ℝ) = β at hβ1 hβ2
  generalize hγdef : (C : ℝ) / ((q : ℤ) : ℝ) = γ at hγ1 hγ2
  -- the linear parts in the (r, s)-coordinates
  set a : Fin 6 → ℝ := ![1 / 15 - β, -462 * β ^ 2 - β, -β, -α - 462 * β * γ - β, -β,
    (15 * ((1 / 15 - β) + (-462 * β ^ 2 - β)) + 31 * (-β + (-α - 462 * β * γ - β)) - 508 * (-β)) / 508]
    with ha
  set b : Fin 6 → ℝ := ![-γ, α - 462 * β * γ - γ, 1 / 31 - γ, -462 * γ ^ 2 - γ, -γ,
    (15 * (-γ + (α - 462 * β * γ - γ)) + 31 * ((1 / 31 - γ) + (-462 * γ ^ 2 - γ)) - 508 * (-γ)) / 508]
    with hb
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15⟩ :=
    finite_complexity_real Z α β γ (a 0) (b 0) (a 1) (b 1) (a 2) (b 2) (a 3) (b 3) (a 4) (b 4) (a 5) (b 5)
      hZ hα1 hα2 hβ1 hβ2 hγ1 hγ2 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have tsym : ∀ i j : Fin 6, a i * b j - b i * a j ≠ 0 → a j * b i - b j * a i ≠ 0 :=
    fun i j h e => h (by linear_combination -e)
  have hminor : ∀ i j : Fin 6, i ≠ j → a i * b j - b i * a j ≠ 0 := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd rfl hij
      | exact t1 | exact t2 | exact t3 | exact t4 | exact t5 | exact t6 | exact t7 | exact t8
      | exact t9 | exact t10 | exact t11 | exact t12 | exact t13 | exact t14 | exact t15
      | exact tsym _ _ t1 | exact tsym _ _ t2 | exact tsym _ _ t3 | exact tsym _ _ t4
      | exact tsym _ _ t5 | exact tsym _ _ t6 | exact tsym _ _ t7 | exact tsym _ _ t8
      | exact tsym _ _ t9 | exact tsym _ _ t10 | exact tsym _ _ t11 | exact tsym _ _ t12
      | exact tsym _ _ t13 | exact tsym _ _ t14 | exact tsym _ _ t15
  -- lifts of the three points n = 0, e₀, e₁
  have L0 := integral_lift OnPl hOnPl q A B C _ hqZ (hpar 0) α β γ _ _ hαdef.symm hβdef.symm hγdef.symm
    rfl rfl
  have L1 := integral_lift OnPl hOnPl q A B C _ hqZ (hpar ![1, 0]) α β γ _ _ hαdef.symm hβdef.symm
    hγdef.symm rfl rfl
  have L2 := integral_lift OnPl hOnPl q A B C _ hqZ (hpar ![0, 1]) α β γ _ _ hαdef.symm hβdef.symm
    hγdef.symm rfl rfl
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Pi.zero_apply, mul_zero, mul_one, add_zero, zero_add] at L0 L1 L2
  push_cast at L0 L1 L2
  obtain ⟨L00, L01, L02, L03, L04, L05⟩ := L0
  obtain ⟨L10, L11, L12, L13, L14, L15⟩ := L1
  obtain ⟨L20, L21, L22, L23, L24, L25⟩ := L2
  have hLv : ∀ i : Fin 6,
      (L i 0 : ℝ) = a i * (15 * ((L 0 0 : ℝ) - L 4 0)) + b i * (31 * ((L 2 0 : ℝ) - L 4 0)) ∧
      (L i 1 : ℝ) = a i * (15 * ((L 0 1 : ℝ) - L 4 1)) + b i * (31 * ((L 2 1 : ℝ) - L 4 1)) := by
    intro i
    fin_cases i
    · show (L 0 0 : ℝ) = (1 / 15 - β) * (15 * ((L 0 0 : ℝ) - L 4 0)) + (-γ) * (31 * ((L 2 0 : ℝ) - L 4 0)) ∧
        (L 0 1 : ℝ) = (1 / 15 - β) * (15 * ((L 0 1 : ℝ) - L 4 1)) + (-γ) * (31 * ((L 2 1 : ℝ) - L 4 1))
      exact ⟨by linear_combination L10 - L00, by linear_combination L20 - L00⟩
    · show (L 1 0 : ℝ) = (-462 * β ^ 2 - β) * (15 * ((L 0 0 : ℝ) - L 4 0)) +
          (α - 462 * β * γ - γ) * (31 * ((L 2 0 : ℝ) - L 4 0)) ∧
        (L 1 1 : ℝ) = (-462 * β ^ 2 - β) * (15 * ((L 0 1 : ℝ) - L 4 1)) +
          (α - 462 * β * γ - γ) * (31 * ((L 2 1 : ℝ) - L 4 1))
      exact ⟨by linear_combination L11 - L01, by linear_combination L21 - L01⟩
    · show (L 2 0 : ℝ) = (-β) * (15 * ((L 0 0 : ℝ) - L 4 0)) + (1 / 31 - γ) * (31 * ((L 2 0 : ℝ) - L 4 0)) ∧
        (L 2 1 : ℝ) = (-β) * (15 * ((L 0 1 : ℝ) - L 4 1)) + (1 / 31 - γ) * (31 * ((L 2 1 : ℝ) - L 4 1))
      exact ⟨by linear_combination L12 - L02, by linear_combination L22 - L02⟩
    · show (L 3 0 : ℝ) = (-α - 462 * β * γ - β) * (15 * ((L 0 0 : ℝ) - L 4 0)) +
          (-462 * γ ^ 2 - γ) * (31 * ((L 2 0 : ℝ) - L 4 0)) ∧
        (L 3 1 : ℝ) = (-α - 462 * β * γ - β) * (15 * ((L 0 1 : ℝ) - L 4 1)) +
          (-462 * γ ^ 2 - γ) * (31 * ((L 2 1 : ℝ) - L 4 1))
      exact ⟨by linear_combination L13 - L03, by linear_combination L23 - L03⟩
    · show (L 4 0 : ℝ) = (-β) * (15 * ((L 0 0 : ℝ) - L 4 0)) + (-γ) * (31 * ((L 2 0 : ℝ) - L 4 0)) ∧
        (L 4 1 : ℝ) = (-β) * (15 * ((L 0 1 : ℝ) - L 4 1)) + (-γ) * (31 * ((L 2 1 : ℝ) - L 4 1))
      exact ⟨by linear_combination L14 - L04, by linear_combination L24 - L04⟩
    · show (L 5 0 : ℝ) = (15 * ((1 / 15 - β) + (-462 * β ^ 2 - β)) + 31 * (-β + (-α - 462 * β * γ - β)) -
            508 * (-β)) / 508 * (15 * ((L 0 0 : ℝ) - L 4 0)) +
          (15 * (-γ + (α - 462 * β * γ - γ)) + 31 * ((1 / 31 - γ) + (-462 * γ ^ 2 - γ)) - 508 * (-γ)) / 508 *
            (31 * ((L 2 0 : ℝ) - L 4 0)) ∧
        (L 5 1 : ℝ) = (15 * ((1 / 15 - β) + (-462 * β ^ 2 - β)) + 31 * (-β + (-α - 462 * β * γ - β)) -
            508 * (-β)) / 508 * (15 * ((L 0 1 : ℝ) - L 4 1)) +
          (15 * (-γ + (α - 462 * β * γ - γ)) + 31 * ((1 / 31 - γ) + (-462 * γ ^ 2 - γ)) - 508 * (-γ)) / 508 *
            (31 * ((L 2 1 : ℝ) - L 4 1))
      constructor
      · linear_combination (L15 - L05) + (15 / 508) * ((L10 - L00) + (L11 - L01)) +
          (31 / 508) * ((L12 - L02) + (L13 - L03)) - (L14 - L04)
      · linear_combination (L25 - L05) + (15 / 508) * ((L20 - L00) + (L21 - L01)) +
          (31 / 508) * ((L22 - L02) + (L23 - L03)) - (L24 - L04)
  -- the determinant of the change of variables is nonzero
  have hD : (15 * ((L 0 0 : ℝ) - L 4 0)) * (31 * ((L 2 1 : ℝ) - L 4 1)) -
      (15 * ((L 0 1 : ℝ) - L 4 1)) * (31 * ((L 2 0 : ℝ) - L 4 0)) ≠ 0 := by
    intro h
    have h' : (15 * (L 0 0 - L 4 0) * (31 * (L 2 1 - L 4 1)) - 15 * (L 0 1 - L 4 1) * (31 * (L 2 0 - L 4 0)) : ℤ)
        = 0 := by exact_mod_cast h
    rw [h', abs_zero] at hdet'
    have hδ0 : δ ≠ 0 := fun h0 => by subst h0; norm_num at hδ
    have : (465 : ℤ) * (q : ℤ) ^ 2 * δ ≠ 0 := by positivity
    exact this hdet'.symm
  have hreal : ((L i 0 * L j 1 - L i 1 * L j 0 : ℤ) : ℝ) = (a i * b j - b i * a j) *
      ((15 * ((L 0 0 : ℝ) - L 4 0)) * (31 * ((L 2 1 : ℝ) - L 4 1)) -
        (15 * ((L 0 1 : ℝ) - L 4 1)) * (31 * ((L 2 0 : ℝ) - L 4 0))) := by
    push_cast
    rw [(hLv i).1, (hLv i).2, (hLv j).1, (hLv j).2]
    ring
  intro h
  have : ((L i 0 * L j 1 - L i 1 * L j 0 : ℤ) : ℝ) = 0 := by rw [h]; simp
  rw [hreal] at this
  exact mul_ne_zero (hminor i j hij) hD this

-- N40 beta_local [assembly]
theorem beta_local (OnPl : ℤ → ℤ → ℤ → ℤ → (Fin 6 → ℤ) → Prop)
    (hOnPl : ∀ q A B C (x : Fin 6 → ℤ), OnPl q A B C x ↔
      (q * (x 1 - x 4) = 31 * A * (x 2 - x 4) + 462 * B * x 4 ∧
       q * (x 3 - x 4) = -15 * A * (x 0 - x 4) + 462 * C * x 4 ∧
       q * (x 4 + 1) = -(15 * B * (x 0 - x 4) + 31 * C * (x 2 - x 4)) ∧
       508 * x 5 = 15 * (x 0 + x 1) + 31 * (x 2 + x 3) - 508 * x 4 - 462))
    (Good : ℝ → ℕ → ℤ → ℤ → ℤ → Prop)
    (hGood : ∀ Z q A B C, Good Z q A B C ↔
      ((4619990760 : ℤ) ∣ A ∧ (4619990760 : ℤ) ∣ B ∧ (4619990760 : ℤ) ∣ C ∧
       (q : ℝ) * Z ^ 2 ≤ A ∧ (A : ℝ) < 2 * q * Z ^ 2 ∧
       (q : ℝ) * Z ≤ B ∧ (B : ℝ) < 2 * q * Z ∧
       (q : ℝ) * Z ≤ C ∧ (C : ℝ) < 2 * q * Z ∧
       (∀ p : ℕ, p.Prime → p ∣ q →
         ¬ (p : ℤ) ∣ A * B * C * (462 * C + 15 * A) * (31 * A - 462 * B) * (15 * B + 31 * C)) ∧
       (∀ p : ℕ, p.Prime → ¬ p ∣ 4619990760 * q →
         ¬ (((p : ℤ) ∣ A ∧ (p : ℤ) ∣ 462 * B + q) ∨ ((p : ℤ) ∣ A ∧ (p : ℤ) ∣ 462 * C + q) ∨
           ((p : ℤ) ∣ 31 * A - 462 * B - q ∧ (p : ℤ) ∣ 15 * A + 462 * C + q)))))
    (q : ℕ) (A B C : ℤ) (Z : ℝ)
    (hq1 : 1 ≤ q) (hqW : q % 4619990760 = 1) (hZ : 100 ≤ Z) (hG : Good Z q A B C)
    (hsq : Squarefree q)
    (c : Fin 6 → ℤ) (L : Fin 6 → Fin 2 → ℤ)
    (hpar : ∀ n : Fin 2 → ℤ, OnPl q A B C (fun i => c i + ∑ j, L i j * n j))
    (hsurj : ∀ x, OnPl q A B C x → ∃ n : Fin 2 → ℤ, x = fun i => c i + ∑ j, L i j * n j)
    (hdet : ∃ δ : ℕ, δ ∣ 508 ∧
      |15 * (L 0 0 - L 4 0) * (31 * (L 2 1 - L 4 1)) - 15 * (L 0 1 - L 4 1) * (31 * (L 2 0 - L 4 0))|
        = 465 * (q : ℤ) ^ 2 * δ)
    (β : ℕ → ℝ)
    (hβ : ∀ p : ℕ, β p = ((p : ℝ) / (p - 1)) ^ 6 / (p : ℝ) ^ 2 *
      ((Fintype.piFinset fun _ : Fin 2 => Finset.range p).filter
        (fun n => ∀ i, ¬ (p : ℤ) ∣ c i + ∑ j, L i j * (n j : ℤ))).card) :
    ∀ p : ℕ, p.Prime →
      (p ∣ 4619990760 → 1 / (p : ℝ) ^ 2 * ((p : ℝ) / (p - 1)) ^ 6 ≤ β p) ∧
      (¬ p ∣ 4619990760 → (1 - 6 / (p : ℝ)) * ((p : ℝ) / (p - 1)) ^ 6 ≤ β p) := by
  intro p hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hfac : 0 < ((p : ℝ) / (p - 1)) ^ 6 := pow_pos (div_pos hp0 (by linarith)) 6
  have hcoef : 0 ≤ ((p : ℝ) / (p - 1)) ^ 6 / (p : ℝ) ^ 2 := by positivity
  rw [hβ p]
  set N := ((Fintype.piFinset fun _ : Fin 2 => Finset.range p).filter
    (fun n => ∀ i, ¬ (p : ℤ) ∣ c i + ∑ j, L i j * (n j : ℤ))).card with hN
  have hN0 : (0 : ℝ) ≤ N := by positivity
  obtain ⟨hWA, hWB, hWC, -⟩ := (hGood Z q A B C).mp hG
  obtain ⟨-, -, hCq, -⟩ := good_coprime Good hGood Z q A B C hG
  constructor
  · intro hpW
    obtain ⟨n, hn, hunit⟩ := local_W OnPl hOnPl q A B C hq1 hqW hWA hWB hWC hCq c L hpar hsurj p hp hpW
    have hmem : n ∈ (Fintype.piFinset fun _ : Fin 2 => Finset.range p).filter
        (fun n => ∀ i, ¬ (p : ℤ) ∣ c i + ∑ j, L i j * (n j : ℤ)) :=
      Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun j => Finset.mem_range.mpr (hn j)), hunit⟩
    have hN1 : 1 ≤ N := Finset.card_pos.mpr ⟨n, hmem⟩
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    calc 1 / (p : ℝ) ^ 2 * ((p : ℝ) / (p - 1)) ^ 6 = ((p : ℝ) / (p - 1)) ^ 6 / (p : ℝ) ^ 2 * 1 := by ring
      _ ≤ ((p : ℝ) / (p - 1)) ^ 6 / (p : ℝ) ^ 2 * N := by gcongr
  · intro hpW
    have hnz : ∀ i, ¬ ((p : ℤ) ∣ c i ∧ ∀ j, (p : ℤ) ∣ L i j) := by
      by_cases hpq : p ∣ q
      · exact local_denominator OnPl hOnPl Good hGood q A B C Z hq1 hqW hZ hG hsq c L hpar hsurj p hp hpq
      · have hpWq : ¬ p ∣ 4619990760 * q := fun h => by
          rcases (Nat.Prime.dvd_mul hp).mp h with h | h
          · exact hpW h
          · exact hpq h
        exact local_away OnPl hOnPl Good hGood q A B C Z hq1 hqW hZ hG c L hpar hsurj hdet p hp hpWq
    have hcount := nonzero_forms_count p hp c L hnz
    have hcount' : (p : ℝ) ^ 2 - 6 * p ≤ N := by
      by_cases h6 : 6 * p ≤ p ^ 2
      · have : ((p ^ 2 - 6 * p : ℕ) : ℝ) ≤ N := by exact_mod_cast hcount
        rw [Nat.cast_sub h6] at this
        push_cast at this
        linarith
      · push Not at h6
        have : (p : ℝ) ^ 2 < 6 * p := by exact_mod_cast h6
        linarith
    calc (1 - 6 / (p : ℝ)) * ((p : ℝ) / (p - 1)) ^ 6
        = ((p : ℝ) / (p - 1)) ^ 6 / (p : ℝ) ^ 2 * ((p : ℝ) ^ 2 - 6 * p) := by
          field_simp
      _ ≤ ((p : ℝ) / (p - 1)) ^ 6 / (p : ℝ) ^ 2 * N := by gcongr

-- N41 ap_product [extremal_averaging]
theorem ap_product :
    Multipliable (fun p : Nat.Primes => (if ((p : ℕ) ∣ 4619990760) then 1 / ((p : ℕ) : ℝ) ^ 2 * (((p : ℕ) : ℝ) / (((p : ℕ) : ℝ) - 1)) ^ 6 else (1 - 6 / ((p : ℕ) : ℝ)) * (((p : ℕ) : ℝ) / (((p : ℕ) : ℝ) - 1)) ^ 6)) ∧
    0 < ∏' p : Nat.Primes, (if ((p : ℕ) ∣ 4619990760) then 1 / ((p : ℕ) : ℝ) ^ 2 * (((p : ℕ) : ℝ) / (((p : ℕ) : ℝ) - 1)) ^ 6 else (1 - 6 / ((p : ℕ) : ℝ)) * (((p : ℕ) : ℝ) / (((p : ℕ) : ℝ) - 1)) ^ 6) := by
  set f : Nat.Primes → ℝ := fun p => if ((p : ℕ) ∣ 4619990760) then
      1 / ((p : ℕ) : ℝ) ^ 2 * (((p : ℕ) : ℝ) / (((p : ℕ) : ℝ) - 1)) ^ 6
    else (1 - 6 / ((p : ℕ) : ℝ)) * (((p : ℕ) : ℝ) / (((p : ℕ) : ℝ) - 1)) ^ 6 with hf
  -- p ∤ W forces p ≥ 13
  have hge13 : ∀ p : Nat.Primes, ¬ ((p : ℕ) ∣ 4619990760) → 13 ≤ (p : ℕ) := by
    intro p h
    have hp := p.2
    have h2 := hp.two_le
    have hn2 : (p : ℕ) ≠ 2 := fun e => h (e ▸ by norm_num)
    have hn3 : (p : ℕ) ≠ 3 := fun e => h (e ▸ by norm_num)
    have hn5 : (p : ℕ) ≠ 5 := fun e => h (e ▸ by norm_num)
    have hn7 : (p : ℕ) ≠ 7 := fun e => h (e ▸ by norm_num)
    have hn11 : (p : ℕ) ≠ 11 := fun e => h (e ▸ by norm_num)
    have hn4 : (p : ℕ) ≠ 4 := fun e => by
      have := hp.eq_one_or_self_of_dvd 2 (by rw [e]; norm_num); omega
    have hn6 : (p : ℕ) ≠ 6 := fun e => by
      have := hp.eq_one_or_self_of_dvd 2 (by rw [e]; norm_num); omega
    have hn8 : (p : ℕ) ≠ 8 := fun e => by
      have := hp.eq_one_or_self_of_dvd 2 (by rw [e]; norm_num); omega
    have hn9 : (p : ℕ) ≠ 9 := fun e => by
      have := hp.eq_one_or_self_of_dvd 3 (by rw [e]; norm_num); omega
    have hn10 : (p : ℕ) ≠ 10 := fun e => by
      have := hp.eq_one_or_self_of_dvd 2 (by rw [e]; norm_num); omega
    have hn12 : (p : ℕ) ≠ 12 := fun e => by
      have := hp.eq_one_or_self_of_dvd 2 (by rw [e]; norm_num); omega
    omega
  -- p ∣ W forces p ≤ 127
  have hle127 : ∀ p : Nat.Primes, (p : ℕ) ∣ 4619990760 → (p : ℕ) ≤ 127 := by
    intro p h
    have hp := p.2
    rw [show (4619990760 : ℕ) = 2 ^ 3 * 3 * 5 * 7 * 11 * 31 * 127 ^ 2 by norm_num] at h
    have le_of : ∀ (a n : ℕ), 0 < a → (p : ℕ) ∣ a ^ n → (p : ℕ) ≤ a := fun a n ha hd =>
      Nat.le_of_dvd ha (hp.dvd_of_dvd_pow hd)
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
        · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
          · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
            · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
              · have := le_of 2 3 (by norm_num) h; omega
              · have := Nat.le_of_dvd (by norm_num) h; omega
            · have := Nat.le_of_dvd (by norm_num) h; omega
          · have := Nat.le_of_dvd (by norm_num) h; omega
        · have := Nat.le_of_dvd (by norm_num) h; omega
      · have := Nat.le_of_dvd (by norm_num) h; omega
    · exact le_of 127 2 (by norm_num) h
  have hpos : ∀ p : Nat.Primes, 0 < f p := by
    intro p
    have hp2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.two_le
    have hq : 0 < (((p : ℕ) : ℝ) / (((p : ℕ) : ℝ) - 1)) ^ 6 :=
      pow_pos (div_pos (by linarith) (by linarith)) 6
    simp only [hf]
    split_ifs with h
    · positivity
    · apply mul_pos _ hq
      have h13 : (13 : ℝ) ≤ (p : ℕ) := by exact_mod_cast hge13 p h
      have : 6 / ((p : ℕ) : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
      linarith
  -- the key bound |log f p| ≤ K p^{-2}
  have hbound : ∀ p : Nat.Primes, ‖Real.log (f p)‖ ≤ 2 * 10 ^ 7 * ((p : ℕ) : ℝ) ^ (-2 : ℝ) := by
    intro p
    have hp := p.2
    have hp2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast hp.two_le
    rw [Real.norm_eq_abs, Real.rpow_neg (by linarith), Real.rpow_two]
    set x : ℝ := ((p : ℕ) : ℝ) with hx
    have hp0 : 0 < x := by linarith
    have hp1 : 0 < x - 1 := by linarith
    have hq0 : 0 < x / (x - 1) := div_pos hp0 hp1
    have hlq_le : Real.log (x / (x - 1)) ≤ (x - 1)⁻¹ := by
      have := Real.log_le_sub_one_of_pos hq0
      have e : x / (x - 1) - 1 = (x - 1)⁻¹ := by field_simp; ring
      linarith
    have hlq_ge : x⁻¹ ≤ Real.log (x / (x - 1)) := by
      have := Real.one_sub_inv_le_log_of_pos hq0
      have e : 1 - (x / (x - 1))⁻¹ = x⁻¹ := by field_simp; ring
      linarith
    have hx2 : 0 < x ^ 2 := by positivity
    simp only [hf]
    split_ifs with hW
    · have hp127 : x ≤ 127 := by
        have := hle127 p hW
        simp only [hx]
        exact_mod_cast this
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, one_div, Real.log_inv,
        Real.log_pow]
      push_cast
      have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
      have hlogx : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hp0
      have hlq0 : 0 ≤ Real.log (x / (x - 1)) := by
        have : 0 < x⁻¹ := by positivity
        linarith
      have h1x : (x - 1)⁻¹ ≤ 1 := by rw [inv_le_one₀ hp1]; linarith
      have hK : 8 * x ≤ 2 * 10 ^ 7 * (x ^ 2)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hx2]
        have h3 : x ^ 3 ≤ 127 ^ 3 := pow_le_pow_left₀ hp0.le hp127 3
        have : 8 * x * x ^ 2 = 8 * x ^ 3 := by ring
        rw [this]
        norm_num at h3 ⊢
        linarith
      rw [abs_le]
      constructor <;> linarith
    · have h13 : (13 : ℝ) ≤ x := by
        have := hge13 p hW
        simp only [hx]
        exact_mod_cast this
      have hx6 : 0 < x - 6 := by linarith
      have h16 : 0 < 1 - 6 / x := by
        have : 6 / x < 1 := by rw [div_lt_one hp0]; linarith
        linarith
      rw [Real.log_mul h16.ne' (by positivity), Real.log_pow]
      push_cast
      have hl1 : Real.log (1 - 6 / x) ≤ -(6 * x⁻¹) := by
        have := Real.log_le_sub_one_of_pos h16
        have e : 1 - 6 / x - 1 = -(6 * x⁻¹) := by ring
        linarith
      have hl2 : -(6 * (x - 6)⁻¹) ≤ Real.log (1 - 6 / x) := by
        have := Real.one_sub_inv_le_log_of_pos h16
        have e : 1 - (1 - 6 / x)⁻¹ = -(6 * (x - 6)⁻¹) := by field_simp; ring
        linarith
      have e1 : 6 * (x - 1)⁻¹ - 6 * x⁻¹ = 6 / ((x - 1) * x) := by field_simp; ring
      have e2 : 6 * (x - 6)⁻¹ - 6 * x⁻¹ = 36 / ((x - 6) * x) := by field_simp; ring
      have b1 : 6 / ((x - 1) * x) ≤ 2 * 10 ^ 7 * (x ^ 2)⁻¹ := by
        rw [← div_eq_mul_inv, div_le_div_iff₀ (mul_pos hp1 hp0) hx2]
        nlinarith
      have b2 : 36 / ((x - 6) * x) ≤ 2 * 10 ^ 7 * (x ^ 2)⁻¹ := by
        rw [← div_eq_mul_inv, div_le_div_iff₀ (mul_pos hx6 hp0) hx2]
        nlinarith
      rw [abs_le]
      constructor <;> linarith
  have hsum : Summable (fun p : Nat.Primes => Real.log (f p)) := by
    apply Summable.of_norm_bounded _ hbound
    exact (Nat.Primes.summable_rpow.mpr (by norm_num)).mul_left _
  have hmult : Multipliable f := Real.multipliable_of_summable_log hpos hsum
  refine ⟨hmult, ?_⟩
  rw [← Real.rexp_tsum_eq_tprod hpos hsum]
  exact Real.exp_pos _

-- N42 singular_series_lower [assembly]
theorem singular_series_lower (OnPl : ℤ → ℤ → ℤ → ℤ → (Fin 6 → ℤ) → Prop)
    (hOnPl : ∀ q A B C (x : Fin 6 → ℤ), OnPl q A B C x ↔
      (q * (x 1 - x 4) = 31 * A * (x 2 - x 4) + 462 * B * x 4 ∧
       q * (x 3 - x 4) = -15 * A * (x 0 - x 4) + 462 * C * x 4 ∧
       q * (x 4 + 1) = -(15 * B * (x 0 - x 4) + 31 * C * (x 2 - x 4)) ∧
       508 * x 5 = 15 * (x 0 + x 1) + 31 * (x 2 + x 3) - 508 * x 4 - 462))
    (Good : ℝ → ℕ → ℤ → ℤ → ℤ → Prop)
    (hGood : ∀ Z q A B C, Good Z q A B C ↔
      ((4619990760 : ℤ) ∣ A ∧ (4619990760 : ℤ) ∣ B ∧ (4619990760 : ℤ) ∣ C ∧
       (q : ℝ) * Z ^ 2 ≤ A ∧ (A : ℝ) < 2 * q * Z ^ 2 ∧
       (q : ℝ) * Z ≤ B ∧ (B : ℝ) < 2 * q * Z ∧
       (q : ℝ) * Z ≤ C ∧ (C : ℝ) < 2 * q * Z ∧
       (∀ p : ℕ, p.Prime → p ∣ q →
         ¬ (p : ℤ) ∣ A * B * C * (462 * C + 15 * A) * (31 * A - 462 * B) * (15 * B + 31 * C)) ∧
       (∀ p : ℕ, p.Prime → ¬ p ∣ 4619990760 * q →
         ¬ (((p : ℤ) ∣ A ∧ (p : ℤ) ∣ 462 * B + q) ∨ ((p : ℤ) ∣ A ∧ (p : ℤ) ∣ 462 * C + q) ∨
           ((p : ℤ) ∣ 31 * A - 462 * B - q ∧ (p : ℤ) ∣ 15 * A + 462 * C + q))))) :
    ∃ cstar : ℝ, 0 < cstar ∧ ∀ (q : ℕ) (A B C : ℤ) (Z : ℝ), 1 ≤ q → q % 4619990760 = 1 → 100 ≤ Z →
      Good Z q A B C → Squarefree q →
      ∀ (c : Fin 6 → ℤ) (L : Fin 6 → Fin 2 → ℤ) (β : ℕ → ℝ),
        (∀ n : Fin 2 → ℤ, OnPl q A B C (fun i => c i + ∑ j, L i j * n j)) →
        (∀ x, OnPl q A B C x → ∃ n : Fin 2 → ℤ, x = fun i => c i + ∑ j, L i j * n j) →
        (∃ δ : ℕ, δ ∣ 508 ∧ |15 * (L 0 0 - L 4 0) * (31 * (L 2 1 - L 4 1)) - 15 * (L 0 1 - L 4 1) * (31 * (L 2 0 - L 4 0))| = 465 * (q : ℤ) ^ 2 * δ) →
        (∀ p : ℕ, β p = ((p : ℝ) / (p - 1)) ^ 6 / (p : ℝ) ^ 2 *
          ((Fintype.piFinset fun _ : Fin 2 => Finset.range p).filter
            (fun n => ∀ i, ¬ (p : ℤ) ∣ c i + ∑ j, L i j * (n j : ℤ))).card) →
        (∀ p : ℕ, p.Prime → 0 < β p) ∧ Multipliable (fun p : Nat.Primes => β p) ∧
          cstar ≤ ∏' p : Nat.Primes, β p := by
  -- Assembly: β_p > 0 from beta_local; pairwise linear independence of the rows of L from fc_lattice
  -- (LinearIndependent.pair_iff with the nonzero 2×2 minor); then bienvenu_lemma12_singular_series gives
  -- Multipliable and positivity; finally ∏ β_p ≥ ∏ (comparison factor) = c* needs a termwise comparison of
  -- infinite products of positive multipliable families (not located in Mathlib; left open).
  obtain ⟨hmult₀, hpos₀⟩ := ap_product
  refine ⟨∏' p : Nat.Primes, (if ((p : ℕ) ∣ 4619990760) then 1 / ((p : ℕ) : ℝ) ^ 2 * (((p : ℕ) : ℝ) / (((p : ℕ) : ℝ) - 1)) ^ 6
    else (1 - 6 / ((p : ℕ) : ℝ)) * (((p : ℕ) : ℝ) / (((p : ℕ) : ℝ) - 1)) ^ 6), hpos₀, ?_⟩
  intro q A B C Z hq1 hqW hZ hG hsq c L β hpar hsurj hdet hβ
  have hloc := beta_local OnPl hOnPl Good hGood q A B C Z hq1 hqW hZ hG hsq c L hpar hsurj hdet β hβ
  have hβpos : ∀ p : ℕ, p.Prime → 0 < β p := by
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hq : 0 < ((p : ℝ) / ((p : ℝ) - 1)) ^ 6 := pow_pos (div_pos (by linarith) (by linarith)) 6
    obtain ⟨h1, h2⟩ := hloc p hp
    by_cases hpW : p ∣ 4619990760
    · have := h1 hpW
      have : 0 < 1 / (p : ℝ) ^ 2 * ((p : ℝ) / (p - 1)) ^ 6 := by positivity
      linarith
    · have := h2 hpW
      have h7 : (7 : ℝ) ≤ p := by
        have h2 := hp.two_le
        have hn2 : p ≠ 2 := fun h => hpW (h ▸ by norm_num)
        have hn3 : p ≠ 3 := fun h => hpW (h ▸ by norm_num)
        have hn5 : p ≠ 5 := fun h => hpW (h ▸ by norm_num)
        have hn4 : p ≠ 4 := fun h => by have := hp.eq_one_or_self_of_dvd 2 (by rw [h]; norm_num); omega
        have hn6 : p ≠ 6 := fun h => by have := hp.eq_one_or_self_of_dvd 2 (by rw [h]; norm_num); omega
        have : 7 ≤ p := by omega
        exact_mod_cast this
      have : 0 < (1 - 6 / (p : ℝ)) * ((p : ℝ) / (p - 1)) ^ 6 := by
        apply mul_pos _ hq
        have : 6 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
        linarith
      linarith
  refine ⟨hβpos, ?_, ?_⟩
  · sorry
  · sorry

-- N43 collision_line [case_split]
theorem collision_line (a b e : ℤ) (M : ℕ) (hab : a ≠ 0 ∨ b ≠ 0) :
    ((Finset.Icc (-(M : ℤ)) M ×ˢ Finset.Icc (-(M : ℤ)) M).filter
      (fun n => a * n.1 + b * n.2 = e)).card ≤ 2 * M + 1 := by
  rcases hab with ha | hb
  · -- n.1 is determined by n.2
    calc _ ≤ (Finset.Icc (-(M : ℤ)) M).card := by
          apply Finset.card_le_card_of_injOn (fun n => n.2)
          · intro n hn
            simp only [Finset.coe_filter, Finset.mem_product, Set.mem_ofPred_eq] at hn
            simpa using hn.1.2
          · intro n hn m hm hnm
            simp only [Finset.coe_filter, Finset.mem_product, Set.mem_ofPred_eq] at hn hm
            have h1 : a * n.1 = a * m.1 := by
              simp only at hnm
              linear_combination hn.2 - hm.2 - b * hnm
            exact Prod.ext (mul_left_cancel₀ ha h1) hnm
      _ = 2 * M + 1 := by rw [Int.card_Icc]; omega
  · calc _ ≤ (Finset.Icc (-(M : ℤ)) M).card := by
          apply Finset.card_le_card_of_injOn (fun n => n.1)
          · intro n hn
            simp only [Finset.coe_filter, Finset.mem_product, Set.mem_ofPred_eq] at hn
            simpa using hn.1.1
          · intro n hn m hm hnm
            simp only [Finset.coe_filter, Finset.mem_product, Set.mem_ofPred_eq] at hn hm
            have h1 : b * n.2 = b * m.2 := by
              simp only at hnm
              linear_combination hn.2 - hm.2 - a * hnm
            exact Prod.ext hnm (mul_left_cancel₀ hb h1)
      _ = 2 * M + 1 := by rw [Int.card_Icc]; omega

-- N44 prime_weight_to_count [extremal_averaging]
theorem prime_weight_to_count {d t : ℕ} (F : Finset (Fin d → ℤ)) (f : (Fin d → ℤ) → Fin t → ℤ) (V : ℝ)
    (hV : 1 ≤ V) (hf : ∀ n ∈ F, ∀ i, (f n i : ℝ) ≤ V) :
    ∑ n ∈ F, ∏ i, (if 0 < f n i ∧ (f n i).natAbs.Prime then Real.log (f n i : ℝ) else 0) ≤
      Real.log V ^ t * ((F.filter (fun n => ∀ i, 0 < f n i ∧ (f n i).natAbs.Prime)).card : ℝ) := by
  classical
  set P : (Fin d → ℤ) → Prop := fun n => ∀ i, 0 < f n i ∧ (f n i).natAbs.Prime with hP
  rw [← Finset.sum_filter_add_sum_filter_not F P]
  have hzero : ∑ n ∈ F.filter (fun n => ¬ P n),
      ∏ i, (if 0 < f n i ∧ (f n i).natAbs.Prime then Real.log (f n i : ℝ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [Finset.mem_filter] at hn
    have : ∃ i, ¬ (0 < f n i ∧ (f n i).natAbs.Prime) := by
      by_contra hcon
      push Not at hcon
      exact hn.2 hcon
    obtain ⟨i, hi⟩ := this
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [ite_eq_right_iff]; intro h; exact absurd h hi)
  rw [hzero, add_zero]
  have hV0 : 0 ≤ Real.log V := Real.log_nonneg hV
  calc ∑ n ∈ F.filter P, ∏ i, (if 0 < f n i ∧ (f n i).natAbs.Prime then Real.log (f n i : ℝ) else 0)
      ≤ ∑ n ∈ F.filter P, Real.log V ^ t := by
        apply Finset.sum_le_sum
        intro n hn
        rw [Finset.mem_filter] at hn
        calc ∏ i, (if 0 < f n i ∧ (f n i).natAbs.Prime then Real.log (f n i : ℝ) else 0)
            ≤ ∏ _i : Fin t, Real.log V := by
              apply Finset.prod_le_prod₀
              · intro i _
                split_ifs with h
                · apply Real.log_nonneg
                  have : (1 : ℤ) ≤ f n i := h.1
                  exact_mod_cast this
                · exact le_rfl
              · intro i _
                split_ifs with h
                · apply Real.log_le_log
                  · have : (0 : ℤ) < f n i := h.1
                    exact_mod_cast this
                  · exact hf n hn.1 i
                · exact hV0
          _ = Real.log V ^ t := by simp
    _ = Real.log V ^ t * ((F.filter P).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

-- N45 plane_prime_count [two_structure_coupling]
theorem plane_prime_count (OnPl : ℤ → ℤ → ℤ → ℤ → (Fin 6 → ℤ) → Prop)
    (hOnPl : ∀ q A B C (x : Fin 6 → ℤ), OnPl q A B C x ↔
      (q * (x 1 - x 4) = 31 * A * (x 2 - x 4) + 462 * B * x 4 ∧
       q * (x 3 - x 4) = -15 * A * (x 0 - x 4) + 462 * C * x 4 ∧
       q * (x 4 + 1) = -(15 * B * (x 0 - x 4) + 31 * C * (x 2 - x 4)) ∧
       508 * x 5 = 15 * (x 0 + x 1) + 31 * (x 2 + x 3) - 508 * x 4 - 462))
    (InReg : ℝ → (Fin 6 → ℤ) → Prop)
    (hInReg : ∀ T (x : Fin 6 → ℤ), InReg T x ↔
      (-2 * T ≤ 15 * ((x 0 : ℝ) - x 4) ∧ 15 * ((x 0 : ℝ) - x 4) ≤ -T ∧
       |31 * ((x 2 : ℝ) - x 4)| ≤ 1 / 100000 * |15 * ((x 0 : ℝ) - x 4)|))
    (Good : ℝ → ℕ → ℤ → ℤ → ℤ → Prop)
    (hGood : ∀ Z q A B C, Good Z q A B C ↔
      ((4619990760 : ℤ) ∣ A ∧ (4619990760 : ℤ) ∣ B ∧ (4619990760 : ℤ) ∣ C ∧
       (q : ℝ) * Z ^ 2 ≤ A ∧ (A : ℝ) < 2 * q * Z ^ 2 ∧
       (q : ℝ) * Z ≤ B ∧ (B : ℝ) < 2 * q * Z ∧
       (q : ℝ) * Z ≤ C ∧ (C : ℝ) < 2 * q * Z ∧
       (∀ p : ℕ, p.Prime → p ∣ q →
         ¬ (p : ℤ) ∣ A * B * C * (462 * C + 15 * A) * (31 * A - 462 * B) * (15 * B + 31 * C)) ∧
       (∀ p : ℕ, p.Prime → ¬ p ∣ 4619990760 * q →
         ¬ (((p : ℤ) ∣ A ∧ (p : ℤ) ∣ 462 * B + q) ∨ ((p : ℤ) ∣ A ∧ (p : ℤ) ∣ 462 * C + q) ∨
           ((p : ℤ) ∣ 31 * A - 462 * B - q ∧ (p : ℤ) ∣ 15 * A + 462 * C + q))))) :
    ∀ τ : ℝ, 0 < τ → ∃ T0 c3 : ℝ, 0 < c3 ∧ ∀ (T Z : ℝ) (q : ℕ) (A B C : ℤ),
      T0 ≤ T → 100 ≤ Z → 1 ≤ q → Squarefree q → q % 4619990760 = 1 →
      (q : ℝ) ≤ Real.log T ^ τ → Z ≤ Real.log T ^ τ → Good Z q A B C →
      ∃ F : Finset (Fin 6 → ℤ),
        (∀ x ∈ F, OnPl q A B C x ∧ InReg T x ∧ Function.Injective x ∧ ∀ i, 0 < x i ∧ (x i).natAbs.Prime) ∧
        c3 * T ^ 2 / ((q : ℝ) ^ 2 * Real.log T ^ 6) ≤ F.card := by
  -- Assembly of Bienvenu's theorem on the lattice parametrisation: K from lattice_coords has volume
  -- ≍ T²/(q²δ), all forms are ≥ N^{9/10} on K by region_bounds_int, the singular series is ≥ c* by
  -- singular_series_lower, so the Λ'-weighted count is ≥ (1-ε) vol(K) c*; prime_weight_to_count converts to a
  -- point count ≥ vol(K) c*/(2 (log V)^6), and collision_line removes the O(T) points with two equal coordinates.
  -- The N = (log T)^{O(1)}-uniformity bookkeeping is left open.
  intro τ hτ
  obtain ⟨cstar, hcstar, hss⟩ := singular_series_lower OnPl hOnPl Good hGood
  obtain ⟨C0, C1, C2, hC1, hlat⟩ := lattice_coords OnPl hOnPl
  obtain ⟨N0, hbien⟩ := bienvenu_prop21_uniform 2 6 10 10 10 (cstar * 3 / 100000 / (465 * 508)) (1 / 2)
    (by positivity) (by norm_num)
  refine ⟨max N0 (max 10 (Real.exp (100 / τ))), cstar / 4, by positivity, ?_⟩
  intro T Z q A B C hT hZ hq hsq hqW hqT hZT hG
  sorry

-- N46 threshold_lemma [assembly]
theorem threshold_lemma (κ : ℝ) (hκ : 0 < κ) (Ch T0 C0 ε : ℝ) (hCh : 0 < Ch) (hε : 0 < ε) :
    ∃ Y0 : ℝ, ∀ Y Q Z : ℝ, Y0 ≤ Y → 1 ≤ Q → Q ≤ Real.log Y ^ κ → 1 ≤ Z → Z ≤ Real.log Y ^ κ →
      Real.log Y / 3 ≤ Real.log (Real.sqrt (Y / (Ch * Z ^ 3))) ∧
      Real.log (Real.sqrt (Y / (Ch * Z ^ 3))) ≤ Real.log Y ∧
      T0 ≤ Real.sqrt (Y / (Ch * Z ^ 3)) ∧
      T0 ≤ Z * Real.sqrt (Y / (Ch * Z ^ 3)) ∧
      2 * Q ≤ Real.log (Real.sqrt (Y / (Ch * Z ^ 3))) ^ (κ + 1) ∧
      Z ≤ Real.log (Real.sqrt (Y / (Ch * Z ^ 3))) ^ (κ + 1) ∧
      C0 * (2 * Q) ^ 2 ≤ Real.sqrt (Y / (Ch * Z ^ 3)) ∧
      (2 * Q) ^ 2 * Real.log (Real.sqrt (Y / (Ch * Z ^ 3))) ^ 6 ≤ ε * Real.sqrt (Y / (Ch * Z ^ 3)) ∧
      Q ^ 6 * Z ^ 4 * Real.log (Real.sqrt (Y / (Ch * Z ^ 3))) ^ 6 ≤ ε * Real.sqrt (Y / (Ch * Z ^ 3)) ^ 2 := by
  -- With T = √(Y/(Ch Z³)) and Q, Z ≤ (log Y)^κ: log T = (log Y - log Ch - 3 log Z)/2 ∈ [log Y / 3, log Y] for
  -- large Y; every remaining inequality is "polylog(Y) ≤ ε·Y^{1/2}" or "polylog ≤ polylog with a larger exponent",
  -- true for Y ≥ Y0(κ, Ch, T0, C0, ε) by isLittleO_log_rpow_atTop. The nine `eventually` statements are
  -- combined through Filter.eventually_atTop; the explicit extraction of Y0 is left open.
  have hlogT : ∀ Y Z : ℝ, 0 < Y → 0 < Z →
      Real.log (Real.sqrt (Y / (Ch * Z ^ 3))) = (Real.log Y - Real.log Ch - 3 * Real.log Z) / 2 := by
    intro Y Z hY hZ
    rw [Real.log_sqrt (by positivity), Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    ring
  sorry

-- N47 two_height_core [assembly]
theorem two_height_core : ∃ c0 : ℝ, 0 < c0 ∧ c0 < 1 ∧ ∀ κ : ℝ, 0 < κ →
    ∃ cκ Yκ Qκ Zκ : ℝ, 0 < cκ ∧ ∀ Y Q Z : ℝ, Yκ ≤ Y → Qκ ≤ Q → Q ≤ Real.log Y ^ κ → Zκ ≤ Z →
      Z ≤ Real.log Y ^ κ →
      ∃ F : Finset (ℕ × ℕ),
        (∀ uv ∈ F, 0 < uv.1 ∧ 0 < uv.2 ∧ Nat.Coprime uv.1 uv.2 ∧
          c0 * Y ≤ ((uv.1 + uv.2 : ℕ) : ℝ) ∧ ((uv.1 + uv.2 : ℕ) : ℝ) ≤ Y ∧
          σ 1 (3600 * uv.1) + σ 1 (3600 * uv.2) = σ 1 (3600 * (uv.1 + uv.2)) ∧
          (3600 * uv.1 * uv.2 * (uv.1 + uv.2)).primeFactors.card ≤ 11) ∧
        cκ * Y * Q ^ 2 * Z / Real.log Y ^ 6 ≤ F.card := by
  -- Assembly (Theorem 1.3): for each retained denominator q ∈ [Q, 2Q] (good_denominators) and each retained
  -- triple (parameter_sieve, ≫ q³Z⁴ of them), plane_prime_count gives ≫ T²/(q² log⁶T) prime sextuples on the plane,
  -- with T = √(Y/(Ch Z³)) (threshold_lemma); planes meet in ≤ 1 point (planes_meet_once, union_card_bound), so the
  -- number of distinct sextuples is ≫ Q · Q³Z⁴ · T²/(Q² log⁶ T) ≫ Y Q² Z / log⁶ Y; each gives a core via
  -- core_from_sextuple with perimeter 3600·508 p4 p5 ∈ [c0 Y, Y] by region_bounds_int, and fibres are ≤ 8
  -- (core_fiber_le_eight). The bookkeeping is left open.
  refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
  intro κ hκ
  obtain ⟨M0, cW, Q0, hcW, hden⟩ := good_denominators
  obtain ⟨Z0, q0, c2, hZ0, hc2, hsieve⟩ := parameter_sieve _ (fun Z q A B C => Iff.rfl) M0
  sorry

-- N48 S_lower_bound [quantitative_improvement]
theorem S_lower_bound : ∀ κ : ℝ, 0 < κ → ∃ c X1 : ℝ, 0 < c ∧ ∀ x : ℝ, X1 ≤ x →
    c * x * Real.log x ^ (3 * κ - 5) ≤ S x := by
  -- From two_height_core at Q = Z = (log Y)^κ: ≫ Y (log Y)^{3κ-6} coprime cores (u, v) with perimeter in [c0 Y, Y];
  -- each core gives, via multiplier_solution, the ordered solutions (3600 g u, 3600 g v) for every g coprime to
  -- 3600 u v (u+v) with g ≤ x/Y, i.e. ≫ x/Y of them (coprime_density, ≤ 11 prime factors), pairwise distinct
  -- across cores and multipliers (multiplier_disjoint); summing the shells Y = x/2^j and applying S_ge_card
  -- gives S x ≫ x (log x)^{3κ-6} · log x. The summation is left open.
  intro κ hκ
  obtain ⟨c0, hc0, hc01, hcore⟩ := two_height_core
  obtain ⟨cκ, Yκ, Qκ, Zκ, hcκ, hcores⟩ := hcore κ hκ
  obtain ⟨c6, X0, hc6, hdens⟩ := coprime_density
  refine ⟨cκ * c6 / 4, max 10 (max Yκ X0), by positivity, ?_⟩
  intro x hx
  sorry

-- ===== Target =====

/-- Li's Theorem 1.1: for every fixed `R > 0`, `S x / (x (log x)^R)` tends to infinity. In particular `S` is not
asymptotic to `c * x` for any finite `c > 0`. -/
theorem li_1061 : ∀ R : ℝ, 0 < R →
    Tendsto (fun x : ℝ ↦ S x / (x * Real.log x ^ R)) atTop atTop := by
  intro R hR
  obtain ⟨c, X1, hc, hS⟩ := S_lower_bound ((R + 6) / 3) (by linarith)
  have h3 : 3 * ((R + 6) / 3) - 5 = R + 1 := by ring
  rw [h3] at hS
  have key : ∀ᶠ x in atTop, c * Real.log x ≤ S x / (x * Real.log x ^ R) := by
    filter_upwards [eventually_ge_atTop X1, eventually_gt_atTop 1] with x hx1 hx2
    have hx0 : 0 < x := by linarith
    have hlog : 0 < Real.log x := Real.log_pos hx2
    have hpos : 0 < x * Real.log x ^ R := by positivity
    rw [le_div_iff₀ hpos]
    calc c * Real.log x * (x * Real.log x ^ R) = c * x * Real.log x ^ (R + 1) := by
          rw [Real.rpow_add hlog, Real.rpow_one]; ring
      _ ≤ S x := hS x hx1
  exact tendsto_atTop_mono' atTop key (Real.tendsto_log_atTop.const_mul_atTop hc)

end Erdos1061
