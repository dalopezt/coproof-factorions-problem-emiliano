import «upper_bound».«main»
import «finite_search».«main»
import Definitions
-- Sub-goal 1: For every n > 2540160, digitFactorialSum n < n



theorem root : {n : ℕ | digitFactorialSum n = n} = {1, 2, 145, 40585} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra hne
    have hle : n ≤ 2540160 := by
      by_contra hgt
      push_neg at hgt
      have := upper_bound n hgt
      omega
    have hmem : n ∈ {n : ℕ | digitFactorialSum n = n ∧ n ≤ 2540160} := by
      simp only [Set.mem_setOf_eq]
      exact ⟨h, hle⟩
    rw [finite_search] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    tauto
  · intro h
    rcases h with rfl | rfl | rfl | rfl
    · have hmem : (1 : ℕ) ∈ {n : ℕ | digitFactorialSum n = n ∧ n ≤ 2540160} := by
        rw [finite_search]; simp
      exact hmem.1
    · have hmem : (2 : ℕ) ∈ {n : ℕ | digitFactorialSum n = n ∧ n ≤ 2540160} := by
        rw [finite_search]; simp
      exact hmem.1
    · have hmem : (145 : ℕ) ∈ {n : ℕ | digitFactorialSum n = n ∧ n ≤ 2540160} := by
        rw [finite_search]; simp
      exact hmem.1
    · have hmem : (40585 : ℕ) ∈ {n : ℕ | digitFactorialSum n = n ∧ n ≤ 2540160} := by
        rw [finite_search]; simp
      exact hmem.1
