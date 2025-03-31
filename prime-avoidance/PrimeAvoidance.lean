import Mathlib.RingTheory.Ideal.Prime

universe u
variable {α : Type u}
variable [CommRing α]

namespace Double
variable (P₁ : Ideal α) (P₂ : Ideal α)
variable (I : Ideal α)

theorem prime_avoidance (hI₁ : ¬ (I ≤ P₁)) (hI₂ : ¬ (I ≤ P₂)) : ∃ (a : α), a ∈ I ∧ a ∉ P₁ ∧ a ∉ P₂ := by
  have ⟨a₁, ⟨ha₁, ha₁'⟩⟩ := Set.not_subset.mp hI₁
  have ⟨a₂, ⟨ha₂, ha₂'⟩⟩ := Set.not_subset.mp hI₂
  cases (em (a₁ ∈ P₂)) with
  | inl ha₁'' =>
    cases (em (a₂ ∈ P₁)) with
    | inl ha₂'' =>
      exists (a₁ + a₂)
      constructor <;> (try constructor)
      . apply Ideal.add_mem <;> assumption
      . by_contra cont
        have := Iff.mp (Ideal.add_mem_iff_left _ ha₂'') cont
        contradiction
      . by_contra cont
        have := Iff.mp (Ideal.add_mem_iff_right _ ha₁'') cont
        contradiction
    | inr ha₂'' =>
      exists a₂
  | inr ha₁'' =>
    exists a₁
end Double

namespace Triple
variable (P₁ : Ideal α) (P₂ : Ideal α) (P₃ : Ideal α)
variable (I : Ideal α)

theorem prime_avoidance
  (_ : Ideal.IsPrime P₁) (_ : Ideal.IsPrime P₂) (hP₃ : Ideal.IsPrime P₃)
  (hI₁ : ¬ (I ≤ P₁)) (hI₂ : ¬ (I ≤ P₂)) (hI₃ : ¬ (I ≤ P₃))
  : ∃ (a : α), a ∈ I ∧ a ∉ P₁ ∧ a ∉ P₂ ∧ a ∉ P₃ := by
  cases (em (I ⊓ P₁ ≤ P₃)) with
  | inl hP₁₃ =>
    have ⟨a, ⟨ha, ha', ha''⟩⟩ := Double.prime_avoidance _ _ _ hI₂ hI₃
    exists a
    repeat (any_goals constructor)
    . assumption
    . by_contra cont
      have := hP₁₃ (Set.mem_inter ha cont)
      contradiction
    . assumption
    . assumption
  | inr hP₁₃ =>
    cases (em (I ⊓ P₂ ≤ P₃)) with
    | inl hP₂₃ =>
      have ⟨a, ⟨ha, ha', ha''⟩⟩ := Double.prime_avoidance _ _ _ hI₁ hI₃
      exists a
      repeat (any_goals constructor)
      . assumption
      . assumption
      . by_contra cont
        have := hP₂₃ (Set.mem_inter ha cont)
        contradiction
      . assumption
    | inr hP₂₃ =>
      have ⟨a₁, ⟨ha₁, ha₁'⟩⟩ := Set.not_subset.mp hP₁₃
      have ⟨a₂, ⟨ha₂, ha₂'⟩⟩ := Set.not_subset.mp hP₂₃
      have ha₁a₂ := Ideal.mul_mem_right a₂ P₁ ha₁.right
      have ha₁a₂' := Ideal.mul_mem_left P₂ a₁ ha₂.right
      have ha₁a₂'' : a₁ * a₂ ∉ P₃ := by
        apply (
          Ideal.IsPrime.mul_mem_iff_mem_or_mem (x := a₁) (y := a₂) hP₃
          |> Iff.not
          |> Iff.mpr
        )
        push_neg
        constructor <;> assumption
      have ⟨a₁₂, ⟨ha₁₂, ha₁₂', ha₁₂''⟩⟩ := Double.prime_avoidance _ _ _ hI₁ hI₂
      cases (em (a₁₂ ∈ P₃)) with
      | inr ha₁₂''' => exists a₁₂
      | inl ha₁₂''' =>
        exists (a₁ * a₂) + a₁₂
        repeat (any_goals constructor)
        . apply Ideal.add_mem
          . apply Ideal.mul_mem_left
            exact Set.mem_of_mem_inter_left ha₂
          . assumption
        . by_contra cont
          have := Iff.mp (Ideal.add_mem_iff_right _ ha₁a₂) cont
          contradiction
        . by_contra cont
          have := Iff.mp (Ideal.add_mem_iff_right _ ha₁a₂') cont
          contradiction
        . by_contra cont
          have := Iff.mp (Ideal.add_mem_iff_left _ ha₁₂''') cont
          contradiction
end Triple

namespace General
variable (Ps : List (Ideal α))
variable (I : Ideal α)

-- TODO: prove it
theorem prime_avoidance
  (hPs : List.Forall (fun P => Ideal.IsPrime P ∧ ¬ (I ≤ P)) Ps)
  : ∃ (a : α), a ∈ I ∧ List.Forall (fun P => a ∉ P) Ps := by
    sorry
end General
