-- R を可換環とする
-- 𝔪 が R の極大イデアルで、n が正整数のとき、R⧸𝔪^n は局所環であることを示す

-- 参考文献
-- 永井保成「代数学入門 群・環・体の基礎とガロワ理論」, 森北出版, 2024

import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Algebra.Algebra.Operations
import Mathlib.RingTheory.Ideal.Maps

section S
universe u
variable {R : Type u}
variable [CommRing R]
variable {𝔪 : Ideal R} (max_𝔪: 𝔪.IsMaximal)

-- R⧸𝔪 が体であることを Lean に認識させる
-- (⧸ は \/ で入力できる)
-- 参考: <https://github.com/leanprover-community/mathlib4/blob/dc4f49f1f40598a6fbc01acc17fdbea3dcd45208/Mathlib/RingTheory/Frobenius.lean#L209>
-- なぜ以下の記述が必要かは以下のリンクを読むと良さそう (Lean 3 の資料なので古いかもしれない)
-- 参考: <https://leanprover-community.github.io/mathlib_docs/notes.html#reducible%20non-instances>
attribute [local instance] Ideal.Quotient.field

-- ちゃんと認識できているか確認する
#synth Field (R⧸𝔪)

-- R⧸𝔪 が体であることから局所環であることも分かる
#synth IsLocalRing (R⧸𝔪)

-- n = 1 のときは上で認識させたインスタンスから直ちに導かれる
def quot_ring_is_local_1 : IsLocalRing (R⧸𝔪) := inferInstance

-- · • · などの演算の正体を探る
set_option pp.notation false

-- • は \smul で入力できる
#check 𝔪 • 𝔪
-- → HSMul.hSMul

#synth HSMul (Ideal R) (Ideal R) (Ideal R)
-- Infoview で出力のポップオーバーを辿っていくと Submodule.instSMul であることが分かる
-- (もっと簡単な方法がありそう)
-- 参考: <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Algebra/Operations.html#Submodule.instSMul>

#check 𝔪 * 𝔪
-- → HMul.hMul

#check 𝔪 + 𝔪
-- → HAdd.hAdd
-- → Submodule.pointwiseAdd
-- 参考: <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/Submodule/Pointwise.html#Submodule.pointwiseAdd>

set_option pp.notation true

lemma pow_le_pow_one {n} (hn : 1 ≤ n) : 𝔪^n ≤ 𝔪 := by
  have := Ideal.pow_le_pow_right (I := 𝔪) hn
  rw [Submodule.pow_one] at this
  trivial

lemma map_Quotient_mk_pow {n} (hn : 1 ≤ n) : Ideal.map (Ideal.Quotient.mk (𝔪^n)) 𝔪 = Ideal.comap (Ideal.Quotient.factor (pow_le_pow_one hn)) 0 := by
  ext y
  constructor
  . intros mem_y
    have ⟨x, mem_x, E⟩ := (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective).mp mem_y
    rw [← E, Ideal.mem_comap, Ideal.Quotient.factor_mk (pow_le_pow_one hn)]
    rw [Ideal.zero_eq_bot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    trivial
  . intros mem_y
    rw [Ideal.mem_comap, Ideal.zero_eq_bot, Ideal.mem_bot] at mem_y
    rw [← Ideal.Quotient.mk_out y, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at mem_y
    apply (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective).mpr
    exists Quotient.out y
    constructor <;> try trivial
    rw [Ideal.Quotient.mk_out]

def map_Quotient_mk_pow_IsMaximal {n} (hn : 1 ≤ n) : (Ideal.map (Ideal.Quotient.mk (𝔪^n)) 𝔪).IsMaximal := by
  rw [map_Quotient_mk_pow hn]
  apply Ideal.comap_isMaximal_of_surjective (H := Ideal.bot_isMaximal)
  apply Ideal.Quotient.factor_surjective

-- 一般の n について示す前に n = 2 のケースで証明方法を確認しておく
-- theorem にすると max_𝔪 が消えてしまうので仕方なく def を使う
def quot_ring_is_local_2 : IsLocalRing (R⧸𝔪•𝔪) :=
  IsLocalRing.of_unique_max_ideal (by
    suffices H : ∀ I : Ideal R, I.IsMaximal → 𝔪 • 𝔪 ≤ I → I ≤ 𝔪 from
      ⟨
        Ideal.map (Ideal.Quotient.mk (𝔪 • 𝔪)) 𝔪,
        by
          have := map_Quotient_mk_pow_IsMaximal max_𝔪 (n := 2) (by trivial)
          rw [Submodule.pow_succ, Submodule.pow_one] at this
          trivial,
        by
          intros I max_I
          have H1 : (Ideal.comap (Ideal.Quotient.mk _) I).IsMaximal := by
            apply Ideal.comap_isMaximal_of_surjective
            apply Ideal.Quotient.mk_surjective
          have H2 : 𝔪 • 𝔪 ≤ Ideal.comap (Ideal.Quotient.mk _) I := by
            intro x mem_x
            rw [Ideal.mem_comap]
            rw [Ideal.Quotient.eq_zero_iff_mem.mpr mem_x]
            apply Ideal.zero_mem
          have H3 := H _ H1 H2
          have E : Ideal.comap (Ideal.Quotient.mk (𝔪 • 𝔪)) I = 𝔪 := Ideal.IsMaximal.eq_of_le H1 (Ideal.isMaximal_def.mp max_𝔪).left H3
          symm
          -- 書き換えたい 𝔪 は複数回出現している。rw だとどの出現を書き換えるか指定することになるが、
          -- 分かりにくいので、calc を使っている
          calc _
            _ = Ideal.map (Ideal.Quotient.mk (𝔪 • 𝔪)) (Ideal.comap (Ideal.Quotient.mk (𝔪 • 𝔪)) I) := by congr; rw [E]
            _ = I := by rw [Ideal.map_comap_of_surjective]; apply Ideal.Quotient.mk_surjective
      ⟩
    intros I max_I I_inc
    by_cases (I + 𝔪 = ⊤)
    case pos E =>
      apply le_of_eq
      have : 1 ∈ I + 𝔪 := by rw [E, ← Ideal.eq_top_iff_one]
      have ⟨a, mem_a, b, mem_b, E1⟩ := Submodule.mem_sup.mp this
      have : 𝔪 ≤ I := by
        intro x mem_x
        have : x = x * a + x * b := by rw [← mul_add, E1, mul_one]
        rw [this]
        apply Ideal.add_mem
        . apply Ideal.mul_mem_left
          trivial
        . apply Set.mem_of_subset_of_mem I_inc
          apply Submodule.smul_mem_smul <;> trivial
      have : 𝔪 = I := Ideal.IsMaximal.eq_of_le max_𝔪 (Ideal.isMaximal_def.mp max_I).left this
      symm
      trivial
    case neg NE =>
      rw [Ideal.IsMaximal.eq_of_le max_𝔪 NE le_add_self]
      apply le_self_add
  )

-- 一般の場合は n = 2 とほとんど同じように示せる
def quot_ring_is_local_general {n} (hn : 1 ≤ n) : IsLocalRing (R⧸𝔪^n) :=
  IsLocalRing.of_unique_max_ideal (by
    suffices H : ∀ I : Ideal R, I.IsMaximal → 𝔪^n ≤ I → I ≤ 𝔪 from
      ⟨
        Ideal.map (Ideal.Quotient.mk (𝔪^n)) 𝔪,
        by apply map_Quotient_mk_pow_IsMaximal max_𝔪 hn,
        by
          intros I max_I
          have H1 : (Ideal.comap (Ideal.Quotient.mk _) I).IsMaximal := by
            apply Ideal.comap_isMaximal_of_surjective
            apply Ideal.Quotient.mk_surjective
          have H2 : 𝔪^n ≤ Ideal.comap (Ideal.Quotient.mk _) I := by
            intro x mem_x
            rw [Ideal.mem_comap]
            rw [Ideal.Quotient.eq_zero_iff_mem.mpr mem_x]
            apply Ideal.zero_mem
          have : Ideal.comap (Ideal.Quotient.mk _) I ≤ 𝔪 := H _ H1 H2
          have E : Ideal.comap (Ideal.Quotient.mk _) I = 𝔪 :=
            Ideal.IsMaximal.eq_of_le H1 (Ideal.isMaximal_def.mp max_𝔪).left this
          symm
          calc
            _ = Ideal.map (Ideal.Quotient.mk _) (Ideal.comap (Ideal.Quotient.mk _) I) := by congr; rw [E]
            _ = I := by rw [Ideal.map_comap_of_surjective]; apply Ideal.Quotient.mk_surjective
      ⟩
    intros I max_I I_inc
    by_cases (I + 𝔪 = ⊤)
    case pos ET =>
      cases n with
      | zero => contradiction
      | succ n' =>
        apply le_of_eq
        symm
        apply (Ideal.IsMaximal.eq_of_le max_𝔪 (Ideal.isMaximal_def.mp max_I).left)
        have H1 : 1 ∈ I + 𝔪 := by rw [ET, ← Ideal.eq_top_iff_one]
        have Hm : ∀ m, 1 ∈ I + 𝔪^m := by
          intros m
          induction m with
          | zero =>
            rw [Submodule.pow_zero]
            -- x ∈ I → x ∈ I + J は Loogle で検索しても出てこない
            -- I + J を I ⊔ J に変えると出てくる
            apply Submodule.mem_sup_right
            rw [Ideal.one_eq_top]
            apply Submodule.mem_top
          | succ m' IHm' =>
            have ⟨a, mem_a, b, mem_b, E1⟩ := Submodule.mem_sup.mp H1
            have ⟨a', mem_a', b', mem_b', Em'⟩ := Submodule.mem_sup.mp IHm'
            have : 1 = (a' * (a + b) + b' * a) + b' * b := by
              rw [add_assoc, ← left_distrib, ← right_distrib, E1, Em', mul_one]
            rw [this]
            repeat' apply Ideal.add_mem
            . apply Submodule.mem_sup_left; apply Ideal.mul_mem_right; trivial
            . apply Submodule.mem_sup_left; apply Ideal.mul_mem_left; trivial
            . apply Submodule.mem_sup_right
              rw [Submodule.pow_succ]
              apply Submodule.mul_mem_mul <;> trivial
        have ⟨a, mem_a, b, mem_b, E1⟩ := Submodule.mem_sup.mp (Hm n')
        intros x mem_x
        have : x = x * a + x * b := by rw [← mul_add, E1, mul_one]
        rw [this]
        apply Ideal.add_mem
        . apply Ideal.mul_mem_left; trivial
        . apply Set.mem_of_subset_of_mem I_inc
          rw [mul_comm, Submodule.pow_succ]
          apply Submodule.mul_mem_mul <;> trivial
    case neg NET =>
      -- x ≤ x + y, y ≤ x + y のような不等式が使えるクラスは CanonicallyOrderedAdd
      -- 参考: <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Order/Monoid/Canonical/Defs.html#CanonicallyOrderedAdd>
      rw [Ideal.IsMaximal.eq_of_le max_𝔪 NET le_add_self]
      apply le_self_add
  )

end S
