module

public import CFSG.Certificates.Kernel.LceSTabSound
public import CFSG.Certificates.Kernel.Misc.Coset.PG

public section

namespace CertificateChecks.KernelMult

open CFSG.KC CFSG.KC.LceS CFSG.Certificates.LCE CFSG.CosetTable

@[expose] def code {m : ℕ} (l : Fin m × Bool) : ℕ := 2 * l.1.val + (if l.2 then 0 else 1)

@[expose] def wordNat {m : ℕ} : List (Fin m × Bool) → ℕ
  | [] => 0
  | l :: w => code l + 256 * wordNat w

@[expose] def ent {m : ℕ} (w : List (Fin m × Bool)) : ℕ := 4 * w.length + 4096 * wordNat w

theorem wLet_eq (W i : ℕ) : wLet W i = W / 2 ^ (8 * i) % 256 := by
  change (W >>> (8 * i)) &&& (2 ^ 8 - 1) = _
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.and_two_pow_sub_one_eq_mod _ 8

theorem bval_succ {G : Type*} [Group G] (gen : ℕ → G) (W n : ℕ) :
    bval gen W (n + 1) = letV gen (wLet W 0) * bval gen (W / 256) n := by
  unfold bval
  rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]
  congr 2
  apply List.map_congr_left
  intro q _
  simp only [Function.comp_apply, wLet_eq, Nat.div_div_eq_div_mul]
  congr 3
  rw [Nat.succ_eq_add_one, Nat.mul_add, pow_add]
  ring

theorem bval_wordNat {m : ℕ} (hm : m < 127) (ws : List (List (Fin m × Bool))) :
    ∀ w : List (Fin m × Bool), bval (CFSG.KC.MiscCoset.pgGen ws) (wordNat w) w.length =
      PresentedGroup.mk _ (FreeGroup.mk w)
  | [] => rfl
  | l :: w => by
    obtain ⟨g, b⟩ := l
    have hg := g.isLt
    have hc : code (g, b) = 2 * g.val + (if b then 0 else 1) := rfl
    have e0 : wordNat ((g, b) :: w) = code (g, b) + 256 * wordNat w := rfl
    have hc' : code (g, b) < 255 := by
      rw [hc]
      split_ifs <;> omega
    have e1 : wLet (wordNat ((g, b) :: w)) 0 = code (g, b) := by
      rw [wLet_eq, e0, Nat.mul_zero, pow_zero, Nat.div_one]
      omega
    have e2 : wordNat ((g, b) :: w) / 256 = wordNat w := by
      rw [e0]
      omega
    rw [List.length_cons, bval_succ, e1, e2, bval_wordNat hm ws w,
      show FreeGroup.mk ((g, b) :: w) = FreeGroup.mk [(g, b)] * FreeGroup.mk w from rfl, map_mul]
    congr 1
    have hp : CFSG.KC.MiscCoset.pgGen ws g.val = PresentedGroup.of g := by
      simp [CFSG.KC.MiscCoset.pgGen, g.isLt]
    unfold letV
    rw [hc]
    cases b
    · have h1 : ¬ (2 * g.val + 1) % 2 = 0 := by omega
      have h2 : (2 * g.val + 1) / 2 = g.val := by omega
      have h3 : ¬ 2 * g.val + 1 = 255 := by omega
      simp only [Bool.false_eq_true, ↓reduceIte, h1, h2, h3, hp]
      rfl
    · have h1 : (2 * g.val + 0) % 2 = 0 := by omega
      have h2 : (2 * g.val + 0) / 2 = g.val := by omega
      have h3 : ¬ 2 * g.val + 0 = 255 := by omega
      simp only [↓reduceIte, h1, h2, h3, hp]
      rfl

theorem bval_ent {m : ℕ} (hm : m < 127) (ws : List (List (Fin m × Bool))) {e : ℕ}
    (w : List (Fin m × Bool)) (h : e = ent w) (hlen : w.length < 1024) :
    bval (CFSG.KC.MiscCoset.pgGen ws) (wWord e) (wLen e) = PresentedGroup.mk _ (FreeGroup.mk w) := by
  have h1 : wWord e = wordNat w := by
    rw [h]
    change (4 * w.length + 4096 * wordNat w) >>> 12 = _
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have h2 : wLen e = w.length := by
    rw [h]
    change ((4 * w.length + 4096 * wordNat w) >>> 2) &&& (2 ^ 10 - 1) = _
    rw [Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [h1, h2]
  exact bval_wordNat hm ws w

end CertificateChecks.KernelMult

end
