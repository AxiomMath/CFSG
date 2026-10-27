module

public import CFSG.Certificates.Kernel.Tower.L3TSound
public import Certificates.Kernel.Tower.L3Glue
public import Certificates.Kernel.Tower.L3WChecks

public section

namespace Certificates.KernelTower

open Certificates.KernelTower CFSG.OddStandard.AltStdSmall4.Tower

theorem ch36408_l3t_all {f : Nat} (hf : f < 28) : ch36408_l3t f = true := by
  interval_cases f
  exacts [ch36408_l3t0, ch36408_l3t1, ch36408_l3t2, ch36408_l3t3, ch36408_l3t4, ch36408_l3t5,
    ch36408_l3t6, ch36408_l3t7, ch36408_l3t8, ch36408_l3t9, ch36408_l3t10, ch36408_l3t11,
    ch36408_l3t12, ch36408_l3t13, ch36408_l3t14, ch36408_l3t15, ch36408_l3t16, ch36408_l3t17,
    ch36408_l3t18, ch36408_l3t19, ch36408_l3t20, ch36408_l3t21, ch36408_l3t22, ch36408_l3t23,
    ch36408_l3t24, ch36408_l3t25, ch36408_l3t26, ch36408_l3t27]

theorem l3_parts {f : Nat} (hf : f < 28) :
    l16 (wrA (Nat.add 2 (l16 (l3P f) 0))) 1 = 1 ∧ ∀ j < 16,
      tgtOK (l3M f) wGS (Nat.shiftRight (l3P f) 48) (l16 (l3P f) 2) (l3G f) (l3Im f j) (l3Wd f)
        (l3X f j) (l3H f j) (l3g2 f j) = true := by
  have h := ch36408_l3t_all hf
  simp only [ch36408_l3t, Bool.and_eq_true, allB_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, h.2⟩

variable (D : ExtData (Grp wrS)) {f : Nat}

theorem l3_center (hf : f < 28)
    (hFA : ∀ c < 8192, l16 (wrA (Nat.add 2 (l16 (l3P f) 0))) c < 8192 ∧
      D.α (subModel_wr.decW c) = subModel_wr.decW (l16 (wrA (Nat.add 2 (l16 (l3P f) 0))) c)) :
    ∀ y : CycExt D, dec2 D subModel_wr.decW 2 * y = y * dec2 D subModel_wr.decW 2 := by
  have hz1 : ∀ k : Grp wrS, subModel_wr.decW 1 * k = k * subModel_wr.decW 1 := by
    intro k
    obtain ⟨c, hc, rfl⟩ := wr_model.surj k (Subgroup.mem_top k)
    rw [← wr_model.dec_mul _ (by omega) _ hc, ← wr_model.dec_mul _ hc _ (by omega),
      Nat.eq_of_beq_eq_true (allB_eq_true.1 ch36408_l3c c hc)]
  have hα : D.α (subModel_wr.decW 1) = subModel_wr.decW 1 := by
    rw [(hFA 1 (by omega)).2, (l3_parts hf).1]
  have e2 : dec2 D subModel_wr.decW 2 = ⟨subModel_wr.decW 1, false⟩ := rfl
  intro y
  obtain ⟨k, d⟩ := y
  rw [e2]
  cases d <;> simp [CycExt.mk_mul_mk, CycExt.pw, CycExt.sq, hz1, hα]

theorem l3_tgt (hf : f < 28)
    (hFA : ∀ c < 8192, l16 (wrA (Nat.add 2 (l16 (l3P f) 0))) c < 8192 ∧
      D.α (subModel_wr.decW c) = subModel_wr.decW (l16 (wrA (Nat.add 2 (l16 (l3P f) 0))) c))
    (hdg : subModel_wr.decW (l16 (l3P f) 1) = D.g) {j : Nat} (hj : j < 16)
    (β : CycExt D →* CycExt D)
    (hβ : ∀ i < 4, β (dec2 D subModel_wr.decW (l16 (l3G f) i)) =
      dec2 D subModel_wr.decW (l16 (l3Im f j) i)) :
    ∀ k < 16384, (bitS (l3S f j) k = true ↔
      dec2 D subModel_wr.decW k * β (dec2 D subModel_wr.decW k) *
        dec2 D subModel_wr.decW (l3g2 f j) = 1) := by
  obtain ⟨hIM, hb, -⟩ := famB_parts (ch36408_l3_all hf)
  exact tgt_sound (l3_model D hf hFA hdg) (fun _ hk => l3M_two hk) (l3_center D hf hFA)
    (fun _ ha _ hb => l3_chi D hf hFA hj ha hb) ((l3_parts hf).2 j hj) hIM hb
    (fun β₀ h1 h2 => l3_fam D hf hFA hdg β₀ h1 h2 j hj) β hβ

theorem l3_invol (hf : f < 28)
    (hFA : ∀ c < 8192, l16 (wrA (Nat.add 2 (l16 (l3P f) 0))) c < 8192 ∧
      D.α (subModel_wr.decW c) = subModel_wr.decW (l16 (wrA (Nat.add 2 (l16 (l3P f) 0))) c))
    (hdg : subModel_wr.decW (l16 (l3P f) 1) = D.g) {j : Nat} (hj : j < 16)
    (D' : ExtData (CycExt D))
    (hβ : ∀ i < 4, D'.α (dec2 D subModel_wr.decW (l16 (l3G f) i)) =
      dec2 D subModel_wr.decW (l16 (l3Im f j) i))
    (hg : D'.g = dec2 D subModel_wr.decW (l3g2 f j)) :
    ∀ k < 16384, (bitS (l3S f j) k = true ↔
      (⟨dec2 D subModel_wr.decW k, true⟩ : CycExt D') ^ 2 = 1) := by
  have e : ∀ x : CycExt D, ((⟨x, true⟩ : CycExt D') ^ 2 = 1) ↔ x * D'.α x * D'.g = 1 := by
    intro x
    rw [pow_two, CycExt.mk_mul_mk D' x x true true, CycExt.one_def]
    simp [CycExt.pw, CycExt.sq]
  intro k hk
  rw [l3_tgt D hf hFA hdg hj D'.α.toMonoidHom hβ k hk, e, hg, MulEquiv.coe_toMonoidHom]

end Certificates.KernelTower
