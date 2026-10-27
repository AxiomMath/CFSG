module

public import CFSG.Certificates.Kernel.Tower.L3Sound
public import CFSG.Certificates.Kernel.Tower.ChiSound
public import Certificates.Kernel.Tower.L3XChecks
public import Certificates.Kernel.Tower.AChecks
public import Certificates.Kernel.Tower.L1Glue

public section

namespace Certificates.KernelTower

open Certificates.KernelTower CFSG.OddStandard.AltStdSmall4.Tower

theorem ch36408_l3_all {f : Nat} (hf : f < 28) : ch36408_l3 f = true := by
  interval_cases f
  exacts [ch36408_l30, ch36408_l31, ch36408_l32, ch36408_l33, ch36408_l34, ch36408_l35,
    ch36408_l36, ch36408_l37, ch36408_l38, ch36408_l39, ch36408_l310, ch36408_l311, ch36408_l312,
    ch36408_l313, ch36408_l314, ch36408_l315, ch36408_l316, ch36408_l317, ch36408_l318,
    ch36408_l319, ch36408_l320, ch36408_l321, ch36408_l322, ch36408_l323, ch36408_l324,
    ch36408_l325, ch36408_l326, ch36408_l327]

theorem ch36408_l3x_all {f : Nat} (hf : f < 28) : ch36408_l3x f = true := by
  interval_cases f
  exacts [ch36408_l3x0, ch36408_l3x1, ch36408_l3x2, ch36408_l3x3, ch36408_l3x4, ch36408_l3x5,
    ch36408_l3x6, ch36408_l3x7, ch36408_l3x8, ch36408_l3x9, ch36408_l3x10, ch36408_l3x11,
    ch36408_l3x12, ch36408_l3x13, ch36408_l3x14, ch36408_l3x15, ch36408_l3x16, ch36408_l3x17,
    ch36408_l3x18, ch36408_l3x19, ch36408_l3x20, ch36408_l3x21, ch36408_l3x22, ch36408_l3x23,
    ch36408_l3x24, ch36408_l3x25, ch36408_l3x26, ch36408_l3x27]

theorem ch36408_chw_all {i : Nat} (hi : i < 16) : chiWOK wrSM wrAC (wrChi i) = true := by
  interval_cases i
  exacts [ch36408_chw0, ch36408_chw1, ch36408_chw2, ch36408_chw3, ch36408_chw4, ch36408_chw5,
    ch36408_chw6, ch36408_chw7, ch36408_chw8, ch36408_chw9, ch36408_chw10, ch36408_chw11,
    ch36408_chw12, ch36408_chw13, ch36408_chw14, ch36408_chw15]

theorem l3_g_lt {f : Nat} (hf : f < 28) : l16 (l3P f) 1 < 8192 :=
  Nat.le_of_ble_eq_true (allB_eq_true.1 ch36408_l3g f hf)

theorem wr_mul_zero {c : Nat} (hc : c < 8192) : wm wrSM wrAC c 0 = c :=
  wr_model.inj _ (wr_model.mul_lt _ hc _ (by omega)) _ hc
    (by rw [wr_model.dec_mul _ hc _ (by omega), wr_model.dec_zero, mul_one])

variable (D : ExtData (Grp wrS)) {f : Nat}

theorem l3_model (hf : f < 28)
    (hFA : ∀ c < 8192, l16 (wrA (Nat.add 2 (l16 (l3P f) 0))) c < 8192 ∧
      D.α (subModel_wr.decW c) = subModel_wr.decW (l16 (wrA (Nat.add 2 (l16 (l3P f) 0))) c))
    (hdg : subModel_wr.decW (l16 (l3P f) 1) = D.g) :
    IsModel (⊤ : Subgroup (CycExt D)) 16384 (l3M f) (dec2 D subModel_wr.decW) :=
  tm_model wr_model D hFA (l3_g_lt hf) hdg

theorem l3M_even {a c : Nat} : l3M f (2 * a) (2 * c) = 2 * wm wrSM wrAC a c := by
  have h : ¬ 2 * a % 2 = 1 := by omega
  rw [l3M, tm_eq, if_neg h, Nat.mul_div_cancel_left a (by omega),
    Nat.mul_div_cancel_left c (by omega), Nat.mul_mod_right, Nat.add_zero]

theorem l3M_one {c : Nat} (hc : c < 8192) : l3M f (2 * c) 1 = 2 * c + 1 := by
  have h : ¬ 2 * c % 2 = 1 := by omega
  have e1 : (1 : Nat) / 2 = 0 := by norm_num
  have e2 : (1 : Nat) % 2 = 1 := by norm_num
  rw [l3M, tm_eq, if_neg h, Nat.mul_div_cancel_left c (by omega), e1, e2, wr_mul_zero hc]

theorem l3M_two {k : Nat} (hk : k < 16384) : l3M f 2 k = k ^^^ 2 := by
  have h : ¬ 2 % 2 = 1 := by omega
  have e1 : (2 : Nat) / 2 = 1 := by norm_num
  have hz := Nat.eq_of_beq_eq_true (allB_eq_true.1 ch36408_l3z k hk)
  have e3 : Nat.land k 1 = k % 2 := Nat.and_one_is_mod k
  rw [shr1, e3] at hz
  rw [l3M, tm_eq, if_neg h, e1]
  exact hz

theorem l3_fam (hf : f < 28)
    (hFA : ∀ c < 8192, l16 (wrA (Nat.add 2 (l16 (l3P f) 0))) c < 8192 ∧
      D.α (subModel_wr.decW c) = subModel_wr.decW (l16 (wrA (Nat.add 2 (l16 (l3P f) 0))) c))
    (hdg : subModel_wr.decW (l16 (l3P f) 1) = D.g) (β : CycExt D →* CycExt D)
    (hβ : ∀ i < 4, β (dec2 D subModel_wr.decW (2 * l16 wGS i)) =
      dec2 D subModel_wr.decW (l16 (Nat.shiftRight (l3P f) 48) i))
    (hb : β (dec2 D subModel_wr.decW 1) = dec2 D subModel_wr.decW (l16 (l3P f) 2)) :
    ∀ j < 16, ∀ k < 16384, (bitS (l3S f j) k = true ↔
      dec2 D subModel_wr.decW 2 ^ xbit (l3X f j) k *
          (dec2 D subModel_wr.decW k * β (dec2 D subModel_wr.decW k)) =
        dec2 D subModel_wr.decW (l3H f j)) :=
  famB_sound (l3_model D hf hFA hdg) ch36408_tree (fun _ _ _ _ => l3M_even) (fun _ hc => l3M_one hc)
    (fun _ hk => l3M_two hk) (ch36408_l3_all hf)
    (fun j hj k h => bitS_union 16 j hj h) β hβ hb

theorem l3_chi (hf : f < 28)
    (hFA : ∀ c < 8192, l16 (wrA (Nat.add 2 (l16 (l3P f) 0))) c < 8192 ∧
      D.α (subModel_wr.decW c) = subModel_wr.decW (l16 (wrA (Nat.add 2 (l16 (l3P f) 0))) c))
    {j : Nat} (hj : j < 16) {a b : Nat} (ha : a < 16384) (hb : b < 16384) :
    xbit (l3X f j) (l3M f a b) = xbit (l3X f j) a ^^^ xbit (l3X f j) b :=
  xbit_tm ch36408_par (fun i hi => ch36408_chw_all hi)
    (allB_eq_true.1 (ch36408_l3x_all hf) j hj) wr_model ch36408_tree D.α.toMonoidHom
    (fun c hc => hFA c hc) (l3_g_lt hf) ha hb

end Certificates.KernelTower
