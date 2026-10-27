module

public import Certificates.Kernel.Om1K.BSound
public import Certificates.Kernel.Om1K.BChecksT
public import Certificates.Kernel.Om1K.BChecksO
public import Certificates.Kernel.Om1K.BChecksW0
public import Certificates.Kernel.Om1K.BChecksW1
public import Certificates.Kernel.Om1K.BChecksW2
public import Certificates.Kernel.Om1K.BChecksW3
public import Certificates.Kernel.Om1K.BChecksQ0
public import Certificates.Kernel.Om1K.BChecksQ
import CFSG.Certificates.Kernel.BfsPinBaseSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelOm1.B

open CFSG.KC.Enum CFSG.KS

theorem wit0c_all : ∀ c < 64, wit0c c = true := by
  intro c hc
  interval_cases c
  exacts [wit0c0, wit0c1, wit0c2, wit0c3, wit0c4, wit0c5, wit0c6, wit0c7, wit0c8, wit0c9,
    wit0c10, wit0c11, wit0c12, wit0c13, wit0c14, wit0c15, wit0c16, wit0c17, wit0c18, wit0c19,
    wit0c20, wit0c21, wit0c22, wit0c23, wit0c24, wit0c25, wit0c26, wit0c27, wit0c28, wit0c29,
    wit0c30, wit0c31, wit0c32, wit0c33, wit0c34, wit0c35, wit0c36, wit0c37, wit0c38, wit0c39,
    wit0c40, wit0c41, wit0c42, wit0c43, wit0c44, wit0c45, wit0c46, wit0c47, wit0c48, wit0c49,
    wit0c50, wit0c51, wit0c52, wit0c53, wit0c54, wit0c55, wit0c56, wit0c57, wit0c58, wit0c59,
    wit0c60, wit0c61, wit0c62, wit0c63]

theorem wit0_all : ∀ i < 4096, witOK E0.T 4096 BD.W0 i = true := by
  intro i hi
  have h := allN_spec (wit0c_all (i / 64) (by omega)) (i % 64) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 64 (i / 64)) (i % 64) = i := Nat.div_add_mod i 64
  rw [e] at h
  exact h

theorem q80_all : ∀ a < 240, q8Row E0.T BD.RT0 BD.PR0 BD.LhG BD.LhI 57 240 true a = true := by
  intro a ha
  have hc : ∀ c < 15, q80c c = true := by
    intro c hc
    interval_cases c
    exacts [q80c0, q80c1, q80c2, q80c3, q80c4, q80c5, q80c6, q80c7, q80c8, q80c9, q80c10,
      q80c11, q80c12, q80c13, q80c14]
  have h := allN_spec (hc (a / 16) (by omega)) (a % 16) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 16 (a / 16)) (a % 16) = a := Nat.div_add_mod a 16
  rw [e] at h
  exact h

theorem q8a_all : ∀ a < 96, q8Row Ea.T BD.RTa BD.PRa BD.LhG BD.LhI 0 96 false a = true := by
  intro a ha
  have hc : ∀ c < 6, q8ac c = true := by
    intro c hc
    interval_cases c
    exacts [q8ac0, q8ac1, q8ac2, q8ac3, q8ac4, q8ac5]
  have h := allN_spec (hc (a / 16) (by omega)) (a % 16) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 16 (a / 16)) (a % 16) = a := Nat.div_add_mod a 16
  rw [e] at h
  exact h

theorem q8c_all : ∀ a < 48, q8Row Ec.T BD.RTc BD.PRc BD.LcG BD.LcI 31 48 false a = true := by
  intro a ha
  have hc : ∀ c < 3, q8cc c = true := by
    intro c hc
    interval_cases c
    exacts [q8cc0, q8cc1, q8cc2]
  have h := allN_spec (hc (a / 16) (by omega)) (a % 16) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 16 (a / 16)) (a % 16) = a := Nat.div_add_mod a 16
  rw [e] at h
  exact h

theorem cnt0 : ((List.range 4096).filter (noWit BD.W0)).length ≤ 64 := by
  rw [← cntN_eq]
  exact Nat.le_of_ble_eq_true kC0

theorem cnt1 : ((List.range 27).filter (noWit BD.W1)).length ≤ 3 := by
  rw [← cntN_eq]
  exact Nat.le_of_ble_eq_true kC1

theorem tupK_inj : ∀ a < 576, ∀ b < 576, tupK a = tupK b → a = b :=
  CFSG.KC.BfsPin.distinctK_inj kOS

end CertificateChecks.KernelOm1.B

end
