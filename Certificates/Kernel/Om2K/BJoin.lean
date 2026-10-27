module

public import Certificates.Kernel.Om2K.BSound
public import Certificates.Kernel.Om2K.BChecksT
public import Certificates.Kernel.Om2K.BChecksW0
public import Certificates.Kernel.Om2K.BChecksW1
public import Certificates.Kernel.Om2K.BChecksW2
public import Certificates.Kernel.Om2K.BChecksW3
public import Certificates.Kernel.Om2K.BChecksQ
import CFSG.Certificates.Kernel.Spor.Loops

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelOm2

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

theorem q80c_all : ∀ c < 15, q80c c = true := by
  intro c hc
  interval_cases c
  exacts [q80c0, q80c1, q80c2, q80c3, q80c4, q80c5, q80c6, q80c7, q80c8, q80c9, q80c10, q80c11,
    q80c12, q80c13, q80c14]

theorem q80_all : ∀ a < 240,
    q8Row E0.T BD.RT0 BD.PR0 BD.LhG BD.LhI 73 BD.nR0 true a = true := by
  intro a ha
  have h := allN_spec (q80c_all (a / 16) (by omega)) (a % 16) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 16 (a / 16)) (a % 16) = a := Nat.div_add_mod a 16
  rw [e] at h
  exact h

theorem q82_all : ∀ a < 48,
    q8Row E2.T BD.RT2 BD.PR2 BD.LcG BD.LcI 31 BD.nR2 false a = true := by
  intro a ha
  have hc : ∀ c < 3, q82c c = true := by
    intro c hc
    interval_cases c
    exacts [q82c0, q82c1, q82c2]
  have h := allN_spec (hc (a / 16) (by omega)) (a % 16) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 16 (a / 16)) (a % 16) = a := Nat.div_add_mod a 16
  rw [e] at h
  exact h

theorem cnt01 : ((List.range 4096).filter (noWit BD.W0 0)).length ≤ 8 := by
  rw [← cntN_eq]
  exact Nat.le_of_ble_eq_true kC01

theorem cnt04 : ((List.range 4096).filter (noWit BD.W0 10)).length ≤ 1184 := by
  rw [← cntN_eq]
  exact Nat.le_of_ble_eq_true kC04

theorem cnt11 : ((List.range 27).filter (noWit BD.W1 0)).length ≤ 1 := by
  rw [← cntN_eq]
  exact Nat.le_of_ble_eq_true kC11

theorem cnt14 : ((List.range 27).filter (noWit BD.W1 10)).length ≤ 19 := by
  rw [← cntN_eq]
  exact Nat.le_of_ble_eq_true kC14

theorem cntCen :
    ((List.range 4608).filter (fun i => Nat.beq fld(BD.CR i, 0, 1) 1)).length ≤ 8 := by
  rw [← cntN_eq]
  exact Nat.le_of_ble_eq_true kCen

end CertificateChecks.KernelOm2

end
