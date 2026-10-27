module

public import Certificates.Kernel.Misc.Perm.M12HypData
public import CFSG.Certificates.Kernel.Misc.PermM12HypSound
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.M12Hyp

open CFSG.GH74.M12.Hyp CFSG.KC.Misc.M12Hyp

theorem valid : validL (HT ++ QT ++ Q1T ++ Q2T ++ BT ++ gensT ++ [JT, ET, NT, FT, XT]) = true := by
  quickRfl

theorem hH : HT.map encT = Hc := by decide +kernel
theorem hQ : QT.map encT = Qc := by decide +kernel
theorem h1 : Q1T.map encT = Q1c := by decide +kernel
theorem h2 : Q2T.map encT = Q2c := by decide +kernel
theorem hB : BT.map encT = Bc := by decide +kernel
theorem hG : gensT.map encT = Gc := by decide +kernel
theorem hJ : encT JT = Jc := by decide +kernel
theorem hE : encT ET = Ec := by decide +kernel
theorem hN : encT NT = Nc := by decide +kernel
theorem hF : encT FT = Fc := by decide +kernel
theorem hX : encT XT = Xc := by decide +kernel

theorem check : c5135 Hc Qc Q1c Q2c Bc Gc Jc Ec Nc Fc Xc = true := by quickRfl

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.M12 in
open CFSG.GH74.M12.Hyp in
theorem facts : ((∀ g ∈ gensT, tmul JT g = tmul g JT) ∧
    (HT.length = 192) ∧
    (HT.Nodup) ∧
    (JT ∈ HT))
    ∧ ((∀ a0 ∈ List.range 4, ∀ a1 ∈ List.range 4, ∀ a2 ∈ List.range 4,
         ∀ a3 ∈ List.range 4, ∀ a4 ∈ List.range 12, a0 ≠ a1 → a0 ≠ a2 → a0 ≠ a3 → a1 ≠ a2 →
           a1 ≠ a3 → a2 ≠ a3 → 4 ≤ a4 → ∃ t ∈ HT, t.take 5 = [a0, a1, a2, a3, a4]))
    ∧ ((∀ t ∈ HT, (∀ s ∈ HT, tmul t s = tmul s t) → t = tid ∨ t = JT) ∧
    (∃ c ∈ HT, ∃ d ∈ HT, tcomm c d ≠ tid) ∧
    (QT.length = 32) ∧
    (tid ∈ QT) ∧
    (JT ∈ QT) ∧
    (∀ s ∈ QT, ∀ t ∈ QT, tmul s t ∈ QT))
    ∧ ((∀ s ∈ QT, tinv s ∈ QT) ∧
    (∀ c ∈ HT, ∀ q ∈ QT, tmul (tmul c q) (tinv c) ∈ QT) ∧
    (∀ s ∈ QT, ((∀ t ∈ QT, tmul s t = tmul t s) ↔ (s = tid ∨ s = JT))) ∧
    (∀ s ∈ QT, ∀ t ∈ QT, tcomm s t = tid ∨ tcomm s t = JT) ∧
    (∀ s ∈ QT, tmul s s = tid ∨ tmul s s = JT) ∧
    (∃ s ∈ QT, s ≠ tid ∧ s ≠ JT))
    ∧ ((∃ c ∈ HT, ∃ d ∈ HT, tcomm c d ∉ QT) ∧
    (∀ x ∈ HT, tmul x (tmul x x) = tid → x ≠ tid →
         ∀ q ∈ QT, tmul q x = tmul x q → q = tid ∨ q = JT) ∧
    (XT ∈ QT) ∧
    (XT ≠ JT) ∧
    (Q1T.length = 8) ∧
    (Q2T.length = 8))
    ∧ ((Q1T.Nodup) ∧
    (Q2T.Nodup) ∧
    (∀ t ∈ Q1T, t ∈ QT) ∧
    (∀ t ∈ Q2T, t ∈ QT) ∧
    (tid ∈ Q1T) ∧
    (tid ∈ Q2T))
    ∧ ((∀ s ∈ Q1T, ∀ t ∈ Q1T, tmul s t ∈ Q1T) ∧
    (∀ s ∈ Q2T, ∀ t ∈ Q2T, tmul s t ∈ Q2T) ∧
    (∀ s ∈ Q1T, tinv s ∈ Q1T) ∧
    (∀ s ∈ Q2T, tinv s ∈ Q2T) ∧
    (∀ c ∈ HT, ∀ q ∈ Q1T, tmul (tmul c q) (tinv c) ∈ Q1T) ∧
    (∀ c ∈ HT, ∀ q ∈ Q2T, tmul (tmul c q) (tinv c) ∈ Q2T))
    ∧ ((∀ x ∈ QT, ∀ y ∈ QT, tpow x 4 = tid → tpow x 2 ≠ tid →
         tmul y y = tpow x 2 → tmul y x = tmul (tpow x 3) y →
           (x ∈ Q1T ∧ y ∈ Q1T) ∨ (x ∈ Q2T ∧ y ∈ Q2T)))
    ∧ ((BT.length = 64) ∧
    (BT.Nodup) ∧
    (tid ∈ BT) ∧
    (∀ s ∈ BT, ∀ t ∈ BT, tmul s t ∈ BT) ∧
    (∀ s ∈ BT, tinv s ∈ BT) ∧
    (∀ t ∈ BT, t ∈ HT))
    ∧ ((ET ∈ BT) ∧
    (NT ∈ BT) ∧
    (FT ∈ BT) ∧
    (JT ∈ BT) ∧
    (XT ∈ BT) ∧
    (∀ s ∈ BT, (∀ t ∈ BT, tmul s t = tmul t s) →
         tmul s s = tid → s ≠ tid → s = JT)) :=
  s5135 valid hH hQ h1 h2 hB hG hJ hE hN hF hX check

end CertificateChecks.KernelMisc.M12Hyp

end
