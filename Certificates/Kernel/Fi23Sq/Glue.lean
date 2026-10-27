module

public import Certificates.Kernel.Fi23Sq.Sound
import Certificates.Kernel.Fi23Sq.L0
import Certificates.Kernel.Fi23Sq.L1
import Certificates.Kernel.Fi23Sq.Misc

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23Sq

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23R CFSG.KC.Fi23S CFSG.KD.Fi23K CFSG.KD.Fi23S
  CFSG.KD.Fi23Sq CFSG.KS.PEnum CFSG.KS.Raw.Orb CFSG.Sporadic.Fi23 CFSG.Sporadic.Fi23.Native
  CertificateChecks.KernelFi23S CFSG.EvenSporadicStandard.TwoFi22

theorem lSqF_all24650 : ∀ s < 16, lSqF s = true := by
  intro s hs
  interval_cases s
  exacts [sq24650L0, sq24650L1, sq24650L2, sq24650L3, sq24650L4, sq24650L5, sq24650L6, sq24650L7,
    sq24650L8, sq24650L9, sq24650L10, sq24650L11, sq24650L12, sq24650L13, sq24650L14, sq24650L15]

theorem lSqB_cover24650 : ∀ k < 512, ∃ s < 16, List.getD lSqB s 0 ≤ k ∧
    k < List.getD lSqB (s + 1) 0 := by
  decide

theorem lfSq_all24650 : ∀ k < 512, ∀ j < 512, lfSq k j = true := by
  intro k hk j hj
  obtain ⟨s, hs, h1, h2⟩ := lSqB_cover24650 k hk
  have h := lSqF_all24650 s hs
  unfold lSqF at h
  rw [strictB_eq] at h
  unfold lSqSl at h
  have h' := allN_iff.1 h (k - List.getD lSqB s 0) (by
    change k - List.getD lSqB s 0 < List.getD lSqB (s + 1) 0 - List.getD lSqB s 0
    omega)
  rw [strictB_eq] at h'
  have e : Nat.add (List.getD lSqB s 0) (k - List.getD lSqB s 0) = k := by
    change List.getD lSqB s 0 + (k - List.getD lSqB s 0) = k
    omega
  rw [e] at h'
  exact allN_iff.1 h' j hj

theorem sqStatement24650 :
    SqStatement D23 d :=
  sqStatement24650_of sq24650M lfSq_all24650

end CertificateChecks.KernelFi23Sq

end
