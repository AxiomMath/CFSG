module

public import CFSG.Certificates.Kernel.LocalQTSecSound
import Certificates.Kernel.LocalQT.Cmd
import all CFSG.Blueprint.NativeSporadic
meta import Certificates.Data.CFSGNative.SectionRank.McL
public import CFSG.Open.Defs

set_option maxRecDepth 100000

#lqt_sr_elem CFSG.KD.LQT.McL CFSG.SectionRank.Native.mclData 3 21
  CFSG.Blueprint.NativeSporadic.McLSeed1 CFSG.Blueprint.NativeSporadic.McLSeed2

public section

namespace CertificateChecks.KernelLocalQT

open CFSG.Blueprint CFSG.Open CFSG.KC.LQT

theorem mcl_elem : ∃ E : Subgroup NativeSporadic.McL, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 := by
  have h := elem_sound _ CFSG.KD.LQT.McL.lay_ok CFSG.KD.LQT.McL.decA CFSG.KD.LQT.McL.decB
    CFSG.KD.LQT.McL.one CFSG.KD.LQT.McL.steps CFSG.KD.LQT.McL.elem
  rw [← CFSG.KD.LQT.McL.LA_eq, ← CFSG.KD.LQT.McL.LB_eq] at h
  exact h

end CertificateChecks.KernelLocalQT

end
