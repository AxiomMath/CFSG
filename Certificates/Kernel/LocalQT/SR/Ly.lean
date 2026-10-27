module

public import CFSG.Certificates.Kernel.LocalQTSecSound
import Certificates.Kernel.LocalQT.Cmd
import all CFSG.Blueprint.NativeSporadic
meta import Certificates.Data.CFSGNative.SectionRank.Ly
public import CFSG.Open.Defs

set_option maxRecDepth 100000

#lqt_sr_elem CFSG.KD.LQT.Ly CFSG.SectionRank.Native.lyData 5 111
  CFSG.Blueprint.NativeSporadic.LySeed1 CFSG.Blueprint.NativeSporadic.LySeed2

public section

namespace CertificateChecks.KernelLocalQT

open CFSG.Blueprint CFSG.Open CFSG.KC.LQT

theorem ly_elem : ∃ E : Subgroup NativeSporadic.Ly, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 := by
  have h := elem_sound _ CFSG.KD.LQT.Ly.lay_ok CFSG.KD.LQT.Ly.decA CFSG.KD.LQT.Ly.decB
    CFSG.KD.LQT.Ly.one CFSG.KD.LQT.Ly.steps CFSG.KD.LQT.Ly.elem
  rw [← CFSG.KD.LQT.Ly.LA_eq, ← CFSG.KD.LQT.Ly.LB_eq] at h
  exact h

end CertificateChecks.KernelLocalQT

end
