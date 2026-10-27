module

public import Certificates.Kernel.ReflExt.Checks708608
public import CFSG.Certificates.Kernel.ReflExt.MovKSound
import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.Certificates.Kernel.ReflExt.DepKSound
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallRankDefs

namespace CFSG.KD.MK708608

#kc_forall_chunks all608 (fun k => CFSG.KD.MK708608.cd k = true) 16 CFSG.KD.MK708608.ch708608.f_ 1

open CFSG.DepFrame CFSG.ReflExt.MK

public section

theorem e6dep_frame : ∃ T, verifyAllM (e6DepPt ()) T = true :=
  partM_verify _ f0 fun i hi => all608 i hi

end

end CFSG.KD.MK708608
