module

public import Certificates.Kernel.ReflExt.Checks708607
public import CFSG.Certificates.Kernel.ReflExt.DepKSound
import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallRankDefs

namespace CFSG.KD.DK708607

#kc_forall_chunks all607 (fun k => CFSG.KD.DK708607.cd k = true) 21 CFSG.KD.DK708607.ch708607.f_ 1

open CFSG.DepFrame CFSG.ReflExt.DK

public section

theorem a5dep_frame : ∃ T, verifyAllD (a5DepPt ()) a5DepBstab T = true :=
  partD_verify _ _ f0 fun i hi => all607 i hi

end

end CFSG.KD.DK708607
