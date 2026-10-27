module

public import Certificates.Kernel.KDenseP.MW
public import CFSG.Certificates.Kernel.KDenseP.MW.C17701

public section

namespace CertificateChecks.KernelKDenseP.MW

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.MonThreeB
  CertificateChecks.KernelKDenseP.Axis
  CFSG.Monster.AxisCount CFSG.AGLEmbedding.Norton.MON5_7 CFSG.YGroups.Y443 CFSG.YGroups.Y443Native
  CFSG.HardMathSupport.Dickson.BMRows.M11

set_option maxRecDepth 100000

theorem c17701 : m11Check () = true := by
  unfold m11Check
  exact (kd_mw% CFSG.KD.MW.c17701 m11Pairs []).1

end CertificateChecks.KernelKDenseP.MW

end
