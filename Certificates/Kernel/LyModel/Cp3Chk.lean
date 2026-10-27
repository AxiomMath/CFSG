module

public import Certificates.Kernel.LyModel.Cp3Data
public import Certificates.Kernel.LyModel.Cp3Net

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelLyModel

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.LyBenes CFSG.KC.LyDce CFSG.KC.LyModel
  CFSG.KC.LyGlue CFSG.Sporadic.Recognition.LyonsSims CertificateChecks.KernelLyB
  CertificateChecks.KernelLyDce

theorem ly6110_cp3yC : yC = Ly0.wordY.map lcode := by decide +kernel

theorem ly6110_cp3gC : gC = Ly0.wordConj.map lcode := by decide +kernel

theorem ly6110_cp3uC : uC = Ly0.uWords.map fun w => w.map lcode := by decide +kernel

theorem ly6110_cp3orb : orbAll = true := by decide +kernel

theorem ly6110_cp3validY : netValid 17 NY0 = true := by decide +kernel

theorem ly6110_cp3netY : planesEq 17 (genNets NS Ly0.wordY) NY0 = true := by decide +kernel

theorem ly6110_cp3fix : fixM NY0 (maskOf o0) = true := by decide +kernel

end CertificateChecks.KernelLyModel

end
