module

public import CFSG.Certificates.Kernel.LyS0.Sound
public import Certificates.Kernel.LyS0.Checks
public import Certificates.Kernel.LyS0.Gens
public import Certificates.Kernel.LyS0.Slices0
public import Certificates.Kernel.LyS0.Slices1
public import Certificates.Kernel.LyS0.Slices2
public import Certificates.Kernel.LyS0.Slices3
public import Certificates.Kernel.LyS0.Slices4
public import Certificates.Kernel.LyS0.Slices5
public import Certificates.Kernel.LyS0.Slices6
public import Certificates.Kernel.LyS0.Slices7
public import Certificates.Kernel.LyS0.Slices8
public import Certificates.Kernel.SporSch.Ly.BS18009
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelLyS0

open CFSG.KD.LyS0

theorem leftAll : ∀ q < 27, leftK GI T (81 * q) 81 = true := by
  intro q hq
  interval_cases q
  exacts [leftC0, leftC1, leftC2, leftC3, leftC4, leftC5, leftC6, leftC7, leftC8, leftC9,
    leftC10, leftC11, leftC12, leftC13, leftC14, leftC15, leftC16, leftC17, leftC18, leftC19,
    leftC20, leftC21, leftC22, leftC23, leftC24, leftC25, leftC26]

theorem sortAll : ∀ q < 27, sortK GI T (81 * q) 81 = true := by
  intro q hq
  interval_cases q
  exacts [sortC0, sortC1, sortC2, sortC3, sortC4, sortC5, sortC6, sortC7, sortC8, sortC9,
    sortC10, sortC11, sortC12, sortC13, sortC14, sortC15, sortC16, sortC17, sortC18, sortC19,
    sortC20, sortC21, sortC22, sortC23, sortC24, sortC25, sortC26]

theorem lyS0Check_true : CFSG.Sporadic.Ly.S0.lyS0Check () = true :=
  CFSG.KS.LyS0K.lyS0Check_of OS.eq PS.eq LS.eq pOps pPar pL shape opsB
    CertificateChecks.KernelSporSch.LyBSF.matA_eq CertificateChecks.KernelSporSch.LyBSF.matB_eq
    CertificateChecks.KernelSporSch.LyBS.vA CertificateChecks.KernelSporSch.LyBS.vB gensC
    leftAll sortAll kill

end CertificateChecks.KernelLyS0

end
