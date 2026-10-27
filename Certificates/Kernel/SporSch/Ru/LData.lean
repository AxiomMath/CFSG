module

public import Certificates.Kernel.SporSch.Ru.WitData
public import CFSG.Sporadic.Schreier.RuCheckLInputs
meta import CFSG.Sporadic.Schreier.RuCheckLInputs

public section

namespace CertificateChecks.KernelSporSch.RuLD

open CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native

meta def primesM : Array Nat := #[5, 7, 13]

meta def yM : Array (Array Nat) := primesM.map ruYpA

meta def x1M : Array (Array Nat) := yM.map (compA 4060 ruLGensA[2]!)

meta def x2M : Array (Array Nat) := x1M.map fun x => compA 4060 x (ruInv ruLGensA[2]!)

meta def x3M : Array (Array Nat) := (Array.range 3).map fun i => compA 4060 yM[i]! x2M[i]!

meta def qM : Array (Array Nat) :=
  (Array.range 42).map fun j => powA 4060 x3M[j / 14]! (35 * (j % 14))

meta def wM : Array (Array Nat) :=
  (Array.range 27).map fun j => powA 4060 (ruVpA primesM[j / 9]!) (32 * (j % 9))

end CertificateChecks.KernelSporSch.RuLD

#kss_perms CertificateChecks.KernelSporSch.RuLD.YT 12 CertificateChecks.KernelSporSch.RuLD.yM
#kss_perms CertificateChecks.KernelSporSch.RuLD.X1T 12 CertificateChecks.KernelSporSch.RuLD.x1M
#kss_perms CertificateChecks.KernelSporSch.RuLD.X2T 12 CertificateChecks.KernelSporSch.RuLD.x2M
#kss_perms CertificateChecks.KernelSporSch.RuLD.X3T 12 CertificateChecks.KernelSporSch.RuLD.x3M
#kss_perms CertificateChecks.KernelSporSch.RuLD.QT 12 CertificateChecks.KernelSporSch.RuLD.qM
#kss_perms CertificateChecks.KernelSporSch.RuLD.WT 12 CertificateChecks.KernelSporSch.RuLD.wM

end
