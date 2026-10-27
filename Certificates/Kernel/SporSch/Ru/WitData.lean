module

public import Certificates.Kernel.SporSch.Ru.GensData
public import CFSG.Sporadic.Schreier.RuWitArrays
meta import CFSG.Sporadic.Schreier.RuWitArrays
meta import Certificates.Kernel.SporSch.Ru.GensData

public section

namespace CertificateChecks.KernelSporSch.RuW

open CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native CertificateChecks.KernelSporSch.RuG

meta def valsMM : Array (Array Nat) := valsM ruMProg ruA0A ruA1A

meta def m1iM : Array Nat := ruInv ruM1A

meta def m2iM : Array Nat := ruInv ruM2A

meta def rwPM : Array (Array Nat) := (Array.range 7).map fun q => ruMWordA (ruRMWord.drop (10 * q))

meta def wwiM : Array Nat := ruInv ruWwA

meta def wrM : Array Nat := compA 4060 ruWwA ruRwA

meta def wrwiM : Array Nat := compA 4060 wrM (ruInv ruWwA)

meta def u7M : Array Nat := powA 4060 ruUwA 7

meta def hwiM : Array Nat := ruInv ruHwA

meta def lmM : Array (Array Nat) := (ruLMWords.map ruMWordA).toArray

meta def hlmM : Array (Array Nat) := lmM.map (compA 4060 ruHwA)

meta def lgiM : Array (Array Nat) := ruLGensA.map ruInv

meta def fgM : Array (Array Nat) := #[ruFusGA 1, ruFusGA 2, ruFusGA 3]

meta def fgiM : Array (Array Nat) := fgM.map ruInv

end CertificateChecks.KernelSporSch.RuW

#kss_perms CertificateChecks.KernelSporSch.RuW.VM 12 CertificateChecks.KernelSporSch.RuW.valsMM
#ks_perm CertificateChecks.KernelSporSch.RuW.M1 12 CFSG.Sporadic.RuSchreier.ruM1A
#ks_perm CertificateChecks.KernelSporSch.RuW.M2 12 CFSG.Sporadic.RuSchreier.ruM2A
#ks_perm CertificateChecks.KernelSporSch.RuW.M1I 12 CertificateChecks.KernelSporSch.RuW.m1iM
#ks_perm CertificateChecks.KernelSporSch.RuW.M2I 12 CertificateChecks.KernelSporSch.RuW.m2iM
#kss_perms CertificateChecks.KernelSporSch.RuW.RwP 12 CertificateChecks.KernelSporSch.RuW.rwPM
#ks_perm CertificateChecks.KernelSporSch.RuW.Rw 12 CFSG.Sporadic.RuSchreier.ruRwA
#ks_perm CertificateChecks.KernelSporSch.RuW.Ww 12 CFSG.Sporadic.RuSchreier.ruWwA
#ks_perm CertificateChecks.KernelSporSch.RuW.WwI 12 CertificateChecks.KernelSporSch.RuW.wwiM
#ks_perm CertificateChecks.KernelSporSch.RuW.WR 12 CertificateChecks.KernelSporSch.RuW.wrM
#ks_perm CertificateChecks.KernelSporSch.RuW.WRWI 12 CertificateChecks.KernelSporSch.RuW.wrwiM
#ks_perm CertificateChecks.KernelSporSch.RuW.Uw 12 CFSG.Sporadic.RuSchreier.ruUwA
#ks_perm CertificateChecks.KernelSporSch.RuW.U7 12 CertificateChecks.KernelSporSch.RuW.u7M
#ks_perm CertificateChecks.KernelSporSch.RuW.Hw 12 CFSG.Sporadic.RuSchreier.ruHwA
#ks_perm CertificateChecks.KernelSporSch.RuW.HwI 12 CertificateChecks.KernelSporSch.RuW.hwiM
#kss_perms CertificateChecks.KernelSporSch.RuW.LM 12 CertificateChecks.KernelSporSch.RuW.lmM
#kss_perms CertificateChecks.KernelSporSch.RuW.HLM 12 CertificateChecks.KernelSporSch.RuW.hlmM
#kss_perms CertificateChecks.KernelSporSch.RuW.LG 12 CFSG.Sporadic.RuSchreier.ruLGensA
#kss_perms CertificateChecks.KernelSporSch.RuW.LGI 12 CertificateChecks.KernelSporSch.RuW.lgiM
#kss_perms CertificateChecks.KernelSporSch.RuW.FG 12 CertificateChecks.KernelSporSch.RuW.fgM
#kss_perms CertificateChecks.KernelSporSch.RuW.FGI 12 CertificateChecks.KernelSporSch.RuW.fgiM

end
