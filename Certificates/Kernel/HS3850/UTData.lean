module

public import Certificates.Kernel.SporSch.Th.GenV4
public import Certificates.Data.SmithB45ExcHSData
meta import Certificates.Data.SmithB45ExcHSData

public section

namespace CertificateChecks.KernelHS3850.UT

open CFSG.Quasithin.B45Exc.HS CFSG.Quasithin.B45Exc.Tab CFSG.QuasithinUnique.Setup.X1

meta def inv : List Nat := sylInv 3850 1024 hsSylAl

meta def cm : List Nat := (List.range hsUTab.m).map fun i =>
  (List.range hsUTab.m).foldl (fun acc j => if hsUTab.commAt i j then acc ||| (1 <<< j) else acc) 0

meta def pr : List Nat := (List.range hsUTab.m).map fun i =>
  (List.range hsUTab.m).foldl (fun acc j => acc ||| (hsUTab.prodAt i j <<< (8 * j))) 0

meta def fx : List Nat := hsUFix.toList

end CertificateChecks.KernelHS3850.UT

end

set_option maxRecDepth 400000

#kss_natlist CertificateChecks.KernelHS3850.UT.INV CertificateChecks.KernelHS3850.UT.inv
#kss_natlist CertificateChecks.KernelHS3850.UT.CM CertificateChecks.KernelHS3850.UT.cm
#kss_natlist CertificateChecks.KernelHS3850.UT.PR CertificateChecks.KernelHS3850.UT.pr
#kss_natlist CertificateChecks.KernelHS3850.UT.FX CertificateChecks.KernelHS3850.UT.fx
