module

public import Certificates.Kernel.RootOrbit.Checks
public import Certificates.Kernel.RootOrbit.FoldChecks
public import CFSG.Certificates.Kernel.RootOrbit.Fold

public section

open CFSG.KC.RootOrbit CFSG.HardMathSupport.Timmesfeld.LangTorus

namespace CertificateChecks.KernelRootOrbit

theorem dGraphOK_D5 : dGraphOK (CartanMatrix.D 5) 3 4 40 = true :=
  dGraphOK_of_certs rowsD5 certD5 foldD5 orthD5 smallD5
theorem dGraphOK_D6 : dGraphOK (CartanMatrix.D 6) 4 5 60 = true :=
  dGraphOK_of_certs rowsD6 certD6 foldD6 orthD6 smallD6
theorem dGraphOK_D7 : dGraphOK (CartanMatrix.D 7) 5 6 84 = true :=
  dGraphOK_of_certs rowsD7 certD7 foldD7 orthD7 smallD7
theorem dGraphOK_D8 : dGraphOK (CartanMatrix.D 8) 6 7 112 = true :=
  dGraphOK_of_certs rowsD8 certD8 foldD8 orthD8 smallD8

end CertificateChecks.KernelRootOrbit
