module

public import Certificates.Kernel.RootOrbit.Checks
public import CFSG.Certificates.Kernel.RootOrbit.Sound

public section

open CFSG.KC.RootOrbit CFSG.HardMathSupport.Timmesfeld.RootAut

namespace CertificateChecks.KernelRootOrbit

theorem orbitOK_A2 : orbitOK (CartanMatrix.A 2) 6 30 = true := orbitOK_of_rootCertB rowsA2 certA2
theorem orbitOK_A3 : orbitOK (CartanMatrix.A 3) 12 30 = true := orbitOK_of_rootCertB rowsA3 certA3
theorem orbitOK_A4 : orbitOK (CartanMatrix.A 4) 20 30 = true := orbitOK_of_rootCertB rowsA4 certA4
theorem orbitOK_A5 : orbitOK (CartanMatrix.A 5) 30 30 = true := orbitOK_of_rootCertB rowsA5 certA5
theorem orbitOK_A6 : orbitOK (CartanMatrix.A 6) 42 30 = true := orbitOK_of_rootCertB rowsA6 certA6
theorem orbitOK_A7 : orbitOK (CartanMatrix.A 7) 56 30 = true := orbitOK_of_rootCertB rowsA7 certA7
theorem orbitOK_A8 : orbitOK (CartanMatrix.A 8) 72 30 = true := orbitOK_of_rootCertB rowsA8 certA8
theorem orbitOK_D4 : orbitOK (CartanMatrix.D 4) 24 30 = true := orbitOK_of_rootCertB rowsD4 certD4
theorem orbitOK_D5 : orbitOK (CartanMatrix.D 5) 40 30 = true := orbitOK_of_rootCertB rowsD5 certD5
theorem orbitOK_D6 : orbitOK (CartanMatrix.D 6) 60 30 = true := orbitOK_of_rootCertB rowsD6 certD6
theorem orbitOK_D7 : orbitOK (CartanMatrix.D 7) 84 30 = true := orbitOK_of_rootCertB rowsD7 certD7
theorem orbitOK_D8 : orbitOK (CartanMatrix.D 8) 112 30 = true :=
  orbitOK_of_rootCertB rowsD8 certD8
theorem orbitOK_E6 : orbitOK (CartanMatrix.E 6) 72 30 = true := orbitOK_of_rootCertB rowsE6 certE6

end CertificateChecks.KernelRootOrbit
