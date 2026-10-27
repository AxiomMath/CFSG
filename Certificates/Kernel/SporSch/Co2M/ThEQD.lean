
module

public import Certificates.Kernel.Sporadic.RawGenSplitP
public import CFSG.Sporadic.Co2Schreier.ThirdCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.ThirdCheckInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Co2Cert

meta def thQPis : Array (Array Nat) :=
  let gA := gArrsOf co2PosTable witRec
  conjPis gA 1024 (leftEnum (quArrsOf gA) 1024)

meta def thQS : Array (Array Nat) := extendArrsN 1024 thQPis quDerivs

meta def thQB : Array Nat := #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

end CertificateChecks.KernelSporSch.Co2M

#ks_rawchain_sl2_data CertificateChecks.KernelSporSch.Co2EQ 1024 11 16 128
  CertificateChecks.KernelSporSch.Co2M.thQS CertificateChecks.KernelSporSch.Co2M.thQB 15
  CFSG.Sporadic.Co2Schreier.quDerivs

#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2EQ 0 0 8
#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2EQ 1 0 8
#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2EQ 2 0 8
#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2EQ 3 0 8
#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2EQ 4 0 8
#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2EQ 5 0 8
#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2EQ 6 0 8
#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2EQ 7 0 8
#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2EQ 8 0 8
#ks_rawchain_sl2_lvpCertificateChecks.KernelSporSch.Co2EQ 9 0 8
