module

public import Certificates.Kernel.MinusQuandle.Data
public import Certificates.Data.Kernel.MinusRealize
import all CFSG.OddTranspositions.PartThree.Eleven.Minus.RealizeCheck

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelMinusRZ

open CFSG.KD.MinusRealize CFSG.KD.MinusQuandle CertificateChecks.KernelMinusQ

theorem pin_t : force (pk true) (fun P => pinOK true P) = true := by decide +kernel

theorem sign_t : force (pk true) (fun P => signOK true P) = true := by decide +kernel

theorem table_t : force (pk true) (fun P => tableOK R P) = true := by decide +kernel

theorem cover_t : force (pk true) (fun P => coverOK true P) = true := by decide +kernel

theorem pin_f : force (pk false) (fun P => pinOK false P) = true := by decide +kernel

theorem sign_f : force (pk false) (fun P => signOK false P) = true := by decide +kernel

theorem table_f : force (pk false) (fun P => tableOK R P) = true := by decide +kernel

theorem cover_f : force (pk false) (fun P => coverOK false P) = true := by decide +kernel

end CertificateChecks.KernelMinusRZ
