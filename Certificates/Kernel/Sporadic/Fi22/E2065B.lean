module

public import CFSG.Certificates.Kernel.Common.TextPiecesD
public import CFSG.Sporadic.FischerOddCore.Fi22CentData
public import CFSG.Sporadic.FischerOddCore.Fi22CentText

public section

#text_pieces_d CertificateChecks.KernelSpor.Fi22CentB.W CFSG.Sporadic.FischerOddCore.fi22Cent3510Text "Certificates/Data/CFSGNative/FischerOddCore/fi22-cent-3510.txt" 3222486 309226541713237166 0 2048 4000000 8192
#text_pieces_d CertificateChecks.KernelSpor.Fi22CentB.Q0 CFSG.Sporadic.FischerOddCore.fi22CentP0 "Certificates/Data/Kernel/Fi22/fi22-cent-3510-p0.txt" 810887 9724557547445411205 0 2048 1000000 2048
#text_pieces_d CertificateChecks.KernelSpor.Fi22CentB.Q1 CFSG.Sporadic.FischerOddCore.fi22CentP1 "Certificates/Data/Kernel/Fi22/fi22-cent-3510-p1.txt" 810887 14092615126009996223 121 2048 1000000 2048
#text_pieces_d CertificateChecks.KernelSpor.Fi22CentB.Q2 CFSG.Sporadic.FischerOddCore.fi22CentP2 "Certificates/Data/Kernel/Fi22/fi22-cent-3510-p2.txt" 800356 3359070508892811279 242 2048 1000000 2048
#text_pieces_d CertificateChecks.KernelSpor.Fi22CentB.Q3 CFSG.Sporadic.FischerOddCore.fi22CentP3 "Certificates/Data/Kernel/Fi22/fi22-cent-3510-p3.txt" 800356 16387478421017533484 654 2048 1000000 2048

namespace CertificateChecks.KernelSpor.Fi22CentB

open CFSG.KC.YModel

theorem split0 : (W.CH == Q0.CH.dropLast ++ W.CH.getD 395 (0, 0) :: W.CH.drop 396) = true := by
  decide +kernel

theorem split1 : (Q1.CH.headD (0, 0) :: W.CH.drop 396 ==
    Q1.CH.dropLast ++ W.CH.getD 791 (0, 0) :: W.CH.drop 792) = true := by
  decide +kernel

theorem split2 : (Q2.CH.headD (0, 0) :: W.CH.drop 792 ==
    Q2.CH.dropLast ++ W.CH.getD 1182 (0, 0) :: W.CH.drop 1183) = true := by
  decide +kernel

theorem split3 : (Q3.CH.headD (0, 0) :: W.CH.drop 1183 == Q3.CH) = true := by
  decide +kernel

theorem last0 : (Q0.CH == Q0.CH.dropLast ++ [Q0.CH.getLastD (0, 0)]) = true := by decide +kernel
theorem last1 : (Q1.CH == Q1.CH.dropLast ++ [Q1.CH.getLastD (0, 0)]) = true := by decide +kernel
theorem last2 : (Q2.CH == Q2.CH.dropLast ++ [Q2.CH.getLastD (0, 0)]) = true := by decide +kernel

theorem join1 : (charsOf [W.CH.getD 395 (0, 0)] ==
    charsOf [Q0.CH.getLastD (0, 0), Q1.CH.headD (0, 0)]) = true := by decide +kernel
theorem join2 : (charsOf [W.CH.getD 791 (0, 0)] ==
    charsOf [Q1.CH.getLastD (0, 0), Q2.CH.headD (0, 0)]) = true := by decide +kernel
theorem join3 : (charsOf [W.CH.getD 1182 (0, 0)] ==
    charsOf [Q2.CH.getLastD (0, 0), Q3.CH.headD (0, 0)]) = true := by decide +kernel

end CertificateChecks.KernelSpor.Fi22CentB

end
