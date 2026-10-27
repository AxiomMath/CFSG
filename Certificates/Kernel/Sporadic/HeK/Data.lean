module

public import Certificates.Kernel.Sporadic.OddCore.TBfsCmd
public import Certificates.Kernel.Sporadic.OddCore.RowsCmd
public import CFSG.Certificates.Kernel.Spor.PackWord
public import Certificates.Data.CFSGNative.He.Certificate
public meta import Certificates.Data.CFSGNative.He.Certificate

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.HeK

open CFSG.Sporadic.He.Native CFSG.Perm.Native CFSG.Sporadic.Th.Native

meta def orbM : VOrbit := orbitData ()

meta def laneRow (v : Array Nat) : Nat :=
  ((List.range v.size).map fun j => v[j]! <<< (12 * j)).foldl (· ||| ·) 0

meta def laneMat (M : Array (Array Nat)) : Nat :=
  ((List.range M.size).map fun i => laneRow M[i]! <<< (600 * i)).foldl (· ||| ·) 0

meta def qM : Array (Array Nat) := colsMat 50 orbM.keys
meta def yM : Array (Array Nat) := invM 7 50 qM

meta def matsM : List Nat := [laneMat qM, laneMat yM]

meta def lettersM : Array Table := chainLetters orbM
meta def ltM : Array Nat := (lettersM.map fun t => t.map (·.toNat)).flatten
meta def lv0M : Array Nat := levelLetters lettersM chainBase 0
meta def lv1M : Array Nat := levelLetters lettersM chainBase 1
meta def lv2M : Array Nat := levelLetters lettersM chainBase 2
meta def lv3M : Array Nat := levelLetters lettersM chainBase 3
meta def lv4M : Array Nat := levelLetters lettersM chainBase 4
meta def lblM : Array Nat := labelsOf (subTrees lettersM lv1M)

end CertificateChecks.KernelSpor.HeK

#knatlist CertificateChecks.KernelSpor.HeK.MATS CertificateChecks.KernelSpor.HeK.matsM
#krows CertificateChecks.KernelSpor.HeK.LT CertificateChecks.KernelSpor.HeK.ltM
#krows CertificateChecks.KernelSpor.HeK.LBL CertificateChecks.KernelSpor.HeK.lblM

#ktbfs CertificateChecks.KernelSpor.HeK.CT0 8330 0 CertificateChecks.KernelSpor.HeK.lettersM
  CertificateChecks.KernelSpor.HeK.lv0M
#ktbfs CertificateChecks.KernelSpor.HeK.CT1 8330 1 CertificateChecks.KernelSpor.HeK.lettersM
  CertificateChecks.KernelSpor.HeK.lv1M
#ktbfs CertificateChecks.KernelSpor.HeK.CT2 8330 3 CertificateChecks.KernelSpor.HeK.lettersM
  CertificateChecks.KernelSpor.HeK.lv2M
#ktbfs CertificateChecks.KernelSpor.HeK.CT3 8330 4 CertificateChecks.KernelSpor.HeK.lettersM
  CertificateChecks.KernelSpor.HeK.lv3M
#ktbfs CertificateChecks.KernelSpor.HeK.CT4 8330 2 CertificateChecks.KernelSpor.HeK.lettersM
  CertificateChecks.KernelSpor.HeK.lv4M

#ktbfs CertificateChecks.KernelSpor.HeK.SB0 8330 0 CertificateChecks.KernelSpor.HeK.lettersM
  CertificateChecks.KernelSpor.HeK.lv1M
#ktbfs CertificateChecks.KernelSpor.HeK.SB1 8330 1 CertificateChecks.KernelSpor.HeK.lettersM
  CertificateChecks.KernelSpor.HeK.lv1M
#ktbfs CertificateChecks.KernelSpor.HeK.SB2 8330 6 CertificateChecks.KernelSpor.HeK.lettersM
  CertificateChecks.KernelSpor.HeK.lv1M
#ktbfs CertificateChecks.KernelSpor.HeK.SB3 8330 21 CertificateChecks.KernelSpor.HeK.lettersM
  CertificateChecks.KernelSpor.HeK.lv1M
#ktbfs CertificateChecks.KernelSpor.HeK.SB4 8330 24 CertificateChecks.KernelSpor.HeK.lettersM
  CertificateChecks.KernelSpor.HeK.lv1M
#ktbfs CertificateChecks.KernelSpor.HeK.SB5 8330 33 CertificateChecks.KernelSpor.HeK.lettersM
  CertificateChecks.KernelSpor.HeK.lv1M
#ktbfs CertificateChecks.KernelSpor.HeK.SB6 8330 368 CertificateChecks.KernelSpor.HeK.lettersM
  CertificateChecks.KernelSpor.HeK.lv1M

end
