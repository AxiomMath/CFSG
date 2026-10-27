module

public import Certificates.Kernel.SporSch.Tits.Inv2266D
public import Certificates.Data.Kernel.SporSch.TitsCnt
public import Certificates.Data.SmithB42TitsDisp
public import Certificates.Kernel.EvenBN.K27580D
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option trace.profiler true
set_option trace.profiler.threshold 1000

namespace CertificateChecks.KernelSporSch.TitsDisp

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch
open CFSG.Sporadic.Schreier.Tits CFSG.Quasithin.B42Tits
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.TitsAbel

@[expose] noncomputable def okV (wd : List Int) : Bool :=
  bAnd(wordEqK 1755 11 (mask 11) (pidn 1755 11) TitsD.S TitsD.SI 13 wd (wK wd),
  bAnd(canonK 1755 11 (mask 11) (1755 * 11) (wK wd),
  bAnd(canonK 1755 11 (mask 11) (1755 * 11) (pinv (wK wd)),
    permOK 1755 11 (mask 11) (1755 * 11) (wK wd) (pinv (wK wd)))))

@[expose] noncomputable def cj (wd : List Int) (x : Nat) : Nat := pc (pc (wK wd) x) (pinv (wK wd))

@[expose] noncomputable def ctK : Nat := pc TitsT (cj titsWordT TitsT)

@[expose] noncomputable def czK : Nat := pc (pc TitsZ (cj titsWordZ₂ TitsZ)) (cj titsWordZ₃ TitsZ)

@[expose] noncomputable def commS (a b : Nat) : Bool := baseComm TitsS.BP 5 (pgR a) (pgR b)

@[expose] noncomputable def colK (col : List Nat) : Bool :=
  allN 143 fun i => allN 143 fun j =>
    i == j || col[i]! != col[j]! || !commS TitsIC[i]! TitsIC[j]!

@[expose] noncomputable def zOut (p : Nat) : Bool :=
  allN 143 fun k => !titsInvCert[k]!.1 || !Nat.beq p TitsIC[k]!

@[expose] noncomputable def colAK (col : List Nat) : Bool :=
  allN 143 fun i => allN 143 fun j =>
    !(titsInvCert[i]!.1 && titsInvCert[j]!.1) || i == j || col[i]! != col[j]! ||
      !commS TitsIC[i]! TitsIC[j]! || zOut (pc TitsIC[i]! TitsIC[j]!)

theorem kVT : okV titsWordT = true := by
  unfold okV wordEqK
  quickRfl
theorem kVZ2 : okV titsWordZ₂ = true := by
  unfold okV wordEqK
  quickRfl
theorem kVZ3 : okV titsWordZ₃ = true := by
  unfold okV wordEqK
  quickRfl
theorem kLT : lettersK 13 titsWordT = true := by quickRfl
theorem kLZ2 : lettersK 13 titsWordZ₂ = true := by quickRfl
theorem kLZ3 : lettersK 13 titsWordZ₃ = true := by quickRfl

theorem kCtNe : neIdK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) ctK = true := by quickRfl
theorem kCt13 : Nat.beq (pw ctK 13) (pidn 1755 11) = true := by quickRfl
theorem kCzNe : neIdK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) czK = true := by quickRfl
theorem kCz13 : Nat.beq (pw czK 13) (pidn 1755 11) = true := by quickRfl

theorem kLen : Nat.beq TitsIC.length 143 = true := by quickRfl
theorem kInS : allL (fun y => memN y CertificateChecks.KernelEvenBN.E32.SI.L) TitsIC = true := by
  quickRfl

theorem kCol : colK titsInvColour = true := by quickRfl
theorem kColA : colAK titsInvColourA = true := by quickRfl

end CertificateChecks.KernelSporSch.TitsDisp

end
