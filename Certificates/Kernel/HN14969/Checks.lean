module

public import Certificates.Kernel.HN14969.HChain
public import Certificates.Kernel.HN14969.RChain
public import Certificates.Kernel.HN14969.PChain
public import Certificates.Data.Kernel.Misc.ArrEnum
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHN14969

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.HN14969 CFSG.KC.Misc.ArrEnum HNUnitaryBridge

theorem iso_ok : ptsOK iso = true := by decide +kernel

theorem actU_ok : actOK uCode.toList iso (pg 7 (mask 7) (RC.S 0)) = true := by decide +kernel

theorem actV_ok : actOK vCode.toList iso (pg 7 (mask 7) (RC.S 1)) = true := by decide +kernel

theorem splitP0 : agreeL 50 (pg 8 (mask 8) (HC.S 0)) (pg 6 (mask 6) (PC.S 0)) = true := by
  decide +kernel

theorem splitP1 : agreeL 50 (pg 8 (mask 8) (HC.S 1)) (pg 6 (mask 6) (PC.S 1)) = true := by
  decide +kernel

theorem splitR0 : agreeL 126 (fun i => pg 8 (mask 8) (HC.S 0) (50 + i))
    (fun i => 50 + pg 7 (mask 7) (RC.S 0) i) = true := by
  decide +kernel

theorem splitR1 : agreeL 126 (fun i => pg 8 (mask 8) (HC.S 1) (50 + i))
    (fun i => 50 + pg 7 (mask 7) (RC.S 1) i) = true := by
  decide +kernel

theorem genA : isListL (pg 6 (mask 6) (PC.S 0)) sigmaAL = true := by decide +kernel

theorem genB : isListL (pg 6 (mask 6) (PC.S 1)) sigmaBL = true := by decide +kernel

theorem words_ok : wordsOKL = true := by decide +kernel

theorem permH : allN 7 (fun j => permOK 176 8 (mask 8) (176 * 8) (HC.S j) (HC.SI j)) = true := by
  quickRfl

theorem permR : allN 7 (fun j => permOK 126 7 (mask 7) (126 * 7) (RC.S j) (RC.SI j)) = true := by
  quickRfl

theorem permP : allN 9 (fun j => permOK 50 6 (mask 6) (50 * 6) (PC.S j) (PC.SI j)) = true := by
  quickRfl

theorem sizesH : (List.range 4).map (fun i => rcnt (HC.LR i)) = [126, 125, 4, 2] := by
  decide +kernel

theorem sizesR : (List.range 4).map (fun i => rcnt (RC.LR i)) = [126, 125, 4, 2] := by
  decide +kernel

theorem sizesP : (List.range 4).map (fun i => rcnt (PC.LR i)) = [50, 42, 30, 2] := by
  decide +kernel

end CertificateChecks.KernelHN14969

end
