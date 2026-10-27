module

public import Certificates.Data.Kernel.O8.CohK
public import Certificates.Kernel.OmegaEight.CohCertData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainModData

public section

namespace CertificateChecks.KernelO8.CohCert

open CFSG.KC.O8Coh CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Chain
open CFSG.EvenSmallLie.UnitarySix.YamadaPar (packN)

set_option maxRecDepth 100000

theorem relP : relCheck6 .plus = true := by decide +kernel
theorem relM : relCheck6 .minus = true := by decide +kernel

theorem endP_B : [packN 6 1 fun _ => id6] = endPB := by decide +kernel
theorem endM_B : [packN 6 1 fun _ => id6] = endMB := by decide +kernel
theorem modP_B : (Array.ofFn (n := 6) fun m => modSol .plus m).toList = modPB := by decide +kernel
theorem modM_B : (Array.ofFn (n := 6) fun m => modSol .minus m).toList = modMB := by decide +kernel
theorem gamP_B : (Array.ofFn (n := 6) fun m => gamSol .plus m).toList = gamPB := by decide +kernel
theorem gamM_B : (Array.ofFn (n := 6) fun m => gamSol .minus m).toList = gamMB := by decide +kernel
theorem extP_B : (Array.ofFn (n := 36) fun j => cobK gensP (2 ^ (j : Nat))).toList = extPB := by
  decide +kernel
theorem extM_B : (Array.ofFn (n := 36) fun j => cobK gensM (2 ^ (j : Nat))).toList = extMB := by
  decide +kernel

theorem endP_len : endPE.length = 36 ∧ endPB.length = 1 ∧ endPQ.length = 216 := by decide +kernel
theorem endM_len : endME.length = 36 ∧ endMB.length = 1 ∧ endMQ.length = 216 := by decide +kernel
theorem modP_len : modPE.length = 252 ∧ modPB.length = 6 ∧ modPQ.length = 1296 := by decide +kernel
theorem modM_len : modME.length = 252 ∧ modMB.length = 6 ∧ modMQ.length = 1296 := by decide +kernel
theorem gamP_len : gamPE.length = 252 ∧ gamPB.length = 6 ∧ gamPQ.length = 1728 := by decide +kernel
theorem gamM_len : gamME.length = 252 ∧ gamMB.length = 6 ∧ gamMQ.length = 1728 := by decide +kernel
theorem extP_len : extPE.length = 216 ∧ extPB.length = 36 ∧ extPQ.length = 756 := by decide +kernel
theorem extM_len : extME.length = 216 ∧ extMB.length = 36 ∧ extMQ.length = 576 := by decide +kernel

theorem endP_seg : ∀ i < 1, segK 36 endPB endPQ (fun l => cobK gensP (2 ^ l)) endPE i = true := by
  decide +kernel
theorem endM_seg : ∀ i < 1, segK 36 endMB endMQ (fun l => cobK gensM (2 ^ l)) endME i = true := by
  decide +kernel
theorem modP_seg : ∀ i < 7, segK 252 modPB modPQ (fun l => modK gensP (2 ^ l)) modPE i = true := by
  decide +kernel
theorem modM_seg : ∀ i < 7, segK 252 modMB modMQ (fun l => modK gensM (2 ^ l)) modME i = true := by
  decide +kernel
theorem gamP_seg : ∀ i < 7, segK 252 gamPB gamPQ (fun l => gamK gensP (2 ^ l)) gamPE i = true := by
  decide +kernel
theorem gamM_seg : ∀ i < 7, segK 252 gamMB gamMQ (fun l => gamK gensM (2 ^ l)) gamME i = true := by
  decide +kernel
theorem extP_seg : ∀ i < 6, segK 216 extPB extPQ
    (fun l => extK gensP (nRels .plus) (extRels .plus) (2 ^ l)) extPE i = true := by
  decide +kernel
theorem extM_seg : ∀ i < 6, segK 216 extMB extMQ
    (fun l => extK gensM (nRels .minus) (extRels .minus) (2 ^ l)) extME i = true := by
  decide +kernel

end CertificateChecks.KernelO8.CohCert

end
