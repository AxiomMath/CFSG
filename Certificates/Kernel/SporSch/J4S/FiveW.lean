
module

public import Certificates.Kernel.SporSch.J4S.FiveT
meta import CFSG.Sporadic.Schreier.J4SData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSporSch.J4FW CFSG.Sporadic.J4Schreier.fiveGenWordsText
#kss_tokens CertificateChecks.KernelSporSch.J4FW CFSG.Sporadic.J4Schreier.fiveGenWordsText
#kss_words CertificateChecks.KernelSporSch.J4FW CFSG.Sporadic.J4Schreier.fiveGenWordsText 4

namespace CertificateChecks.KernelSporSch.J4Five

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.C11
open CFSG.Sporadic.J4Schreier CFSG.Sporadic.Schreier.PairText
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.J4XY

theorem fw_eq : fiveGenWords = J4FW.ws.toArray := by
  rw [fiveGenWords, J4FW.eq, CFSG.KS.SporSch.tokK_sound J4FW.tok]
  exact tokWords_sound J4FW.wtok

theorem w0 : Nat.beq (W J4FW.w0) (J4GC 0) = true := by quickRfl
theorem w1 : Nat.beq (W J4FW.w1) (J4GC 1) = true := by quickRfl
theorem w2 : Nat.beq (W J4FW.w2) (J4GC 2) = true := by quickRfl
theorem w3 : Nat.beq (W J4FW.w3) (J4GC 3) = true := by quickRfl

theorem gens_eq : ∀ i < 4, wordCols (fiveGenWords[i]!) = generatorColumns[i]! := by
  intro i hi
  rw [GC_eq hi, fw_eq, wordCols_eq']
  obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  · exact congrArg unpack11 (Nat.eq_of_beq_eq_true w0)
  · exact congrArg unpack11 (Nat.eq_of_beq_eq_true w1)
  · exact congrArg unpack11 (Nat.eq_of_beq_eq_true w2)
  · exact congrArg unpack11 (Nat.eq_of_beq_eq_true w3)

end CertificateChecks.KernelSporSch.J4Five

end
