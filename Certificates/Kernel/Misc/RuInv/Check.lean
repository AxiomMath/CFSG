module

public import Certificates.Kernel.Misc.RuInv.Gens
public import Certificates.Kernel.Misc.RuSq.Bind
public import Certificates.Data.Kernel.Spor.TextAt
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.FactsB2Inputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option Elab.async false

namespace CertificateChecks.KernelMisc.RuInv

open CFSG.KC.Enum CFSG.KS CFSG.KS.Text CFSG.KS.Raw CFSG.Sporadic.RuSchreier CFSG.KC.Misc.RuInv
  CFSG.EvenSporadicStandard.RuStd CertificateChecks.KernelMisc.RuSq
  CertificateChecks.KernelMisc.TextBlocks

theorem line0 : lineK 3 4060 12 AD.n0 (RuSqT.chars.drop (0 * (3 * 4060 + 1))) = true := by
  quickRfl

theorem line1 : lineK 3 4060 12 AD.n1 (RuSqT.chars.drop (1 * (3 * 4060 + 1))) = true := by
  quickRfl

theorem slotOK : (Nat.beq (slotK cprogK AD.n0 AD.n1).1 AD.n2 &&
    Nat.beq (slotK cprogK AD.n0 AD.n1).2 AD.n3) = true := by
  quickRfl

theorem perm0 : permOK 4060 12 (mask 12) (4060 * 12) AD.n2 AD.n4 = true := by quickRfl
theorem perm1 : permOK 4060 12 (mask 12) (4060 * 12) AD.n3 AD.n5 = true := by quickRfl
theorem hz : Nat.beq (E 0) (powP AD.n2 10) = true := by quickRfl
theorem hw1 : Nat.beq (E 1) (wordP G GI ruInvWord1) = true := by quickRfl
theorem hw2 : Nat.beq (E 31) (wordP G GI ruInvWord2) = true := by quickRfl
theorem hw3 : Nat.beq (E 271) (wordP G GI ruInvWord3) = true := by quickRfl
theorem hw4 : Nat.beq (E 751) (wordP G GI ruInvWord4) = true := by quickRfl
theorem reach0 : reachK NX.n0 0 1 = true := by quickRfl
theorem reach1 : reachK NX.n0 1 30 = true := by quickRfl
theorem reach2 : reachK NX.n0 31 240 = true := by quickRfl
theorem reach3 : reachK NX.n0 271 480 = true := by quickRfl
theorem reach4 : reachK NX.n0 751 640 = true := by quickRfl
theorem keysOK : keysK HS PK.n0 1391 = true := by quickRfl
theorem cnt0 : Nat.beq (rcnt (RuSqS.LR 0)) 2048 = true := by quickRfl
theorem cnt1 : Nat.beq (rcnt (RuSqS.LR 1)) 8 = true := by quickRfl

end CertificateChecks.KernelMisc.RuInv

end
