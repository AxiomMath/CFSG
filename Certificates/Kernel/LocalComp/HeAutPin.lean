module

public import Certificates.Kernel.LocalComp.HeAutEnum
public import Certificates.Kernel.LocalComp.HeFixBind
public import CFSG.Certificates.Kernel.HexaKSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelLC.HeAutCheck

open CFSG.KC.BfsPin CFSG.KC.HexaK CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw
open CFSG.ComponentClassification.AS81.HeSylow CFSG.ComponentClassification.GrSLit.HeldFix
open CertificateChecks.KernelLC

@[expose] noncomputable def Pz : Nat := packA 6 heAutZ32.toList

@[expose] noncomputable def Pr : Nat := packA 6 heAutR32.toList

@[expose] noncomputable def Ps : Nat := packA 6 heAutS32.toList

theorem kBindQ : (Nat.beq heAutQ32.toArray.size HeAutQ.ng &&
    allN HeAutQ.ng fun k => bindArrK heAutQ32.toArray[k]! 32 6 (HeAutQ.G k)) = true := by quickRfl

theorem kBindE : (Nat.beq heAutE32.toArray.size HeAutE.ng &&
    allN HeAutE.ng fun k => bindArrK heAutE32.toArray[k]! 32 6 (HeAutE.G k)) = true := by quickRfl

theorem kBindF : (Nat.beq heAutF32.toArray.size HeAutF.ng &&
    allN HeAutF.ng fun k => bindArrK heAutF32.toArray[k]! 32 6 (HeAutF.G k)) = true := by quickRfl

theorem kBindU : (Nat.beq heAutU32.toArray.size HeAutU.ng &&
    allN HeAutU.ng fun k => bindArrK heAutU32.toArray[k]! 32 6 (HeAutU.G k)) = true := by quickRfl

theorem kBindZ : bindArrK heAutZ32 32 6 Pz = true := by quickRfl

theorem kBindR : bindArrK heAutR32 32 6 Pr = true := by quickRfl

theorem kBindS : bindArrK heAutS32 32 6 Ps = true := by quickRfl

theorem kY : (Nat.beq HeAutY.ng 6 && allN 6 fun k => Nat.beq (HeAutY.G k) (HeFix.Q k)) = true := by
  quickRfl

@[expose] noncomputable def gensPerm (g : Nat) (G : Nat → Nat) : Bool :=
  allN g fun k => permOK 32 6 (mask 6) (32 * 6) (G k) (pinvS 32 6 (mask 6) (G k))

theorem kPermG : (gensPerm HeAutY.ng HeAutY.G && gensPerm HeAutQ.ng HeAutQ.G &&
    gensPerm HeAutE.ng HeAutE.G && gensPerm HeAutF.ng HeAutF.G && gensPerm HeAutU.ng HeAutU.G) =
    true := by quickRfl

theorem kPermZ : permOK 32 6 (mask 6) (32 * 6) Pz (pinvS 32 6 (mask 6) Pz) = true := by quickRfl

theorem kPermR : permOK 32 6 (mask 6) (32 * 6) Pr (pinvS 32 6 (mask 6) Pr) = true := by quickRfl

theorem kPermS : permOK 32 6 (mask 6) (32 * 6) Ps (pinvS 32 6 (mask 6) Ps) = true := by quickRfl

theorem pin {gs : List (Array Nat)} {g N : Nat} {G T E S : Nat → Nat}
    (hb : (Nat.beq gs.toArray.size g && allN g fun k => bindArrK gs.toArray[k]! 32 6 (G k)) = true)
    (hp : gensPerm g G = true) (hk : bfsK 32 6 g G N T E S = true) (hf : N ≤ 4000) :
    Pin 32 6 gs g G N T E S :=
  ⟨(binds_of_check hb).1, (binds_of_check hb).2, allN_spec hp, hk, hf⟩

theorem pinY (hp : gensPerm HeAutY.ng HeAutY.G = true) :
    Pin 32 6 hfT0Tabs32.toList HeAutY.ng HeAutY.G HeAutY.N HeAutY.T HeAutY.E HeAutY.S := by
  have hy := kY
  simp only [Bool.and_eq_true] at hy
  have hng : HeAutY.ng = 6 := Nat.eq_of_beq_eq_true hy.1
  refine ⟨?_, fun k hk => ?_, allN_spec hp, HeAutY.ok, by decide⟩
  · rw [Array.toArray_toList, HeFix.hfT0Tabs32_get.1, hng]
  · rw [hng] at hk
    rw [Array.toArray_toList, HeFix.hfT0Tabs32_get.2 k hk,
      Nat.eq_of_beq_eq_true (allN_spec hy.2 k hk)]

end CertificateChecks.KernelLC.HeAutCheck

end
