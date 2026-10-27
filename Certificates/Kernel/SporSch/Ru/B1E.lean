module

public import Certificates.Kernel.SporSch.Ru.C2253P
public import CFSG.Certificates.Kernel.SporSch.RuEBfsSound
public import Certificates.Data.GMS78RuB1Check
meta import Certificates.Data.GMS78RuB1Check
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuB1K

open CFSG.Sporadic.RuSchreier CFSG.Sporadic.RuSchreier.RuB1 CFSG.Monster.B.Co2.Native

meta def eM : Array (Array Nat) := ruEArr

meta def xM : Array (Array Nat) := xList

end CertificateChecks.KernelSporSch.RuB1K

#kss_perms CertificateChecks.KernelSporSch.RuB1K.EA 12 CertificateChecks.KernelSporSch.RuB1K.eM
#kss_perms CertificateChecks.KernelSporSch.RuB1K.XA 12 CertificateChecks.KernelSporSch.RuB1K.xM

namespace CertificateChecks.KernelSporSch.RuB1K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.Sporadic.RuSchreier
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CertificateChecks.KernelSporSch
  CertificateChecks.KernelSporSch.RuG

theorem eLen : Nat.beq (lenNL (ebfsK Ns0 Ns1 Ns0I Ns1I Z).1) 7 = true := by quickRfl

theorem eOK : allN 7 (fun i => Nat.beq ((ebfsK Ns0 Ns1 Ns0I Ns1I Z).1.getD i 0) (EA i)) = true := by
  quickRfl

theorem cE : allN 7 (fun i => canonK 4060 12 (mask 12) (4060 * 12) (EA i)) = true := by quickRfl

theorem cC0I : canonK 4060 12 (mask 12) (4060 * 12) C0I = true := by quickRfl

@[expose] noncomputable def xP (j : Nat) : Nat :=
  pcomp 4060 12 (mask 12)
    (pcomp 4060 12 (mask 12) (ppow 4060 12 (mask 12) (pidn 4060 12) C0 (Nat.div j 7))
      (EA (Nat.mod j 7)))
    (ppow 4060 12 (mask 12) (pidn 4060 12) C0I (Nat.div j 7))

theorem xOK : allN 35 (fun j => Nat.beq (xP j) (XA j)) = true := by quickRfl

theorem cX : allN 35 (fun j => canonK 4060 12 (mask 12) (4060 * 12) (XA j)) = true := by quickRfl

theorem len_ebfs : (ebfsK Ns0 Ns1 Ns0I Ns1I Z).1.length = 7 := by
  rw [← lenNL_eq]
  exact Nat.eq_of_beq_eq_true eLen

theorem e_eq {i : Nat} (hi : i < 7) : ruEArr[i]! = unpack 4060 12 (EA i) := by
  have hs := ebfsK_sound z_eq zCanon' ns0_eq ns1_eq pNs0 pNs1
  rw [ruEArr_def, hs]
  dsimp only
  rw [getElem!_pos _ i (by simp [len_ebfs]; omega)]
  simp only [List.getElem_toArray, List.getElem_map]
  rw [← Nat.eq_of_beq_eq_true (allN_spec eOK i hi),
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [len_ebfs]; omega),
    Option.getD_some]
where zCanon' : canonK 4060 12 (mask 12) (4060 * 12) Z = true := RuF.zCanon

theorem e_size : ruEArr.size = 7 := by
  rw [ruEArr_def, ebfsK_sound z_eq RuF.zCanon ns0_eq ns1_eq pNs0 pNs1]
  simp [len_ebfs]

end CertificateChecks.KernelSporSch.RuB1K

end
