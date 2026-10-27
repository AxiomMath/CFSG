module

public import Certificates.Data.J2KJCoverC16
public import Certificates.Kernel.J2Cover.M22Fold
public import Certificates.Kernel.Misc.Perm.J2C3A
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover.C16K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Child3
open CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.J2Cover.Models
open CFSG.RankThree.PartTwo.J2Residue.C16
open CertificateChecks.KernelJ2Cover

open CertificateChecks.KernelMisc.J2C3 (Z hz)

theorem cZ : CnN 315 9 Z := by quickRfl

theorem kConj : Nat.beq (pcomp 315 9 (mask 9) (wordP cWord) Z)
    (pcomp 315 9 (mask 9) (wordP x0Word) (wordP cWord)) = true := by quickRfl

theorem kCent : d0.all (fun a => Nat.beq (pcomp 315 9 (mask 9) (ELT a) (wordP x0Word))
    (pcomp 315 9 (mask 9) (wordP x0Word) (ELT a))) = true := by quickRfl

theorem kTab : d0.all (fun a => d0.contains (itK a) && d0.all fun b => d0.contains (mtK a b)) =
    true := by quickRfl

theorem kCob : d0.all (fun a => d0.all fun b => (fRK a).testBit b ==
    (lamMaskD0.testBit a ^^ lamMaskD0.testBit b ^^ lamMaskD0.testBit (mtK a b))) = true := by
  quickRfl

theorem kLt : d0.all (fun a => decide (a < 128)) = true := by quickRfl

theorem it_pt (a : Nat) : invTab[a]! = itK a := congrFun it_eq a

theorem fR_pt (a : Nat) : fRows[a]! = fRK a := congrFun fR_eq a

theorem c16_true : c16Check () = true := by
  have hlt := List.all_eq_true.1 kLt
  have e1 : eqA 315 (compA 315 (wordArr cWord) CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.zArr)
      (compA 315 (wordArr x0Word) (wordArr cWord)) = true := by
    rw [wordArr_eq, wordArr_eq, hz,
      compA_unpackN (wordP_canon _) cZ, compA_unpackN (wordP_canon _) (wordP_canon _),
      eqA_unpackN (canon_pcN (wordP_canon _) cZ) (canon_pcN (wordP_canon _) (wordP_canon _))]
    exact kConj
  have e2 : d0.all (fun a => d0.contains invTab[a]! &&
      d0.all fun b => d0.contains (mulTab[a]!)[b]!) = true := by
    simp only [it_pt, mt_pt]
    exact kTab
  have e3 : d0.all (fun a => eqA 315 (compA 315 eltArrs[a]! (wordArr x0Word))
      (compA 315 (wordArr x0Word) eltArrs[a]!)) = true := by
    refine List.all_eq_true.2 fun a ha => ?_
    have hl : a < 128 := of_decide_eq_true (hlt a ha)
    rw [eltArrs_eq a hl, wordArr_eq, compA_unpackN (eltT_canon a hl) (wordP_canon _),
      compA_unpackN (wordP_canon _) (eltT_canon a hl),
      eqA_unpackN (canon_pcN (eltT_canon a hl) (wordP_canon _))
        (canon_pcN (wordP_canon _) (eltT_canon a hl))]
    exact List.all_eq_true.1 kCent a ha
  have e4 : (!(maskBit lamMaskD0 0)) = true := by quickRfl
  have e5 : d0.all (fun a => d0.all fun b => bitAt fRows a b == cobBit lamMaskD0 a b) = true := by
    simp only [bitAt, cobBit, maskBit, fR_pt, mt_pt]
    exact kCob
  unfold c16Check
  simp only [e1, e2, e3, e4, e5, Bool.and_self]

end CertificateChecks.KernelJ2Cover.C16K

end
