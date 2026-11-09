module

public import Certificates.Kernel.HSStd.U43Z4SolD
public import CFSG.Certificates.Kernel.Spor.PtPre

public section

namespace CFSG.KC.U43Case

open CFSG.KC.Enum CFSG.KS CFSG.KS.PtC

theorem commP_eq_commPt {n w : Nat} (hn : n < 16777216) (hw : n + 1 < 2 ^ w) (a b : Nat) :
    commP n w a b = commPt n w a b := by
  unfold commP pp
  exact beq_pcomp_comm hn hw a b

theorem commPt4_eq (n w a c d e f : Nat) :
    (commPt n w a c && commPt n w a d && commPt n w a e && commPt n w a f) =
      ((preT n w a c && preT n w a d && preT n w a e && preT n w a f) &&
        (commPt n w a c && commPt n w a d && commPt n w a e && commPt n w a f)) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true]
  constructor
  · intro h
    obtain ⟨⟨⟨hc, hd⟩, he⟩, hf⟩ := h
    exact ⟨⟨⟨⟨preT_of hc, preT_of hd⟩, preT_of he⟩, preT_of hf⟩, ⟨⟨hc, hd⟩, he⟩, hf⟩
  · intro h
    exact h.2

@[expose] noncomputable def cent5Pt (n w t N : Nat) (Y : Nat → Nat) (c k : Nat) : Nat :=
  ((List.range N).filter fun i =>
    (preT n w (Y i) c && preT n w (Y i) (cpP n w t c) && preT n w (Y i) k &&
        preT n w (Y i) (cpP n w t k)) &&
      (commPt n w (Y i) c && commPt n w (Y i) (cpP n w t c) && commPt n w (Y i) k &&
        commPt n w (Y i) (cpP n w t k))).length

theorem cent5P_eq_cent5Pt {n w : Nat} (hn : n < 16777216) (hw : n + 1 < 2 ^ w) (t N : Nat)
    (Y : Nat → Nat) (c k : Nat) : cent5P n w t N Y c k = cent5Pt n w t N Y c k := by
  unfold cent5P cent5Pt
  simp only [commP_eq_commPt hn hw]
  congr 1
  exact List.filter_congr fun i _ => commPt4_eq n w (Y i) c _ k _

end CFSG.KC.U43Case

namespace CertificateChecks.KernelHSStd.U43Z4

open CFSG.KC CFSG.KC.Enum CFSG.KS CFSG.KC.U43Case CertificateChecks.KernelHSStd

@[expose] noncomputable def ksCPt (g : Nat) : Bool :=
  (lnth [] z4CG g).all fun p =>
    cent5Pt 820 10 (Z4P 0) Z4Y.cnt Z4Y.T (Z4Y.T p.1) (Z4Y.T p.2) == 3

theorem ksC_eq_ksCPt (g : Nat) : ksC g = ksCPt g := by
  unfold ksC ksCPt
  simp only [cent5P_eq_cent5Pt (n := 820) (w := 10) (by decide) (by decide)]

end CertificateChecks.KernelHSStd.U43Z4

end
