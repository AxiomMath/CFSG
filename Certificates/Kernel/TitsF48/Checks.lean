module

public import Certificates.Kernel.TitsF48.Data
public import Certificates.Kernel.TitsD.Data
public import Certificates.Kernel.TitsOct.Data
public import Certificates.Kernel.Misc.Tits.Text
public import Certificates.Data.Kernel.TitsF48K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsF48

open CFSG.KC.Enum CFSG.KS CFSG.KC.TwoF4LieK CFSG.KC.TitsOctK CFSG.KC.TitsDK CFSG.KC.TitsF48K
  CFSG.KD.TitsF48 CertificateChecks.KernelMisc

@[expose] noncomputable def lpF (i : Nat) : Nat := fw 11 CFSG.KD.TitsOct.LP i

@[expose] noncomputable def HG (j : Nat) : Nat := TitsText.F (Nat.add 43 j)

@[expose] noncomputable def Q0 : Nat := TitsText.F 64

@[expose] noncomputable def LY : Nat := CFSG.KD.TitsOct.LAY0

theorem fwsEq : fws = [[8], [12], [14], [16], [11, 6], [4, 2, 2]] := by decide +kernel

theorem gwsEq : gws = [[2, 2], [6], [3, 7, 14, 3], [10, 13, 6]] := by decide +kernel

theorem lens : bAnd(Nat.beq WA.length 1024, bAnd(Nat.beq WB.length 1024,
    Nat.beq WC.length 256)) = true := by
  quickRfl

theorem bindF : bindK HG CFSG.KD.TitsD.HI FA fws = true := by quickRfl

theorem bindG : bindK HG CFSG.KD.TitsD.HI GG gws = true := by quickRfl

theorem invFA : invF FA FAI = true := by quickRfl

theorem recF : recR lpF FA 6 (fun x => bIf(Nat.beq x 87, true, Nat.beq x 133)) 8 1024 LY ORD PR
    LB PS = true := by
  quickRfl

theorem half : halfF ORD PR LB = true := by quickRfl

theorem far : bAnd(farK LY, Nat.beq (layAt LY 133) 8) = true := by quickRfl

theorem small : smallF lpF FA CFSG.KD.TitsOct.PL (GG 0) (GG 1) (GG 2) (GG 3) = true := by
  quickRfl

theorem rowA0 : rowsK (rowA FA FAI LY ORD PR LB PS (GG 0) Q0 (GG 2) (GG 3) S1) 0 (WA.take 512) =
    true := by
  quickRfl

theorem rowA1 : rowsK (rowA FA FAI LY ORD PR LB PS (GG 0) Q0 (GG 2) (GG 3) S1) 512
    (WA.drop 512) = true := by
  quickRfl

theorem rowB0 : rowsK (rowB FA FAI LY ORD PR LB PS (GG 0) Q0 (GG 2) (GG 3) S2) 0 (WB.take 512) =
    true := by
  quickRfl

theorem rowB1 : rowsK (rowB FA FAI LY ORD PR LB PS (GG 0) Q0 (GG 2) (GG 3) S2) 512
    (WB.drop 512) = true := by
  quickRfl

theorem rowC0 : rowsK (rowC FA LY ORD PR LB PS (GG 0) Q0 (GG 2) (GG 3) S1 S2) 0 WC = true := by
  quickRfl

end CertificateChecks.KernelTitsF48

end
