module

public import Certificates.Kernel.Fin76bAut.Data
public import Certificates.Data.Kernel.Fin76bAut
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFin76bAut

open CFSG.KC.Enum CFSG.KS CFSG.KS.EAut

theorem ch24614Hd : eRecHdK ET G GI 5 1920 T PL = true := by quickRfl

theorem ch24614Rec0 : eRecSlK G 5 1920 T PL POS SRT SRI 0 480 = true := by quickRfl

theorem ch24614Rec1 : eRecSlK G 5 1920 T PL POS SRT SRI 480 480 = true := by quickRfl

theorem ch24614Rec2 : eRecSlK G 5 1920 T PL POS SRT SRI 960 480 = true := by quickRfl

theorem ch24614Rec3 : eRecSlK G 5 1920 T PL POS SRT SRI 1440 480 = true := by quickRfl

theorem ch24614Syl : bAnd(eSylHdK 1920 T SP 5 128 ST SPL,
    eRecSlK (fun j => T (SP j)) 5 128 ST SPL SPOS SSRT SSRI 0 128) = true := by quickRfl

theorem ch24614Cls : eClsK 1920 T 5 REP 155 IV ICL ICJ = true := by quickRfl

theorem ch24614Sq : bAnd(eSqK ET 1920 T 0 22 W2, eSqK ET 1920 T 21 1 W4) = true := by quickRfl

theorem ch24614Pair : ePairK ET 1920 T 80 PA PB PI = true := by quickRfl

theorem ch24614Inn : eInnK ET 1920 T 16 INN INE = true := by quickRfl

theorem ch24614Q : eQK 1920 T 16 INN QC = true := by quickRfl

end CertificateChecks.KernelFin76bAut

end
