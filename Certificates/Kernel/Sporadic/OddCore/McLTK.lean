module

public import Certificates.Kernel.Sporadic.OddCore.McLTC
public import Certificates.Kernel.Sporadic.OddCore.McLL
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.McLTK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CertificateChecks.KernelCensus CertificateChecks.KernelSpor

@[expose] noncomputable def cK (p : Nat) : Bool := canonK 275 9 (mask 9) (275 * 9) p

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 275 9 (mask 9) p q

@[expose] noncomputable def iE (p q : Nat) : Bool := invEqK 275 9 (mask 9) (275 * 9) p q

@[expose] noncomputable def idP : Nat := pidn 275 9

@[expose] noncomputable def sK (p : Nat) : Bool :=
  siftK 275 9 (mask 9) (275 * 9) (pidn 275 9) McLC.LR McLC.TRI McLC.BP 5 0 p

@[expose] noncomputable def cm (p q : Nat) : Bool := Nat.beq (pc p q) (pc q p)

@[expose] noncomputable def cube1 (p : Nat) : Bool := Nat.beq (pc p (pc p (pc p idP))) idP

@[expose] noncomputable def lo32 (v : Nat) : Nat := Nat.land v 4294967295
@[expose] noncomputable def hi32 (v : Nat) : Nat := Nat.shiftRight v 32

@[expose] noncomputable def atK (cnt : Nat) (T : Nat → Nat) (q p : Nat) : Bool :=
  bAnd(Nat.blt q cnt, Nat.beq (T q) p)

@[expose] noncomputable def atOr (cnt : Nat) (T : Nat → Nat) (q p : Nat) (e : Bool) : Bool :=
  bIf(Nat.blt q cnt, Nat.beq (T q) p, e)

@[expose] noncomputable def X : Nat := McLTh.F 0
@[expose] noncomputable def XI : Nat := McLThI 0

@[expose] noncomputable def gxG (c : Nat) : Nat :=
  nIf(Nat.beq c 3, McLTl.F 0, McLTh.F c)
@[expose] noncomputable def gxGI (c : Nat) : Nat :=
  nIf(Nat.beq c 3, McLTlI 0, McLThI c)

theorem base_ok : (szOK 275 9 && cK idP && CFSG.KS.Prim.idK 275 9 (mask 9) &&
    allN 11 (fun k => cK (McLTh.F k) && cK (McLThI k) && iE (McLTh.F k) (McLThI k)) &&
    allN 15 (fun k => cK (McLTl.F k) && cK (McLTlI k) && iE (McLTl.F k) (McLTlI k)) &&
    cK (McLCT.F 0) && cK (McLTO 0) && iE (McLCT.F 0) (McLTO 0) &&
    allN 2 (fun j => Nat.beq (McLTC.G j) (McLC.S j) && cK (McLTC.G j) && cK (McLTC.GI j) &&
      iE (McLTC.G j) (McLTC.GI j)) &&
    allN 5 (fun j => Nat.beq (McLTT.G j) idP && Nat.beq (McLTT.GI j) (McLTh.F (j + 6))) &&
    allN 5 (fun j => Nat.beq (McLTR.G j) idP && Nat.beq (McLTR.GI j) (McLTl.F (j + 2))) &&
    allN 4 (fun j => Nat.beq (McLTA.G j) idP && Nat.beq (McLTA.GI j) (McLTl.F (j + 7))) &&
    Nat.beq McLTT.cnt 729 && Nat.beq McLTR.cnt 243 && Nat.beq McLTA.cnt 81 &&
    Nat.beq McLTC.cnt 30800 &&
    penumHdK idP McLTT.cnt 800 McLTT.T McLTT.PL && penumHdK idP McLTR.cnt 300 McLTR.T McLTR.PL &&
    penumHdK idP McLTA.cnt 200 McLTA.T McLTA.PL &&
    penumHdK X McLTC.cnt 30800 McLTC.T McLTC.PL) = true := by
  quickRfl

theorem sifts_ok : (allN 5 (fun j => sK (McLTh.F (j + 6))) && allN 5 (fun j => sK (McLTl.F (j + 2))) &&
    allN 4 (fun j => sK (McLTl.F (j + 7))) && sK (McLTl.F 0) && !sK (McLTl.F 1) &&
    sK (pc (McLTl.F 1) (McLCT.F 0)) && sK (McLTl.F 11) && !sK (McLTl.F 14) &&
    sK (pc (McLTl.F 14) (McLCT.F 0))) = true := by
  quickRfl

theorem small_ok : (Nat.beq (pc (pc (McLTl.F 0) X) (McLTlI 0)) XI && cm (McLTl.F 1) X &&
    allN 5 (fun j => cm X (McLTl.F (j + 2))) && allN 5 (fun j => cm X (McLTh.F (j + 6))) &&
    allN 20 (fun k => atK McLTR.cnt McLTR.T (r32 McLTQNR k)
      (pc (pc (gxG (Nat.div k 5)) (McLTl.F (Nat.add (Nat.mod k 5) 2))) (gxGI (Nat.div k 5)))) &&
    (Nat.beq (pc (pc (McLTl.F 11) X) (McLTlI 11)) X ||
      Nat.beq (pc (pc (McLTl.F 11) X) (McLTlI 11)) XI) &&
    atK McLTR.cnt McLTR.T (r32 McLTQX 0) X && atK McLTR.cnt McLTR.T (r32 McLTQX 1) (McLTl.F 12) &&
    atK McLTR.cnt McLTR.T (r32 McLTQX 2) (McLTl.F 13) &&
    Nat.beq (pc (pc (McLTl.F 12) (McLTl.F 13)) (pc (McLTlI 12) (McLTlI 13))) X &&
    Nat.beq (pc (McLTl.F 14) (McLTl.F 14)) idP &&
    allN 4 (fun j => Nat.beq (pc (pc (McLTl.F 14) (McLTl.F (j + 7))) (McLTlI 14))
      (McLTlI (j + 7))) &&
    allN 4 (fun j => atK McLTC.cnt McLTC.T (r32 McLTQAC j) (McLTl.F (j + 7)))) = true := by
  quickRfl

theorem recT_ok :
    (penumSlK 275 9 (mask 9) (275 * 9) true McLTT.G McLTT.GI 5 McLTT.cnt McLTT.T McLTT.PL
      McLTT.POS McLTT.SRT McLTT.SRI 0 McLTT.cnt &&
    slK McLTT.cnt (hsortPtK 275 9 (mask 9) McLTT.cnt McLTT.T McLTT.HS McLTT.HSI) 0 McLTT.cnt &&
    slK (Nat.mul McLTT.cnt 10) (findPtK McLTT.cnt McLTT.T
      (prodQK 275 9 (mask 9) 10 McLTT.T (bothK 5 McLTT.GI (fun j => McLThI (j + 6))))
      McLTClT) 0 (Nat.mul McLTT.cnt 10)) = true := by
  quickRfl

theorem recR_ok :
    (penumSlK 275 9 (mask 9) (275 * 9) true McLTR.G McLTR.GI 5 McLTR.cnt McLTR.T McLTR.PL
      McLTR.POS McLTR.SRT McLTR.SRI 0 McLTR.cnt &&
    slK McLTR.cnt (hsortPtK 275 9 (mask 9) McLTR.cnt McLTR.T McLTR.HS McLTR.HSI) 0 McLTR.cnt &&
    slK (Nat.mul McLTR.cnt 10) (findPtK McLTR.cnt McLTR.T
      (prodQK 275 9 (mask 9) 10 McLTR.T (bothK 5 McLTR.GI (fun j => McLTlI (j + 2))))
      McLTClR) 0 (Nat.mul McLTR.cnt 10)) = true := by
  quickRfl

theorem recA_ok :
    (penumSlK 275 9 (mask 9) (275 * 9) true McLTA.G McLTA.GI 4 McLTA.cnt McLTA.T McLTA.PL
      McLTA.POS McLTA.SRT McLTA.SRI 0 McLTA.cnt &&
    slK McLTA.cnt (hsortPtK 275 9 (mask 9) McLTA.cnt McLTA.T McLTA.HS McLTA.HSI) 0 McLTA.cnt &&
    slK (Nat.mul McLTA.cnt 8) (findPtK McLTA.cnt McLTA.T
      (prodQK 275 9 (mask 9) 8 McLTA.T (bothK 4 McLTA.GI (fun j => McLTlI (j + 7))))
      McLTClA) 0 (Nat.mul McLTA.cnt 8)) = true := by
  quickRfl

@[expose] noncomputable def rK (i : Nat) : Bool :=
  cK (McLTRI i) && iE (McLTR.T i) (McLTRI i) && cube1 (McLTR.T i) &&
    atK McLTT.cnt McLTT.T (r32 McLTQRT i) (McLTR.T i) &&
    memK 275 9 (mask 9) McLTC.cnt McLTC.T McLTC.HS (McLTR.T i) (lo32 (McLTQRC i))
      (hi32 (McLTQRC i)) &&
    (!Nat.blt (lo32 (McLTQRC i)) McLTC.cnt || Nat.beq (McLTR.T i) X || Nat.beq (McLTR.T i) XI)

@[expose] noncomputable def rZ (i : Nat) : Bool := allN 5 (fun j => cm (McLTR.T i) (McLTl.F (j + 2)))

@[expose] noncomputable def aK (i : Nat) : Bool :=
  cube1 (McLTA.T i) && atK McLTT.cnt McLTT.T (r32 McLTQAT i) (McLTA.T i) &&
    memK 275 9 (mask 9) McLTR.cnt McLTR.T McLTR.HS (McLTA.T i) (lo32 (McLTQAR i))
      (hi32 (McLTQAR i))

@[expose] noncomputable def aaK (i : Nat) : Bool := allN 81 (fun j => cm (McLTA.T i) (McLTA.T j))

theorem rA_ok : (allN 243 rK && Nat.beq (cntBelowK McLTR.cnt rZ 4) 3) = true := by quickRfl

@[expose] noncomputable def aR (i : Nat) : Bool := Nat.blt (lo32 (McLTQAR i)) McLTR.cnt

theorem aA_ok : (allN 81 aK && Nat.beq (cntBelowK McLTA.cnt aR 2) 27) = true := by
  quickRfl

theorem aa_ok : allN 81 aaK = true := by quickRfl

@[expose] noncomputable def tKe (i e : Nat) : Bool :=
  atOr McLTR.cnt McLTR.T (lo32 (McLTQS i)) e
      (absK 275 9 (mask 9) McLTT.cnt McLTT.T McLTT.HS (pc (pc (McLTlI 11) e) (McLTl.F 11))
        (hi32 (McLTQS i))) &&
    Nat.blt (lo32 (McLTQRA i)) McLTR.cnt &&
    atK McLTA.cnt McLTA.T (hi32 (McLTQRA i)) (pc (McLTRI (lo32 (McLTQRA i))) e) &&
    atOr McLTR.cnt McLTR.T (lo32 (McLTQO i)) e
      (atOr McLTA.cnt McLTA.T (hi32 (McLTQO i)) e (!cube1 e)) &&
    memK 275 9 (mask 9) McLTC.cnt McLTC.T McLTC.HS e (lo32 (McLTQTC i)) (hi32 (McLTQTC i)) &&
    (!Nat.blt (lo32 (McLTQTC i)) McLTC.cnt || atK McLTA.cnt McLTA.T (hi32 (McLTQO i)) e) &&
    atOr McLTA.cnt McLTA.T (hi32 (McLTQO i)) e
      (Nat.ble (cntBelowK McLTA.cnt (fun k => cm e (McLTA.T k)) 2) 9)

@[expose] noncomputable def tK (i : Nat) : Bool :=
  strictB (McLTT.T i) (fun e => tKe i e)

@[expose] noncomputable def tZ (i : Nat) : Bool := allN 5 (fun j => cm (McLTT.T i) (McLTh.F (j + 6)))

@[expose] noncomputable def tC (i : Nat) : Bool := Nat.blt (lo32 (McLTQTC i)) McLTC.cnt

theorem tCnt_ok : (Nat.beq (cntBelowK McLTT.cnt tC 12) 20 && Nat.beq (cntBelowK McLTT.cnt tZ 12) 3) =
    true := by quickRfl

@[expose] noncomputable def cOK (c : Nat) : Bool := Nat.beq c idP || Nat.beq c X || Nat.beq c XI

@[expose] noncomputable def prK (i j : Nat) : Bool :=
  cOK (pc (pc (McLTR.T i) (McLTR.T j)) (pc (McLTRI i) (McLTRI j)))

@[expose] noncomputable def tSl (s : Nat) : Bool :=
  allN 27 (fun d => strictB (Nat.add (Nat.mul 27 s) d) (fun i => bIf(Nat.blt i 729, tK i, true)))

@[expose] noncomputable def pSl (s : Nat) : Bool :=
  allN 9 (fun d => strictB (Nat.add (Nat.mul 9 s) d) (fun i =>
    bIf(Nat.blt i 243, allN 243 (prK i), true)))

@[expose] noncomputable def cSl (s : Nat) : Bool :=
  penumSlK 275 9 (mask 9) (275 * 9) true McLTC.G McLTC.GI 2 McLTC.cnt McLTC.T McLTC.PL McLTC.POS
    McLTC.SRT McLTC.SRI (Nat.mul 400 s) 400

@[expose] noncomputable def hSl (s : Nat) : Bool :=
  slK McLTC.cnt (hsortPtK 275 9 (mask 9) McLTC.cnt McLTC.T McLTC.HS McLTC.HSI) (Nat.mul 1100 s) 1100

end CertificateChecks.KernelSpor.McLTK

end
