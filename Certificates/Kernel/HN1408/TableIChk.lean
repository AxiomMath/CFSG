module

public import Certificates.Kernel.HN1408.TableIDefs
public import Certificates.Kernel.HN1408.SpecDefs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Spor.BindList

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.Blk
open CFSG.EvenSporadicStandard.HNRecog
open CFSG.Sporadic.SmallOddCore.Native (natArr)

@[expose] noncomputable def headI (ws : List (List Nat)) (k m : Nat) (G GI GJ T PL : Nat → Nat)
    (cnt : Nat) : Bool :=
  bAnd(Nat.beq ws.length k, bAnd(allN k fun j => bAnd(Nat.beq (GI j) (WK (ws.getD j [])),
    bAnd(Nat.beq (G j) idK, bAnd(canonK 1408 11 (mask 11) (1408 * 11) (GJ j),
      invEqK 1408 11 (mask 11) (1408 * 11) (GI j) (GJ j)))),
    bAnd(Nat.beq cnt m, penumHdK idK cnt 100000 T PL)))

theorem kH1 : headI nWords1 7 256 TI1.G TI1.GI J1 TI1.T TI1.PL TI1.cnt = true := by quickRfl
theorem kH3 : headI sWords3 2 960 TI3.G TI3.GI J3 TI3.T TI3.PL TI3.cnt = true := by quickRfl
@[expose] noncomputable def headI4 : Bool :=
  bAnd(Nat.beq nSpec3.length 4, bAnd(allN 4 fun j =>
    bAnd(Nat.beq (TI4.GI j) (specK [TI3.GI 0, TI3.GI 1] (nSpec3.getD j [])),
    bAnd(Nat.beq (TI4.G j) idK, bAnd(canonK 1408 11 (mask 11) (1408 * 11) (J4 j),
      invEqK 1408 11 (mask 11) (1408 * 11) (TI4.GI j) (J4 j)))),
    bAnd(Nat.beq TI4.cnt 16, penumHdK idK TI4.cnt 100000 TI4.T TI4.PL)))

theorem kH4 : headI4 = true := by quickRfl

theorem kR4 : bAnd(bAnd(pe4, hs4), cl4) = true := by quickRfl

@[expose] noncomputable def headL (k : Nat) (L : List CFSG.Sporadic.Th.Native.Table) (m : Nat)
    (G GI GJ T PL : Nat → Nat) (cnt : Nat) : Bool :=
  bAnd(Nat.beq L.length 2, bAnd(allN 2 fun j => bAnd(bindListK k 4 (GI j) (natArr (L.getD j #[])).toList,
    bAnd(Nat.beq (G j) (pidn k 4), bAnd(canonK k 4 (mask 4) (k * 4) (GI j),
      bAnd(canonK k 4 (mask 4) (k * 4) (GJ j), invEqK k 4 (mask 4) (k * 4) (GI j) (GJ j))))),
    bAnd(Nat.beq cnt m, bAnd(szOK k 4, penumHdK (pidn k 4) cnt 100000 T PL))))

theorem kL1 : bAnd(bAnd(bAnd(headL 5 labs1 120 TL1.G TL1.GI TL1J TL1.T TL1.PL TL1.cnt, peL1),
    hsL1), clL1) = true := by quickRfl
theorem kL3 : bAnd(bAnd(bAnd(headL 5 labs3 60 TL3.G TL3.GI TL3J TL3.T TL3.PL TL3.cnt, peL3),
    hsL3), clL3) = true := by quickRfl
theorem kL2h : headL 8 labs2 20160 TL2.G TL2.GI TL2J TL2.T TL2.PL TL2.cnt = true := by quickRfl
theorem kLSh : headL 8 labsS2 20160 TLS.G TLS.GI TLSJ TLS.T TLS.PL TLS.cnt = true := by quickRfl

theorem kB1 : bindListK 1408 4 (TB.F 0) (TB1.chars.map fun c => c.toNat - 48) = true := by quickRfl
theorem kB2 : bindListK 1408 4 (TB.F 1) (TB2.chars.map fun c => c.toNat - 48) = true := by quickRfl
theorem kB3 : bindListK 1408 4 (TB.F 2) (TB3.chars.map fun c => c.toNat - 48) = true := by quickRfl

@[expose] noncomputable def blkK (i k : Nat) (ws : List (List Nat)) (LG : Nat → Nat) : Bool :=
  bAnd(blkLeK 1408 4 (TB.F i) k, bAnd(blkSurjK 1408 4 (TB.F i) k,
    allN 2 fun j => blkMapK 1408 11 4 (TB.F i) k (WK (ws.getD j [])) (LG j)))

theorem kD1 : blkK 0 5 classz.centGens TL1.GI = true := by quickRfl
theorem kD2 : blkK 1 8 classb.centGens TL2.GI = true := by quickRfl
theorem kD3 : blkK 2 5 sWords3 TL3.GI = true := by quickRfl
theorem kDS : blkK 1 8 sWords2 TLS.GI = true := by quickRfl

theorem kT1 : bAnd(allN 7 fun j => bAnd(blkTrivK 1408 11 4 (TB.F 0) (TI1.GI j),
      commP (TI1.GI j) (WK wordZ)),
    bAnd(Nat.blt (TW1 0) TI1.cnt, bAnd(Nat.beq (TI1.T (TW1 0)) (WK wordA),
    bAnd(Nat.blt (TW1 1) TI1.cnt, bAnd(Nat.beq (TI1.T (TW1 1)) (WK wordZ),
      allN 256 fun i => strictB (TQ1 i) fun q => bAnd(Nat.blt q 4,
        Nat.beq (pc (TI1.T i) (TI1.T i))
          (nIf(Nat.beq q 0, idK, nIf(Nat.beq q 1, WK wordA, nIf(Nat.beq q 2, WK wordZ, WK wordAZ)))))))))) =
    true := by
  quickRfl

theorem kT2 : bAnd(allN 2 fun j => strictB (WK (sWords2.getD j [])) fun s =>
      bAnd(commP s (WK wordB), orbMapK s),
    bAnd(blkTrivK 1408 11 4 (TB.F 1) (WK wordA), bAnd(blkTrivK 1408 11 4 (TB.F 1) (WK wordB),
    bAnd(bIf(inOrbS2 (pt (WK wordA) 3), false, true), bAnd(bIf(inOrbS2 (pt (WK wordB) 3), false, true),
      bIf(inOrbS2 (pt (WK (wordA ++ wordB)) 3), false, true)))))) = true := by
  quickRfl
theorem kT3 : bAnd(allN 2 fun j => commP (TI3.GI j) (WK wordZ₁),
    bAnd(allN 4 fun j => bAnd(blkTrivK 1408 11 4 (TB.F 2) (TI4.GI j),
      bAnd(Nat.blt (TW3 j) TI3.cnt, Nat.beq (TI3.T (TW3 j)) (TI4.GI j))),
    bAnd(allN 16 fun i => Nat.beq (pc (TI4.T i) (TI4.T i)) idK,
      strictB (WK wordA) fun a => strictB (WK wordZ₁) fun z => strictB (WK (wordA ++ wordZ₁)) fun az =>
        allN 960 fun i => strictB (TI3.T i) fun x =>
          bAnd(bIf(Nat.beq x a, false, true), bAnd(bIf(Nat.beq x z, false, true),
            bIf(Nat.beq x az, false, true)))))) = true := by
  quickRfl

end CFSG.KD.HN1408

end
