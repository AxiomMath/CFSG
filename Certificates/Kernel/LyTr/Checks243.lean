module

public import Certificates.Kernel.LyTr.Slices
public import Certificates.Data.Kernel.Spor.MulHF
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.LyTr.Defs

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelLyTr

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KS.Raw
open CFSG.Sporadic.Recognition.LyonsSims

theorem k_base : bAnd(szOK 243 8, bAnd(c8 id8, bAnd(CFSG.KS.Prim.idK 243 8 (mask 8),
    bAnd(allN 5 (fun j => bAnd(c8 (GH.F j), bAnd(c8 (GHI j), i8 (GH.F j) (GHI j)))),
    bAnd(allN 3 (fun j => bAnd(c8 (LH.F j), bAnd(c8 (LHI j), i8 (LH.F j) (LHI j)))),
    bAnd(allN 5 (fun j => bAnd(c8 (R2.GI j), bAnd(c8 (R2I j), bAnd(i8 (R2.GI j) (R2I j),
      Nat.beq (R2.G j) id8)))),
    bAnd(allN 6 (fun j => bAnd(c8 (RP j), bAnd(c8 (RPI j), i8 (RP j) (RPI j)))),
    bAnd(Nat.beq R2.cnt 3888, penumHdK id8 R2.cnt 5000 R2.T R2.PL)))))))) = true := by
  quickRfl

theorem k_words : bAnd(allN 5 (fun j => Nat.beq (wK 243 8 LG (Ly243.txyWords.getD j [])) (R2.GI j)),
    allN 6 (fun j => Nat.beq (wK 243 8 LG (Ly243.repWords.getD j [])) (RP j))) = true := by
  quickRfl

theorem k_lines : bAnd(allN 3 (fun i => ord8 3 (LH.F i)),
    allN 3 (fun i => allN 3 (fun j => bIf(Nat.beq i j, true,
      !inL (LH.F j) (LH.F i) (LHI i))))) = true := by
  quickRfl

theorem k_perm : allN 5 (fun m => allN 3 (fun i =>
    bIf(inL (cj8 (GH.F m) (GHI m) (LH.F i)) (LH.F 0) (LHI 0), true,
    bIf(inL (cj8 (GH.F m) (GHI m) (LH.F i)) (LH.F 1) (LHI 1), true,
      inL (cj8 (GH.F m) (GHI m) (LH.F i)) (LH.F 2) (LHI 2))))) = true := by
  quickRfl

theorem k_fix0 : allN 4 (fun m => inL (cj8 (GH.F m) (GHI m) (LH.F 0)) (LH.F 0) (LHI 0)) = true := by
  quickRfl

theorem k_kswap : bAnd(inL (cj8 (GH.F 4) (GHI 4) (LH.F 0)) (LH.F 1) (LHI 1),
    bAnd(inL (cj8 (GH.F 4) (GHI 4) (LH.F 1)) (LH.F 0) (LHI 0),
      inL (cj8 (GH.F 4) (GHI 4) (LH.F 2)) (LH.F 2) (LHI 2))) = true := by
  quickRfl

theorem k_ker : allN 5 (fun j => allN 3 (fun i =>
    inL (cj8 (R2.GI j) (R2I j) (LH.F i)) (LH.F i) (LHI i))) = true := by
  quickRfl

@[expose] noncomputable def cjOf (c : Nat) : Nat := fld(CJ 0, Nat.mul 3 c, 7)

@[expose] noncomputable def cosQ (c : Nat) : Nat :=
  p8 (p8 (RP (Nat.div c 10)) (GB (Nat.mod c 10))) (RPI (cjOf c))

theorem k_coset : bAnd(Nat.beq (RP 0) id8, bAnd(allN 60 (fun c => bAnd(Nat.blt (cjOf c) 6,
      findPtK R2.cnt R2.T cosQ CP c)),
    allN 5 (fun j => !fixL (RP (j + 1)) (RPI (j + 1))))) = true := by
  quickRfl

theorem k_kcompat : allN 5 (fun j => Nat.beq (cj8 (GH.F 4) (GHI 4) (R2.GI j))
    (wK 243 8 LT (Ly1080.sigmaTxyWords.getD j []))) = true := by
  quickRfl

theorem k_r2s0 : r2Sl 0 = true := by quickRfl

theorem k_r2s1 : r2Sl 1 = true := by quickRfl

theorem k_r2s2 : r2Sl 2 = true := by quickRfl

theorem k_r2s3 : r2Sl 3 = true := by quickRfl

theorem k_r2s4 : r2Sl 4 = true := by quickRfl

theorem k_r2s5 : r2Sl 5 = true := by quickRfl

theorem k_r2s6 : r2Sl 6 = true := by quickRfl

theorem k_r2s7 : r2Sl 7 = true := by quickRfl

theorem k_r2s8 : r2Sl 8 = true := by quickRfl

theorem k_r2s9 : r2Sl 9 = true := by quickRfl

theorem k_r2s10 : r2Sl 10 = true := by quickRfl

theorem k_r2s11 : r2Sl 11 = true := by quickRfl

theorem k_r2s12 : r2Sl 12 = true := by quickRfl

theorem k_r2s13 : r2Sl 13 = true := by quickRfl

theorem k_r2s14 : r2Sl 14 = true := by quickRfl

theorem k_r2s15 : r2Sl 15 = true := by quickRfl

theorem k_r2h : slK R2.cnt (hsortPtKF 243 8 (mask 8) R2.cnt R2.T R2.HS R2.HSI) 0 R2.cnt = true := by
  quickRfl

theorem k_r2cl0 : r2clSl 0 = true := by quickRfl

theorem k_r2cl1 : r2clSl 1 = true := by quickRfl

theorem k_r2cl2 : r2clSl 2 = true := by quickRfl

theorem k_r2cl3 : r2clSl 3 = true := by quickRfl

theorem k_r2cl4 : r2clSl 4 = true := by quickRfl

theorem k_r2cl5 : r2clSl 5 = true := by quickRfl

theorem k_r2cl6 : r2clSl 6 = true := by quickRfl

theorem k_r2cl7 : r2clSl 7 = true := by quickRfl

theorem k_r2cl8 : r2clSl 8 = true := by quickRfl

theorem k_r2cl9 : r2clSl 9 = true := by quickRfl

theorem k_r2cl10 : r2clSl 10 = true := by quickRfl

theorem k_r2cl11 : r2clSl 11 = true := by quickRfl

theorem k_r2cl12 : r2clSl 12 = true := by quickRfl

theorem k_r2cl13 : r2clSl 13 = true := by quickRfl

theorem k_r2cl14 : r2clSl 14 = true := by quickRfl

theorem k_r2cl15 : r2clSl 15 = true := by quickRfl

@[expose] noncomputable def centAt (X : Nat) : Bool :=
  bIf(allN 5 (fun g => Nat.beq (p8 X (R2.GI g)) (p8 (R2.GI g) X)), Nat.beq X id8, true)

theorem k_cent0 : slK R2.cnt (fun i => centAt (R2.T i)) 0 972 = true := by quickRfl
theorem k_cent1 : slK R2.cnt (fun i => centAt (R2.T i)) 972 972 = true := by quickRfl
theorem k_cent2 : slK R2.cnt (fun i => centAt (R2.T i)) 1944 972 = true := by quickRfl
theorem k_cent3 : slK R2.cnt (fun i => centAt (R2.T i)) 2916 972 = true := by quickRfl

end CertificateChecks.KernelLyTr

end
