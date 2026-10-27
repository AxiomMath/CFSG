module

public import Certificates.Kernel.Sp6Insp443.Data
public import Certificates.Data.Sp6Insp443
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelS6I

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Sp6I CFSG.EvenSmallLie.Sp6
  CertificateChecks.KernelLC.Sp6J CFSG.SectionRank.QTK.Insp443.Sp6

@[expose] def candT (k : Nat) : List (List CFSG.Sporadic.Th.Native.Table) :=
  Bool.rec (motive := fun _ => List (List CFSG.Sporadic.Th.Native.Table)) cands7 cands5
    (Nat.blt k 6)

@[expose] def candI (k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Nat.sub k 6) k (Nat.blt k 6)

@[expose] noncomputable def ch725106d (k : Nat) : Bool :=
  strictB (D.cP.getD k 0) (fun C => strictB (D.cI.getD k 0) (fun CI =>
  strictB (D.nU.getD k 0) (fun a => strictB (D.nW.getD k 0) (fun b =>
  bAnd(lettersNK (D.cw.getD k []),
  bAnd(Nat.beq (wordNK 36 6 (mask 6) One36 XQ.S XQ.SI (D.cw.getD k [])) C,
  bAnd(permOK 36 6 (mask 6) (36 * 6) C CI,
  bAnd(canonK 36 6 (mask 6) (36 * 6) C, bAnd(canonK 36 6 (mask 6) (36 * 6) CI,
  bAnd(Nat.beq (lenT ((candT k).getD (candI k) [])) a,
  bAnd(Nat.beq (lenT ((candT k).getD (D.wIdx.getD k 0) [])) b,
  bAnd(tabsPK 36 6 (mask 6) (36 * 6) (D.uT.getD k 0) ((candT k).getD (candI k) []) 0,
  bAnd(tabsPK 36 6 (mask 6) (36 * 6) (D.wT.getD k 0) ((candT k).getD (D.wIdx.getD k 0) []) 0,
  bAnd(conjPK 36 6 (mask 6) (36 * 6) (D.uT.getD k 0) (D.uP.getD k 0) C CI a,
  bAnd(conjPK 36 6 (mask 6) (36 * 6) (D.wT.getD k 0) (D.wP.getD k 0) C CI b,
  bAnd(Nat.blt (D.cls.getD k 0) 4,
  bAnd(Nat.beq (maskPK 36 6 (mask 6) (36 * 6) One36 (D.uP.getD k 0) (D.uM.getD k 0) a)
    (wordK 36 6 (mask 6) One36 XQ.S XQ.SI (sp6InvRepWords.getD (D.cls.getD k 0) [])),
  spanPK 36 6 (mask 6) (36 * 6) One36 (D.wP.getD k 0) (D.sP.getD k 0) b)))))))))))))))))

#kc_each ch725106d 0 12

theorem ch725106cls : D.cls = [2, 2, 2, 2, 2, 2, 1, 1, 3, 3, 3, 3] := by decide +kernel

end CertificateChecks.KernelS6I

end
