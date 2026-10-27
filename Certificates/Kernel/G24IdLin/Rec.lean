module

public meta import Lean
meta import Certificates.Data.G24IdentLin
public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import CFSG.Open.LocalVocabulary

namespace CFSG.KD.G24Id.Gen

open CFSG.Quasithin.St84.G24Lin CFSG.Quasithin.St84.G24Ident

meta def rowsOf (A : ZMat) (r c : Nat) : List Nat :=
  (List.range r).map fun i =>
    (List.range c).foldl (fun acc j => if zent A i j = 1 then acc ||| (1 <<< j) else acc) 0

meta def sysData (n d r : Nat) (M K P Y : ZMat) : List Nat :=
  rowsOf P d n ++ rowsOf K n d ++ rowsOf Y n r ++ rowsOf M r n

meta def dc : List Nat :=
  sysData 16 2 32 (mComm ((gZ2 ()).getD 0 #[]) ((gZ2 ()).getD 1 #[])) (kComm ((gN2 ()).getD 2 #[]))
    (ofBits pComm) (ofBits yComm)

meta def dq1 : List Nat :=
  sysData 72 2 216 (mQuad 8 2 (gV1 ()) (gZ1 ()))
    (kQuad 2 (qVec 8 2 q1lin q1c) ((gZ1 ()).getD 2 #[])) (ofBits pQuad1) (ofBits yQuad1)

meta def dq2 : List Nat :=
  sysData 84 2 252 (mQuad 6 4 (gV2 ()) (gZ2 ()))
    (kQuad 4 (qVec 6 4 q2lin q2c) ((gN2 ()).getD 2 #[])) (ofBits pQuad2) (ofBits yQuad2)

meta def dh1 : List Nat :=
  sysData 48 16 96 (mFox 8 2 (gV1 ()) (gZ1 ())) (kFox 8 2 (gV1 ()) (gZ1 ())) (ofBits pH11)
    (ofBits yH11)

meta def dh2 : List Nat :=
  sysData 72 24 144 (mFox 6 4 (gV2 ()) (gZ2 ())) (kFox 6 4 (gV2 ()) (gZ2 ())) (ofBits pH12)
    (ofBits yH12)

meta def de : List Nat :=
  sysData 24 10 48 (mExt (gU2 ()) (gN2 ())) (kExt (gU2 ()) (gN2 ()) (gX0 ())) (ofBits pExt2)
    (ofBits yExt2)

meta def db : List Nat :=
  [(gV1 (), 8), (gZ1 (), 2), (gV2 (), 6), (gZ2 (), 4)].flatMap fun (G, n) =>
    (List.range 3).flatMap fun t => rowsOf (G.getD t #[]) n n

end CFSG.KD.G24Id.Gen

#kss_ntree CFSG.KD.G24Id.DB CFSG.KD.G24Id.Gen.db

#kss_ntree CFSG.KD.G24Id.DC CFSG.KD.G24Id.Gen.dc
#kss_ntree CFSG.KD.G24Id.DQ1 CFSG.KD.G24Id.Gen.dq1
#kss_ntree CFSG.KD.G24Id.DQ2 CFSG.KD.G24Id.Gen.dq2
#kss_ntree CFSG.KD.G24Id.DH1 CFSG.KD.G24Id.Gen.dh1
#kss_ntree CFSG.KD.G24Id.DH2 CFSG.KD.G24Id.Gen.dh2
#kss_ntree CFSG.KD.G24Id.DE CFSG.KD.G24Id.Gen.de
