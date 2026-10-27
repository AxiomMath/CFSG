module

public import Certificates.Data.Kernel.LocalQT.Pipe
public import Certificates.Kernel.LocalQT.Pipe.D4050
public import Certificates.Kernel.LocalQT.Pipe.D4050c

public section

namespace CFSG.KD.LQT.C4050

open CFSG.KC.LQT.S CFSG.KC.LQT.PP CFSG.QuasithinUnique.Setup.X1

@[expose] noncomputable def famS (c : Nat) : Bool := slpChk 4725 13 TF j2Data.prog (getK SL c)

@[expose] noncomputable def famM (c : Nat) : Bool := omChk 4725 13 TF MF PRK GNK (getK ML c)

@[expose] noncomputable def famE (c : Nat) : Bool :=
  edgeChunk 315 9 13 4725 (codeK 9 (chunksK taC)) (codeK 9 (chunksK tbC)) (TF 0) (TF 1) PRK GNK
    RF (treeOf RL) (c * 315) 315

@[expose] noncomputable def famR (c : Nat) : Bool :=
  repsChunk 4725 13 (qpK TF j2Data.qp) RPK RIK QPK QGK DPK REPS OML (c * 945) 945

@[expose] noncomputable def famB (h : Nat) : Bool :=
  blockK 4725 13 (qpK TF j2Data.qp) MF RPK REPS BM BWL j2Data.xs.toList h

@[expose] noncomputable def famP (i : Nat) : Bool :=
  pairK 4725 13 (qpK TF j2Data.qp) MF RPK REPS BM PWL j2Data.xs.toList i

end CFSG.KD.LQT.C4050

end
