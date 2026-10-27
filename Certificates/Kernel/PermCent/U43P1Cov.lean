module

public import Certificates.Kernel.PermCent.U43P1Tab
public import Certificates.Data.Kernel.PermCent.U43P1Chk
public import Certificates.Data.Kernel.PermCent.U43P1W
public import Certificates.Kernel.PermCent.U43P1A6
public import Certificates.Kernel.PermCent.U43P1Cen
public import Certificates.Kernel.PermCent.U43P1S

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelPermCent.U43P1

open CFSG.ComponentClassification.HarrisLit.P1.U43.Cover CFSG.KC.Enum CFSG.KS

theorem cover :
    (coverOK SM1.T clsT clsN [0, 1, 2] covM1 && coverOK SF.T clsT clsN [0, 3, 4] covF &&
      coverOK SI.T clsT clsN [0, 5] covI) = true ∧
    covM1.length = 256 ∧ covF.length = 256 ∧ covI.length = 256 := by
  decide +kernel

theorem look :
    (isId (pc (pk cM1 false) (pk cM1 false)) && isId (pc (pk cI true) (pk cI true)) &&
      isId (pc (pk cDi true) (pk cDi true)) &&
      lookOK (pk cM1 false) clsT clsN [0, 1, 2] [(0, clsR 0), (1, clsR 1), (2, clsR 2)] lkM1 &&
      lookOK (pk cI true) clsT clsN [0, 3, 4] [(0, clsR 0), (3, clsR 3), (4, clsR 4)] lkF &&
      lookOK (pk cDi true) clsT clsN [0, 5] [(0, clsR 0), (5, clsR 5)] lkI) = true := by
  decide +kernel

theorem dconj :
    (isId (pc (pk cDi false) (pk cDmi false)) &&
      Nat.beq (pc (pk cDi false) (pc (pk cI true) (pk cDmi false))) (pk cM1 true) &&
      Nat.beq (pc (pk cDi false) (pc (pk cDi true) (pk cDmi false))) (pk cDmi true)) = true := by
  decide +kernel

@[expose] noncomputable def ordP (p g : ℕ) : Bool :=
  !isId g && cond (Nat.beq p 3) (isId (pc g (pc g g))) (isId (pc g (pc g (pc g (pc g g)))))

@[expose] noncomputable def normOK (CG CGI LG LT : ℕ → ℕ) (W : List ℕ) (NL : ℕ) : Bool :=
  Nat.beq W.length 4 && ((List.range 4).all fun i =>
    Nat.blt (W.getD i 0) NL &&
      Nat.beq (pc (CG (i / 2)) (pc (LG (i % 2)) (CGI (i / 2)))) (LT (W.getD i 0)))

theorem small :
    ((List.range 2).all (fun j => commOK (CgIn.G j) (clsT 0 (clsR 0)) &&
      commOK (KIn.G j) (clsT 0 (clsR 0))) &&
      normOK CgIn.G CgIn.GI KIn.G KIn.T nmIn 288) = true := by
  decide +kernel

theorem five :
    ((List.range 2).all fun j => commOK (FFb.G j) (clsT 4 (clsR 4)) && ordP 5 (FFb.G j)) =
      true := by
  decide +kernel

theorem a6 :
    ((List.range 2).all (fun j => commOK (CgM1a.G j) (clsT 1 (clsR 1)) &&
      commOK (LM1a.G j) (clsT 1 (clsR 1)) && commOK (CgIa.G j) (clsT 5 (clsR 5)) &&
      commOK (LIa.G j) (clsT 5 (clsR 5))) &&
      normOK CgM1a.G CgM1a.GI LM1a.G LM1a.T nmM1a 360 &&
      normOK CgIa.G CgIa.GI LIa.G LIa.T nmIa 360 &&
      ordP 3 (LM1a.G 0) && ordP 5 (LM1a.G 1) && ordP 3 (LIa.G 0) && ordP 5 (LIa.G 1) &&
      ((List.range 360).all fun j => invL.contains j || (!invol (LM1a.T j) && !invol (LIa.T j))))
      = true := by
  decide +kernel

end CertificateChecks.KernelPermCent.U43P1

end
