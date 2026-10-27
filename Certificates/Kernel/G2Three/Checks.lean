module

public import Certificates.Data.Kernel.G2Three.Defs
public import Certificates.Kernel.G2Three.Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.G2Three

open CFSG.KC.Ord

theorem consts_ok : consts3OK 14 5 196 LO RM CI ONE UP = true := by quickRfl

theorem one_ok : (Nat.beq (XX 0) ONE && Nat.beq (XS 0) ONE && Nat.beq (XP 0) ONE) = true := by
  quickRfl

theorem buildX_ok : buildK XX GX PAX PBX 576 5 9 = true := by quickRfl
theorem stepX_ok : stepK XX GX PAX PBX CX POSX 576 5 45 = true := by quickRfl
theorem sortX_ok : sortK XX SRTX SRIX 576 9 = true := by quickRfl

theorem buildS_ok : buildK XS GS PAS PBS 64 5 1 = true := by quickRfl
theorem stepS_ok : stepK XS GS PAS PBS CS POSS 64 5 5 = true := by quickRfl
theorem sortS_ok : sortK XS SRTS SRIS 64 1 = true := by quickRfl

theorem buildP_ok : buildK XP GP PAP PBP 9 2 1 = true := by quickRfl
theorem stepP_ok : stepK XP GP PAP PBP CP POSP 9 2 1 = true := by quickRfl
theorem sortP_ok : sortK XP SRTP SRIP 9 1 = true := by quickRfl

theorem orbO_ok : orbK XO GA GB OA OB 7371 4 116 = true := by quickRfl
theorem sortO_ok : sortK XO SRTO SRIO 7371 116 = true := by quickRfl

theorem inv_ok : invK XS XO IDX 64 7371 1 = true := by quickRfl
theorem cent_ok : centK XX (GX 0) (GX 2) (XO 0) 576 9 = true := by quickRfl
theorem comm_ok : commK GX (XO 0) 5 = true := by quickRfl
theorem cube_ok : cubeK GA 4 = true := by quickRfl

end CFSG.KD.G2Three

end
