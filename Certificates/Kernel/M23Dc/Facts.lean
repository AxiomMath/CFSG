module

public import Certificates.Kernel.M23Dc.Final
public import CFSG.Quasithin.Background.HSporLatM23Sg
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.M23Dc

open CFSG.QuasithinUnique.Ch1.SporLat

theorem m23Sg_eq_lat : m23Sg = CFSG.Quasithin.H.MathieuLat.m23Sg := rfl

theorem m23K_mw_eq : m23LatK.mw = CFSG.Quasithin.A312M23.m23MwLit := by
  change J.mw.toArray = _
  apply eq_of_beq
  quickRfl


theorem m23K_Y_eq (j : ℕ) : m23CtxK.Y j = CFSG.Quasithin.H.MathieuLat.m23Member j := by
  unfold LatCtx.Y LatCtx.gens CFSG.Quasithin.H.MathieuLat.m23Member
  rw [m23K_D_mw, m23K_mw_eq]
  rfl

theorem m23K_S_eq : m23CtxK.S = CFSG.Quasithin.H.MathieuLat.m23SylTwo :=
  m23CtxK.hSeq.symm

end CFSG.KD.M23Dc

end
