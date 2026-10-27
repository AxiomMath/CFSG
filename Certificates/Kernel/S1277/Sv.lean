module

public import Certificates.Data.Kernel.S1277KSv
public import Certificates.Kernel.S1277.ModData
public import Certificates.Kernel.S1277.LatData
public import Certificates.Kernel.S1277.FrData
public import Certificates.Kernel.S1277.SvData
public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Lce
import CFSG.Certificates.Kernel.Common.EachTrue

public section

namespace CFSG.KP.S1277Sv

open CFSG.KC.S1277Lat CFSG.KC.S1277Mod CFSG.KC.S1277Sv CFSG.KD.S1277Mod CFSG.KD.S1277Lat
  CFSG.KD.S1277Fr CFSG.KD.S1277Sv

noncomputable abbrev Mn : Mdl := ⟨48, apn, cpn, ipn, onen⟩

theorem sv_s : sChk Mn kgn (sgcn.getD 4 0) (sgwn.getD 4 []) sg sl sp sj sd = true := by quickRfl

theorem sv_p : pChk sl pl pi = true := by quickRfl

theorem sv_vg : vgChk (sgln.getD 4 0) [] vg = true := by quickRfl

theorem sv_hp : hpChk vg sl sp36 hp = true := by quickRfl

theorem sv_cnt : cntChk vr vb = true := by quickRfl

theorem sv_vr : vr.length = 40 := by decide +kernel

#kc_each CFSG.KP.S1277Sv ch589103cov (covChk sp36 hp vt sl a1 a2 vr vb) 0 40

theorem sv_wS : allLt 130 (wSChk pl sg vg vt vw) = true := by quickRfl

theorem sv_wA1 : allLt 130 (wAChk pl sg vg vt k1 2 w1) = true := by quickRfl

theorem sv_wA2 : allLt 130 (wAChk pl sg vg vt k2 3 w2) = true := by quickRfl

theorem sv_a1 : aChk1 sg sl vg vt k1 2 a1 a1p a1j a1d = true := by quickRfl

theorem sv_a2 : aChk1 sg sl vg vt k2 3 a2 a2p a2j a2d = true := by quickRfl

theorem neg_s : CFSG.KC.notB (sChk Mn kgn (sgcn.getD 4 0) (sgwn.getD 4 []) (sg.set 0 (sg.getD 0 0 ^^^ 64))
    sl sp sj sd) = true := by quickRfl

theorem neg_s2 : CFSG.KC.notB (sChk Mn kgn (sgcn.getD 4 0) (sgwn.getD 4 []) sg sl sp
    (sj.set 5 ((sj.getD 5 0 + 1) % 9)) sd) = true := by quickRfl

theorem neg_p : CFSG.KC.notB (pChk sl (pl.set 7 (sl.getD 23 0)) pi) = true := by quickRfl

theorem neg_vg : CFSG.KC.notB (vgChk (sgln.getD 4 0) [] (vg.set 3 (vg.getD 3 0 ^^^ 1))) = true := by
  quickRfl

theorem neg_hp : CFSG.KC.notB (hpChk vg sl sp36 (hp ^^^ 2 ^ (36 * 100))) = true := by quickRfl

theorem neg_cov : CFSG.KC.notB (covChk sp36 hp vt sl a1 a2 (vr.set 3 ((vr.getD 3 []).dropLast)) vb 3) =
    true := by quickRfl

theorem neg_cov2 : CFSG.KC.notB (covChk sp36 hp vt sl a1 a2
    (vr.set 5 (((vr.getD 5 []).getD 1 0) :: ((vr.getD 5 []).getD 0 0) :: (vr.getD 5 []).drop 2))
    vb 5) = true := by quickRfl

theorem neg_cov3 : CFSG.KC.notB (covChk sp36 hp (vt ^^^ 3) sl a1 a2 vr vb 0) = true := by quickRfl

theorem neg_cnt : CFSG.KC.notB (cntChk (vr.set 0 []) vb) = true := by quickRfl

theorem neg_wS : CFSG.KC.notB (allLt 130 (wSChk pl sg vg vt
    (vw.set 1 ((vw.getD 1 []).dropLast)))) = true := by quickRfl

theorem neg_wA1 : CFSG.KC.notB (allLt 130 (wAChk pl sg vg vt k1 2
    (w1.set 1 ((w1.getD 1 []).dropLast)))) = true := by quickRfl

theorem neg_a1 : CFSG.KC.notB (aChk1 sg sl vg vt k1 2 (a1.drop 1) a1p a1j a1d) = true := by quickRfl

theorem neg_a2 : CFSG.KC.notB (aChk1 sg sl vg vt k2 3 a2 (a2p.set 100 100) a2j a2d) = true := by
  quickRfl

theorem neg_a3 : CFSG.KC.notB (aChk1 sg sl vg vt k2 2 a1 a1p a1j a1d) = true := by quickRfl

end CFSG.KP.S1277Sv

end
