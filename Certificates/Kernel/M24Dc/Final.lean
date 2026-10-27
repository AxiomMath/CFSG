module

public import Certificates.Kernel.M24Dc.Checks
public import Certificates.Kernel.M24Dc.C0
public import Certificates.Kernel.M24Dc.C1
public import Certificates.Kernel.M24Dc.C2
public import Certificates.Kernel.M24Dc.C3
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24DcInputs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.M24Dc

open CFSG.KC.SLDc CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.M24

theorem rc_len : D.Rc.length = 8 := rfl

theorem chunks : (List.range D.Rc.length).all (chunkOK C D) = true := by
  rw [rc_len, List.all_eq_true]
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact K0.all 0 (by decide)
  · exact K0.all 1 (by decide)
  · exact K1.all 0 (by decide)
  · exact K1.all 1 (by decide)
  · exact K2.all 0 (by decide)
  · exact K2.all 1 (by decide)
  · exact K3.all 0 (by decide)
  · exact K3.all 1 (by decide)

theorem dc_ok : dcCheck C D = true := by
  unfold dcCheck
  rw [glob, pts, orbs, chunks]
  rfl

theorem sepB : (J.sep == sepL) = true := by quickRfl

theorem mw0B : (J.mw.getD 0 [] == []) = true := by quickRfl

theorem mwLenB : (J.mw.length == 13) = true := by quickRfl

theorem omB : (m24LatK.Om.map (fun o => o.lbl.size) ==
    #[1, 315, 63, 135, 21, 9, 21, 3, 3, 3, 9, 3, 9]) = true := by
  quickRfl

theorem otB : (m24OtK.map (fun o => o.lbl.size) ==
    #[1, 64, 16, 16, 8, 4, 8, 2, 2, 2, 4, 2, 4]) = true := by
  quickRfl

theorem facts : M24DcFacts :=
  ⟨dc_ok, eq_of_beq tabsB, tabs, invs, eq_of_beq sepB, mws, eq_of_beq mw0B,
    Nat.eq_of_beq_eq_true mwLenB, mems, ots, fix, move, top, eq_of_beq omB,
    eq_of_beq otB⟩

end CFSG.KD.M24Dc

end
