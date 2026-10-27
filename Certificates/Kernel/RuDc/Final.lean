module

public import Certificates.Kernel.RuDc.Glob
public import Certificates.Kernel.RuDc.G0
public import Certificates.Kernel.RuDc.G1
public import Certificates.Kernel.RuDc.G2
public import Certificates.Kernel.RuDc.G3
public import Certificates.Kernel.RuDc.G4
public import Certificates.Kernel.RuDc.G5
public import Certificates.Kernel.RuDc.G6
public import Certificates.Kernel.RuDc.G7
public import Certificates.Kernel.RuDc.G8
public import Certificates.Kernel.RuDc.G9
public import Certificates.Kernel.E68Spor4215.Final
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRuDcInputs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.RuDc

open CFSG.KC.SLDc CFSG.KC.E64F CFSG.KC.SLOm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.RuCert CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Sporadic.Ru.Native (ruData)

theorem ch_of {f : Nat → Bool} {o c : Nat} (hf : ∀ i, f i = chunkOK C D (Nat.add o i))
    (h : ∀ i < c, f i = true) {i : Nat} (h1 : o ≤ i) (h2 : i < o + c) : chunkOK C D i = true := by
  have e : Nat.add o (i - o) = i := by simp only [Nat.add_eq]; omega
  have := h (i - o) (by omega)
  rw [hf, e] at this
  exact this

theorem rc_lenB : (D.Rc.length == 847) = true := by
  quickRfl

theorem rc_len : D.Rc.length = 847 := Nat.eq_of_beq_eq_true rc_lenB

theorem chunks_ok : (List.range D.Rc.length).all (chunkOK C D) = true := by
  rw [rc_len, List.all_eq_true]
  intro i hi
  rw [List.mem_range] at hi
  by_cases h0 : i < 388
  · exact ch_of (o := 0) (fun _ => rfl) G0.all (by omega) (by omega)
  by_cases h1 : i < 744
  · exact ch_of (o := 388) (fun _ => rfl) G1.all (by omega) (by omega)
  by_cases h2 : i < 827
  · exact ch_of (o := 744) (fun _ => rfl) G2.all (by omega) (by omega)
  by_cases h3 : i < 836
  · exact ch_of (o := 827) (fun _ => rfl) G3.all (by omega) (by omega)
  by_cases h4 : i < 837
  · exact ch_of (o := 836) (fun _ => rfl) G4.all (by omega) (by omega)
  by_cases h5 : i < 839
  · exact ch_of (o := 837) (fun _ => rfl) G5.all (by omega) (by omega)
  by_cases h6 : i < 842
  · exact ch_of (o := 839) (fun _ => rfl) G6.all (by omega) (by omega)
  by_cases h7 : i < 844
  · exact ch_of (o := 842) (fun _ => rfl) G7.all (by omega) (by omega)
  by_cases h8 : i < 846
  · exact ch_of (o := 844) (fun _ => rfl) G8.all (by omega) (by omega)
  · exact ch_of (o := 846) (fun _ => rfl) G9.all (by omega) (by omega)

theorem dc_ok : dcCheck C D = true := by
  unfold dcCheck
  rw [glob, pts, orbs, chunks_ok]
  rfl

theorem good_letters : ∀ l < 8, Good ruData.n ruSLPL[nodes.getD l 0]! (C.L l) := by
  intro l hl
  have hj : nodes.getD l 0 < ruProg.length + 2 := by interval_cases l <;> decide
  rw [CFSG.KD.E68S4215.ru_SLPL]
  have hc : J.lc.getD l 0 = CFSG.KD.LQT.C4143.TF (nodes.getD l 0) :=
    Nat.eq_of_beq_eq_true (all_range codes l hl)
  have e : C.L l = CFSG.KC.LQT.PW.imgW 12 (CFSG.KD.LQT.C4143.TF (nodes.getD l 0)) := by
    funext p
    change CFSG.KC.LQT.PW.imgW 12 (J.lc.getD l 0) p = _
    rw [hc]
  rw [e]
  exact CFSG.KD.E68S4215.good_ru hj

theorem mwB : (D.mw == ruMw.toList) = true := by
  quickRfl

theorem sepB : (D.sep == ruB) = true := by
  quickRfl

theorem omB : (ruLatK.Om.map (fun o => o.lbl.size) == #[1, 15, 21, 3, 3]) = true := by
  quickRfl

theorem otB : (ruOtK.map (fun o => o.lbl.size) == #[1, 8, 8, 2, 2]) = true := by
  quickRfl

theorem facts : RuDcFacts :=
  ⟨⟨dc_ok, invs, eq_of_beq mwB, good_letters⟩, eq_of_beq sepB, rfl, rfl, eq_of_beq omB, mems,
    eq_of_beq otB, incl⟩

end CFSG.KD.RuDc

end
