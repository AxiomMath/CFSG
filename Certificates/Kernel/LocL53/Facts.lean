module

public import CFSG.Certificates.Kernel.LocLn.Glue
public import Certificates.Kernel.LocL53.Pts
public import Certificates.Kernel.LocL53.Pairs
public import Certificates.Kernel.LocL53.Reps
import CFSG.Certificates.Kernel.PackSetSound

public section

namespace CertificateChecks.KernelLocL53

open CFSG.KD.LocLn CFSG.KS.LocLn CFSG.KC.Enum CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.Loc

theorem ptAll : ∀ i < 1024, ptN k5 7 1024 G T E PA LA SO SOI i = true := by
  have hb : ∀ q < 16, l53Pt q = true := by
    intro q hq
    interval_cases q
    exacts [l53Pt0, l53Pt1, l53Pt2, l53Pt3, l53Pt4, l53Pt5, l53Pt6, l53Pt7, l53Pt8, l53Pt9,
      l53Pt10, l53Pt11, l53Pt12, l53Pt13, l53Pt14, l53Pt15]
  intro i hi
  exact blk_all (L := 64) (Q := 16) (by norm_num) hb i (by omega)

theorem flAll : ∀ i < 1024, flagN k5 (T i) = F i := by
  have hb : ∀ q < 16, l53Fl q = true := by
    intro q hq
    interval_cases q
    exacts [l53Fl0, l53Fl1, l53Fl2, l53Fl3, l53Fl4, l53Fl5, l53Fl6, l53Fl7, l53Fl8, l53Fl9,
      l53Fl10, l53Fl11, l53Fl12, l53Fl13, l53Fl14, l53Fl15]
  intro i hi
  exact Nat.eq_of_beq_eq_true (blk_all (L := 64) (Q := 16) (by norm_num) hb i (by omega))

theorem prAll : ∀ a < 416, pairN k5 1024 67 T O8 O2 CV RX RT 167 a = true := by
  have hb : ∀ q < 104, l53Pr q = true := by
    intro q hq
    interval_cases q
    exacts [l53Pr0, l53Pr1, l53Pr2, l53Pr3, l53Pr4, l53Pr5, l53Pr6, l53Pr7, l53Pr8, l53Pr9,
      l53Pr10, l53Pr11, l53Pr12, l53Pr13, l53Pr14, l53Pr15, l53Pr16, l53Pr17, l53Pr18, l53Pr19,
      l53Pr20, l53Pr21, l53Pr22, l53Pr23, l53Pr24, l53Pr25, l53Pr26, l53Pr27, l53Pr28, l53Pr29,
      l53Pr30, l53Pr31, l53Pr32, l53Pr33, l53Pr34, l53Pr35, l53Pr36, l53Pr37, l53Pr38, l53Pr39,
      l53Pr40, l53Pr41, l53Pr42, l53Pr43, l53Pr44, l53Pr45, l53Pr46, l53Pr47, l53Pr48, l53Pr49,
      l53Pr50, l53Pr51, l53Pr52, l53Pr53, l53Pr54, l53Pr55, l53Pr56, l53Pr57, l53Pr58, l53Pr59,
      l53Pr60, l53Pr61, l53Pr62, l53Pr63, l53Pr64, l53Pr65, l53Pr66, l53Pr67, l53Pr68, l53Pr69,
      l53Pr70, l53Pr71, l53Pr72, l53Pr73, l53Pr74, l53Pr75, l53Pr76, l53Pr77, l53Pr78, l53Pr79,
      l53Pr80, l53Pr81, l53Pr82, l53Pr83, l53Pr84, l53Pr85, l53Pr86, l53Pr87, l53Pr88, l53Pr89,
      l53Pr90, l53Pr91, l53Pr92, l53Pr93, l53Pr94, l53Pr95, l53Pr96, l53Pr97, l53Pr98, l53Pr99,
      l53Pr100, l53Pr101, l53Pr102, l53Pr103]
  intro a ha
  exact blk_all (L := 4) (Q := 104) (by norm_num) hb a (by omega)

theorem rpAll : ∀ i < 67, repAt i l53Data.reps[i]! = true := by
  have hb : ∀ q < 9, l53Rp q = true := by
    intro q hq
    interval_cases q
    exacts [l53Rp0, l53Rp1, l53Rp2, l53Rp3, l53Rp4, l53Rp5, l53Rp6, l53Rp7, l53Rp8]
  intro i hi
  have h := blk_all (L := 8) (Q := 9) (by norm_num) hb i (by omega)
  have hb' : Nat.blt i 67 = true := Nat.blt_eq.mpr hi
  rw [hb'] at h
  exact h

theorem check_true : locCheck 5 inF5 l53Data = true := by
  have hg := gensB
  rw [Bool.and_eq_true] at hg
  obtain ⟨hg1, hg2⟩ := hg
  refine locCheck_of kit5 rfl (m := 7) (N := 1024) (NR := 67) (n8 := 416) (n2 := 167)
    (G := G) (T := T) (F := F) (O8 := O8) (O2 := O2) (CV := CV) (RX := RX) (RT := RT)
    (PA := PA) (LA := LA) (SO := SO) (SOI := SOI) (E := E)
    (Nat.eq_of_beq_eq_true hg1) (fun k hk => ?_) (by norm_num) ptAll
    (by rw [fuelK.1]; norm_num) (by rw [fuelK.2]; norm_num) flAll (eq_of_beq o8B) (eq_of_beq o2B)
    prAll repsSize (fun i hi => ?_) (fun i hi => ⟨rfl, rfl⟩)
  · have e := CFSG.KC.Pack.allBlk_spec hg2 k hk
    rw [Nat.add_eq, Nat.zero_add] at e
    exact CFSG.KC.Pack.band_iff.1 e
  · have h := rpAll i hi
    unfold repAt at h
    simp only [CFSG.KC.Pack.strictB_eq] at h
    obtain ⟨r1, h⟩ := CFSG.KC.Pack.band_iff.1 h
    obtain ⟨r2, h⟩ := CFSG.KC.Pack.band_iff.1 h
    obtain ⟨r3, h⟩ := CFSG.KC.Pack.band_iff.1 h
    obtain ⟨r4, r5⟩ := CFSG.KC.Pack.band_iff.1 h
    exact ⟨r1, r2, r3, r4, r5⟩

end CertificateChecks.KernelLocL53

end
