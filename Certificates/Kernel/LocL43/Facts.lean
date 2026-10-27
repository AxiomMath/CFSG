module

public import CFSG.Certificates.Kernel.LocLn.Glue
public import Certificates.Kernel.LocL43.Checks
import CFSG.Certificates.Kernel.PackSetSound

public section

namespace CertificateChecks.KernelLocL43

open CFSG.KD.LocLn CFSG.KS.LocLn CFSG.KC.Enum CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.Loc

theorem ptAll : ∀ i < 512, ptN k4 4 512 G T E PA LA SO SOI i = true := by
  have hb : ∀ q < 8, l43Pt q = true := by
    intro q hq
    interval_cases q
    exacts [l43Pt0, l43Pt1, l43Pt2, l43Pt3, l43Pt4, l43Pt5, l43Pt6, l43Pt7]
  intro i hi
  exact blk_all (L := 64) (Q := 8) (by norm_num) hb i (by omega)

theorem flAll : ∀ i < 512, flagN k4 (T i) = F i := by
  have hb : ∀ q < 8, l43Fl q = true := by
    intro q hq
    interval_cases q
    exacts [l43Fl0, l43Fl1, l43Fl2, l43Fl3, l43Fl4, l43Fl5, l43Fl6, l43Fl7]
  intro i hi
  exact Nat.eq_of_beq_eq_true (blk_all (L := 64) (Q := 8) (by norm_num) hb i (by omega))

theorem prAll : ∀ a < 160, pairN k4 512 38 T O8 O2 CV RX RT 119 a = true := by
  have hb : ∀ q < 40, l43Pr q = true := by
    intro q hq
    interval_cases q
    exacts [l43Pr0, l43Pr1, l43Pr2, l43Pr3, l43Pr4, l43Pr5, l43Pr6, l43Pr7, l43Pr8, l43Pr9,
      l43Pr10, l43Pr11, l43Pr12, l43Pr13, l43Pr14, l43Pr15, l43Pr16, l43Pr17, l43Pr18, l43Pr19,
      l43Pr20, l43Pr21, l43Pr22, l43Pr23, l43Pr24, l43Pr25, l43Pr26, l43Pr27, l43Pr28, l43Pr29,
      l43Pr30, l43Pr31, l43Pr32, l43Pr33, l43Pr34, l43Pr35, l43Pr36, l43Pr37, l43Pr38, l43Pr39]
  intro a ha
  exact blk_all (L := 4) (Q := 40) (by norm_num) hb a (by omega)

theorem rpAll : ∀ i < 38, repAt i l43Data.reps[i]! = true := by
  have hb : ∀ q < 5, l43Rp q = true := by
    intro q hq
    interval_cases q
    exacts [l43Rp0, l43Rp1, l43Rp2, l43Rp3, l43Rp4]
  intro i hi
  have h := blk_all (L := 8) (Q := 5) (by norm_num) hb i (by omega)
  have hb' : Nat.blt i 38 = true := Nat.blt_eq.mpr hi
  rw [hb'] at h
  exact h

theorem inFAll : ∀ i < 38, inF4 l43Data.reps[i]!.g₁ = true ∧ inF4 l43Data.reps[i]!.g₂ = true := by
  intro i hi
  have hi' : i < l43Data.reps.size := by rw [repsSize]; exact hi
  have hm : l43Data.reps[i]! ∈ l43Data.reps.toList := by
    rw [getElem!_pos l43Data.reps i hi']
    exact Array.getElem_mem_toList hi'
  have h := List.all_eq_true.1 inF4B _ hm
  rwa [Bool.and_eq_true] at h

theorem check_true : locCheck 4 inF4 l43Data = true := by
  have hg := gensB
  rw [Bool.and_eq_true] at hg
  obtain ⟨hg1, hg2⟩ := hg
  refine locCheck_of kit4 rfl (m := 4) (N := 512) (NR := 38) (n8 := 160) (n2 := 119)
    (G := G) (T := T) (F := F) (O8 := O8) (O2 := O2) (CV := CV) (RX := RX) (RT := RT)
    (PA := PA) (LA := LA) (SO := SO) (SOI := SOI) (E := E)
    (Nat.eq_of_beq_eq_true hg1) (fun k hk => ?_) (by norm_num) ptAll
    (by rw [fuelK.1]; norm_num) (by rw [fuelK.2]; norm_num) flAll (eq_of_beq o8B) (eq_of_beq o2B)
    prAll repsSize (fun i hi => ?_) inFAll
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

end CertificateChecks.KernelLocL43

end
