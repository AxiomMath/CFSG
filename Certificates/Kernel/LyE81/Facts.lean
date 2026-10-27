module

public import CFSG.Certificates.Kernel.LyE81.Sound
public import Certificates.Kernel.LyE81.Mats
public import Certificates.Kernel.LyE81.Orb
public import Certificates.Kernel.LyE81.Tab
public import Certificates.Kernel.SporSch.Ly.BS18009
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelLyE81

open CFSG.KD.LyE81 CFSG.KS.LyE81K CFSG.KS.ArrBfsSim CFSG.KC.Enum
open CFSG.RankThree.PartTwo.Sec4.Item434SporLy CFSG.RankThree.PartTwo.Sec4.Item434SporE81
open CFSG.Monster.B.Fischer CFSG.Sporadic.He.Native CFSG.KS.SporSch.LyM

local notation "U" X:max => unpackL 111 12 1332 X

theorem orbAll : ∀ q < 27, orbK PT V E PA LA (81 * q) 81 = true := by
  intro q hq
  interval_cases q
  exacts [orbC0, orbC1, orbC2, orbC3, orbC4, orbC5, orbC6, orbC7, orbC8, orbC9, orbC10, orbC11,
    orbC12, orbC13, orbC14, orbC15, orbC16, orbC17, orbC18, orbC19, orbC20, orbC21, orbC22, orbC23,
    orbC24, orbC25, orbC26]

theorem sortAll : ∀ q < 27, CFSG.KD.LyE81.sortK V SO SOI (81 * q) 81 = true := by
  intro q hq
  interval_cases q
  exacts [sortC0, sortC1, sortC2, sortC3, sortC4, sortC5, sortC6, sortC7, sortC8, sortC9, sortC10,
    sortC11, sortC12, sortC13, sortC14, sortC15, sortC16, sortC17, sortC18, sortC19, sortC20,
    sortC21, sortC22, sortC23, sortC24, sortC25, sortC26]

theorem vVal : lyE81.v = UV (V 0) := by
  have h := List.all_eq_true.1 vEq
  apply Array.ext (by rw [vSz, UV_size])
  intro j h1 h2
  have hj : j < 111 := by rw [vSz] at h1; exact h1
  rw [← getElem!_pos lyE81.v j h1, ← getElem!_pos (UV (V 0)) j h2, UV_get hj]
  exact (Nat.eq_of_beq_eq_true (h j (List.mem_range.2 hj))).symm

theorem lyE81Check_true :
    lyE81Check lyE81 CFSG.Sporadic.Ly.Native.matA CFSG.Sporadic.Ly.Native.matB = true := by
  have vA := CertificateChecks.KernelSporSch.LyBS.vA
  have vB := CertificateChecks.KernelSporSch.LyBS.vB
  have vC : CFSG.KD.LyS0.vld C = true := by
    have := CFSG.KS.allBlk_spec vM 0 (by norm_num)
    exact this
  have vD : CFSG.KD.LyS0.vld D = true := by
    have := CFSG.KS.allBlk_spec vM 1 (by norm_num)
    exact this
  have hslp := slpM_eq vA vB slp1 slp2 slp3 slp4
  obtain ⟨hPsz, hPk⟩ := P_eq (X := lyE81) (PK := PK) vC vD pWsz letters words
  have htr : ∀ k < 7, trK (PK k) (PT k) = true := fun k hk => by
    have := CFSG.KS.allBlk_spec tr k hk
    rwa [Nat.add_eq, Nat.zero_add] at this
  obtain ⟨T, hvld⟩ := tables_of (fun k hk => (hPk k hk).1) htr orbAll sortAll
  have hbfs : orbCert (lyE81.pW.map (evalWord #[U C, U D])) lyE81.v lyE81.fuel =
      cert 7 2187 (fun i => UV (V i)) E PA LA := by
    unfold orbCert
    rw [hPsz, vVal, fuelEq]
    exact arrBfs_eq T (by norm_num)
  have h2 := pcCheck_of hPsz hPk pc
  have h3 := orbitOK_of hPsz T hvld vVal
  have h4 : tabCheck 7 2187 (cert 7 2187 (fun i => UV (V i)) E PA LA).edges
      (cert 7 2187 (fun i => UV (V i)) E PA LA).par (cert 7 2187 (fun i => UV (V i)) E PA LA).lab
      lyE81.idZ lyE81.sets = true := by
    rw [tabCheck_eq]
    exact tab
  rw [CertificateChecks.KernelSporSch.LyBSF.matA_eq, CertificateChecks.KernelSporSch.LyBSF.matB_eq]
  unfold lyE81Check
  simp only [hslp, hbfs, letters, h2, h3, h4, Bool.and_self]

end CertificateChecks.KernelLyE81

end
