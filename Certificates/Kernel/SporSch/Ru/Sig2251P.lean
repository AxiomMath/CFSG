module

public import Certificates.Kernel.SporSch.Ru.Sig2251
public import CFSG.Certificates.Kernel.SporSch.RuVOrbSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuSig

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KC.VecK CFSG.Sporadic.RuSchreier
  CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallF2.Native
  CertificateChecks.KernelSporSch.RuG CertificateChecks.KernelVec.Ru

theorem horb : ∀ h < (CFSG.Sporadic.Ru.Native.ruData ()).n,
    orbAt (CFSG.Sporadic.Ru.Native.ruData ()).d (CFSG.Sporadic.Ru.Native.ruData ()).n NA NB Pt AT
      BT h = true := by
  refine allS_cover (ns := 16) (S := 256) (fun s hs => ?_) (by decide)
  interval_cases s
  exacts [orb_0, orb_1, orb_2, orb_3, orb_4, orb_5, orb_6, orb_7, orb_8, orb_9, orb_10, orb_11,
    orb_12, orb_13, orb_14, orb_15]

theorem hbfs : ∀ h < (CFSG.Sporadic.Ru.Native.ruData ()).n,
    bfsAt (CFSG.Sporadic.Ru.Native.ruData ()).n AT BT FO h = true := by
  refine allS_cover (ns := 16) (S := 256) (fun s hs => ?_) (by decide)
  interval_cases s
  exacts [bfs_0, bfs_1, bfs_2, bfs_3, bfs_4, bfs_5, bfs_6, bfs_7, bfs_8, bfs_9, bfs_10, bfs_11,
    bfs_12, bfs_13, bfs_14, bfs_15]

theorem hsort : ∀ h < (CFSG.Sporadic.Ru.Native.ruData ()).n,
    sortAt (CFSG.Sporadic.Ru.Native.ruData ()).n Pt S IP SP h = true := by
  refine allS_cover (ns := 16) (S := 256) (fun s hs => ?_) (by decide)
  interval_cases s
  exacts [sort_0, sort_1, sort_2, sort_3, sort_4, sort_5, sort_6, sort_7, sort_8, sort_9, sort_10,
    sort_11, sort_12, sort_13, sort_14, sort_15]

theorem tables : ∀ i < 4060,
    ap (CFSG.Sporadic.Ru.Native.ruData.orbit ()).alpha i = lk AT 32 i ∧
      ap (CFSG.Sporadic.Ru.Native.ruData.orbit ()).beta i = lk BT 32 i :=
  vOrbit_tables (CFSG.Sporadic.Ru.Native.ruData ()) hA hB seed (by quickRfl) p0 horb hbfs hsort

theorem sig_eq : ruSigmaA = unpack 4060 12 SIG := by
  have h := hexPackK_sound (by norm_num) (by norm_num) sigK
  rw [← eq] at h
  apply Array.ext
  · simp [ruSigmaA, unpack]
  · intro i h1 h2
    have hi : i < 4060 := by simpa [unpack] using h2
    simp only [ruSigmaA, unpack, Array.getElem_ofFn]
    have e := h i hi
    rw [Nat.zero_add] at e
    exact e

theorem get_unpack {P i : Nat} (hi : i < 4060) : (unpack 4060 12 P)[i]! = pg 12 (mask 12) P i := by
  rw [unpack, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem facts : isInvA 4060 ruSigmaA (invCand 4060 ruSigmaA) = true ∧
    (∀ i < 4060, ruSigmaA[ruA0A[i]!]! =
        ap (CFSG.Sporadic.Ru.Native.ruData.orbit ()).alpha ruSigmaA[i]! ∧
      ruSigmaA[ruA1A[i]!]! = ap (CFSG.Sporadic.Ru.Native.ruData.orbit ()).beta ruSigmaA[i]!) := by
  refine ⟨(inv_of sig_eq pSig).2, fun i hi => ?_⟩
  have hs : pg 12 (mask 12) SIG i < 4060 := by simpa [Nat.blt_eq] using allN_spec sigLt i hi
  have h0 : pg 12 (mask 12) A0 i < 4060 := by simpa [Nat.blt_eq] using allN_spec a0Lt i hi
  have h1 : pg 12 (mask 12) A1 i < 4060 := by simpa [Nat.blt_eq] using allN_spec a1Lt i hi
  obtain ⟨tA, tB⟩ := tables _ hs
  rw [sig_eq, a0_eq, a1_eq, get_unpack hi, get_unpack hi, get_unpack hi, get_unpack h0,
    get_unpack h1, tA, tB]
  exact ⟨Nat.eq_of_beq_eq_true (allN_spec eqA0 i hi), Nat.eq_of_beq_eq_true (allN_spec eqA1 i hi)⟩

end CertificateChecks.KernelSporSch.RuSig

end
