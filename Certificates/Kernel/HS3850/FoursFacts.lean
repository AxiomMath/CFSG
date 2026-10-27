module

public import Certificates.Kernel.HS3850.Fours
public import Certificates.Kernel.HS3850.FusFacts

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HS3850

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.HSAutN CFSG.KC.PkPow CFSG.KD.LQT.C4126
open CFSG.KS.MulH CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.EvenSporadicStandard.HSStd CFSG.EvenSporadicStandard.HypOne
open CFSG.KD.LQT.HO (Cn cIdn)

theorem fours_eq {k : Nat} (hk : k < 2) : natArr (foursTbl k) = unpack 3850 12 (FG.F k) := by
  have h := CFSG.KC.Misc.HexFlat.hexT_sound FG.all (by norm_num) k hk
  rw [← FG.eq] at h
  exact h

theorem fours_tab {k : Nat} (hk : k < 2) : foursTbl k = tabT (unpack 3850 12 (FG.F k)) := by
  rw [← fours_eq hk, tabT_natArr]

theorem fourK_spec {L R : Nat} {w : List Nat} (h : fourK L R w = true) :
    L = wfoldR CFSG.KD.LQT.HN.ls8 w ∧ Cn L ∧ Cn (pinvS 3850 12 (mask 12) L) ∧
      invEqK 3850 12 (mask 12) (3850 * 12) L (pinvS 3850 12 (mask 12) L) = true ∧ Cn R ∧
      Cn (pinvS 3850 12 (mask 12) R) ∧
      invEqK 3850 12 (mask 12) (3850 * 12) R (pinvS 3850 12 (mask 12) R) = true ∧
      ordK (pc (pc (pc L R) (pinvS 3850 12 (mask 12) L)) (pinvS 3850 12 (mask 12) R)) 2 = true := by
  unfold fourK at h
  simp only [CFSG.KS.PEnum.strictB_app', bAnd_iff] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨Nat.eq_of_beq_eq_true h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem foursWit_of {l t : Table}
    {L R : Nat} {w : List Nat} (hw : ∀ x ∈ w, x < 16) (hl : l = tabT (unpack 3850 12 L))
    (ht : t = tabT (unpack 3850 12 R)) (h : fourK L R w = true) :
    foursWitOK 3850 hsSift l t = true := by
  obtain ⟨e, cL, cLI, iL, cR, cRI, iR, hord⟩ := fourK_spec h
  obtain ⟨g, hg, hrep⟩ := CFSG.KD.LQT.HN.rep_word w hw
  rw [← e] at hrep
  have hs : hsSift l = true := by
    rw [hl]
    refine (CFSG.KD.LQT.HN.sift_iff (G := g) ?_).2 hg
    rw [natArr_tabT cL]
    exact hrep
  unfold foursWitOK commTable
  rw [hs, hl, ht, invT_unpack (by norm_num) iL, invT_unpack (by norm_num) iR, compT_pc cL cR,
    compT_pc (cn_pc cL cR) cLI, compT_pc (cn_pc (cn_pc cL cR) cLI) cRI,
    ord_of (cn_pc (cn_pc (cn_pc cL cR) cLI) cRI) hord, permOK_unpack cL iL, permOK_unpack cR iR,
    invOK_unpack cL cLI iL, invOK_unpack cR cRI iR]
  rfl

theorem foursData_true :
    foursData = true := by
  obtain ⟨h0, h1⟩ := (by simpa only [bAnd_iff] using ok25370 :
    fourK (FG.F 0) (HC.F 21) fw0 = true ∧ fourK (FG.F 1) (HC.F 34) fw1 = true)
  unfold foursData
  rw [foursWit_of (by decide) (fours_tab (k := 0) (by norm_num)) (cent_tab (k := 21) (by norm_num)) h0,
    foursWit_of (by decide) (fours_tab (k := 1) (by norm_num)) (cent_tab (k := 34) (by norm_num)) h1]
  rfl

end CFSG.KD.HS3850

end
