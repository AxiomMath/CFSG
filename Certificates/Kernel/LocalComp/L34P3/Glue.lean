module

public import Certificates.Kernel.LocalComp.L34P3.Chk
public import Certificates.Kernel.LocalComp.L34T1.Glue
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsI22CertInputs
import CFSG.Certificates.Kernel.L34GraphSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34P3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34KSnd
open CFSG.KC.L34Scan2 CFSG.KC.L34W
open CFSG.KS.PEnum (GensOK)
open CertificateChecks.KernelLC.L34Para CertificateChecks.KernelLC.L34T1
open CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ASVolI
open CFSG.KLie.CT (andB orB notB)

theorem o2_of {ws : List (List Nat)} {G : Nat → Nat} {inU : Nat → Bool}
    (hg : GensOK 42 6 3 G (wordTabs ws)) (hi : p3InvK G = true) (h : p3O2K G inU = true) :
    burnsideI22P3_o2Check ws inU = true := by
  obtain ⟨hsz, hb⟩ := hg
  have hc : ∀ k < 3, Cn (G k) ∧ Cn (pinvS 42 6 (mask 6) (G k)) ∧
      pcomp 42 6 (mask 6) (G k) (pinvS 42 6 (mask 6) (G k)) = pidn 42 6 := fun k hk => by
    have h' := allN' hi k hk
    rw [sapp] at h'
    obtain ⟨c, e⟩ := andB_iff.1 h'
    exact ⟨(hb k hk).2, c, Nat.eq_of_beq_eq_true e⟩
  have hI := invsOK_of_pcomp (GI := fun k => pinvS 42 6 (mask 6) (G k)) hsz
    (fun k hk => (hb k hk).1) hc
  unfold burnsideI22P3_o2Check
  dsimp only
  rw [rT.1, hI.2, Bool.true_and, CFSG.KS.BfsReplay.allBelow_iff]
  intro k hk
  rw [Bool.or_eq_true]
  rcases orB_iff.1 (allN' h k hk) with h1 | h1
  · exact Or.inl h1
  · right
    rw [sapp] at h1
    obtain ⟨j, hj, hf⟩ := ex_of_notB_allN h1
    rw [sapp] at hf
    obtain ⟨cg, cgi, -⟩ := hc j hj
    obtain ⟨ck, ek⟩ := htg k
    rw [anyBelow_iff, hsz]
    refine ⟨j, hj, ?_⟩
    unfold conjTab
    rw [hI.1 j hj, (hb j hj).1, ek, comp_unpack' cg ck, comp_unpack' (canonK_pcomp cg ck) cgi]
    exact CFSG.KC.L34K.notIn_sound rfl (canonK_pcomp (canonK_pcomp cg ck) cgi) rT.2.2.1 (nf_of hf)

theorem trans_of {ws : List (List Nat)} {P : Nat → Nat} {inU : Nat → Bool} {k₀ : Nat}
    (hr : (enumBFS 42 (wordTabs ws) 960).tabs = pts 42 6 960 P ∧
      enumOK 42 (wordTabs ws) (enumBFS 42 (wordTabs ws) 960) = true ∧
      ∀ i < 960, canonK 42 6 (mask 6) (42 * 6) (P i) = true)
    (hu : inU k₀ = true) (h0 : k₀ ≠ 0) (h : p3TransK 960 P inU k₀ = true) :
    burnsideI22P3_transCheck ws inU k₀ = true := by
  unfold burnsideI22P3_transCheck
  dsimp only
  unfold p3TransK at h
  rw [sapp] at h
  obtain ⟨c0, e0⟩ := htg k₀
  have hk0 : (k₀ != 0) = true := bne_iff_ne.2 h0
  simp only [hr.2.1, hr.1, size_pts, hu, hk0, beq_self_eq_true, Bool.true_and]
  rw [CFSG.KS.BfsReplay.allBelow_iff]
  intro k hk
  rw [Bool.or_eq_true, Bool.or_eq_true]
  rcases orB_iff.1 (allN' h k hk) with h1 | h1
  · exact Or.inl (Or.inl (by rw [notB_iff.1 h1]; rfl))
  rcases orB_iff.1 h1 with h2 | h2
  · exact Or.inl (Or.inr (by rw [Nat.eq_of_beq_eq_true h2]; rfl))
  right
  rw [sapp] at h2
  obtain ⟨i, hi, hf⟩ := ex_of_notB_allN h2
  rw [sapp] at hf
  obtain ⟨ck, ek⟩ := htg k
  have cx := hr.2.2 i hi
  rw [anyBelow_iff]
  refine ⟨i, hi, ?_⟩
  rw [CFSG.KC.L34Scan.pts_get' hi, e0, ek, comp_unpack' cx c0, comp_unpack' ck cx,
    beq_unpack (canonK_pcomp cx c0) (canonK_pcomp ck cx)]
  exact nf_of hf

theorem prod_of {inU inV : Nat → Bool} (h : p3ProdK inU inV = true) :
    burnsideI22P3_prodCheck inU inV = true := by
  unfold p3ProdK at h
  rw [CFSG.KC.L34Graph.forceL_eq] at h
  have gL : ∀ k < 64, ((List.range 64).map (tgK L34R.G)).getD k 0 = tgK L34R.G k := fun k hk => by
    rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map, List.getElem_range]
  unfold burnsideI22P3_prodCheck
  rw [CFSG.KS.BfsReplay.allBelow_iff]
  intro k hk
  have h1 := allN' h k hk
  rw [sapp, gL k hk] at h1
  obtain ⟨a, ha, hfa⟩ := ex_of_notB_allN h1
  obtain ⟨hua, h2⟩ := andB_iff.1 (nf_of hfa)
  rw [sapp, gL a ha] at h2
  obtain ⟨b, hb, hfb⟩ := ex_of_notB_allN h2
  obtain ⟨hvb, e⟩ := andB_iff.1 (nf_of hfb)
  rw [gL b hb] at e
  obtain ⟨ca, ea⟩ := htg a
  obtain ⟨cb, eb⟩ := htg b
  obtain ⟨ck, ek⟩ := htg k
  rw [anyBelow_iff]
  refine ⟨a, ha, ?_⟩
  rw [hua, Bool.true_and, anyBelow_iff]
  refine ⟨b, hb, ?_⟩
  rw [hvb, Bool.true_and, ea, eb, ek, comp_unpack' ca cb, beq_unpack (canonK_pcomp ca cb) ck]
  exact e

theorem nc_of {a b : Nat} (h : p3NcK a b = true) : burnsideI22P3_ncCheck a b = true := by
  unfold p3NcK at h
  rw [sapp, sapp] at h
  obtain ⟨ca, ea⟩ := htg a
  obtain ⟨cb, eb⟩ := htg b
  unfold burnsideI22P3_ncCheck
  rw [ea, eb, comp_unpack' ca cb, comp_unpack' cb ca]
  exact nbeq_of (canonK_pcomp ca cb) (canonK_pcomp cb ca) h

theorem check_true : burnsideI22P3_check () = true := by
  unfold burnsideI22P3_check
  rw [o2_of r1.2.2.2 k7280i1 k7280o1, o2_of r2.2.2.2 k7280i2 k7280o2,
    trans_of ⟨r1.1, r1.2.1, r1.2.2.1⟩ rfl (by decide) k7280t1,
    trans_of ⟨r2.1, r2.2.1, r2.2.2.1⟩ rfl (by decide) k7280t2, prod_of k7280p1, prod_of k7280p2,
    nc_of k7280n]
  rfl

end CertificateChecks.KernelLC.L34P3

end
