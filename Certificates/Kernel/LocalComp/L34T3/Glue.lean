module

public import Certificates.Kernel.LocalComp.L34T3.C11a
public import Certificates.Kernel.LocalComp.L34T3.C11b
public import Certificates.Kernel.LocalComp.L34T3.Defs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.LocalComp.L34T3.Small
public import Certificates.Kernel.LocalComp.L34Cert
public import Certificates.Kernel.LocalComp.L34Para.Final
public import CFSG.Certificates.Kernel.L34PowSound
public import CFSG.Certificates.Kernel.L34ScanSound
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCover2CertInputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsNoFrobCertInputs
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34T3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34KSnd
open CFSG.KC.L34Scan CFSG.KC.L34Scan2 CFSG.KC.L34W CFSG.KC.L34Pow CertificateChecks.KernelLC.L34X
open CertificateChecks.KernelLC.L34Cert CertificateChecks.KernelLC.L34Para
open CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.KLie.CT (andB orB notB)

theorem sapp (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem hG : GensG L34R.G := fun j hj => ⟨bindR.2 j hj, cnG hj⟩

theorem htgK (k : Nat) : Cn (tgK L34R.G k) ∧ wordTab (tg k) = unpack 42 6 (tgK L34R.G k) :=
  tgK_eq hG k

theorem htg (k : Nat) : Cn (tgP k) ∧ wordTab (tg k) = unpack 42 6 (tgP k) := tgK_eq hG k

theorem chunks {F : Nat → Bool} (h : ∀ j < 4, chunk45 F j = true) : ∀ s < 180, F s = true := by
  intro s hs
  have hj : s / 45 < 4 := by omega
  have h' := CFSG.KS.Raw.Orb.allN_iff.1 (h (s / 45) hj) (s % 45) (Nat.mod_lt _ (by decide))
  have e : Nat.add (Nat.mul 45 (s / 45)) (s % 45) = s := Nat.div_add_mod s 45
  rwa [e] at h'

theorem cent22211All : ∀ s < 180, cent22211 s = true := chunks fun j hj => by
  match j, hj with
  | 0, _ => exact k11c0
  | 1, _ => exact k11c1
  | 2, _ => exact k11c2
  | 3, _ => exact k11c3

theorem h0_true : h0OK = true := by
  have hk := k22211h
  unfold h0K h0P at hk
  rw [sapp] at hk
  obtain ⟨h3, hall⟩ := andB_iff.1 hk
  obtain ⟨ch, eh⟩ := wordK_eq hG h0w
  unfold h0OK
  rw [eh, comp_unpack' ch ch, comp_unpack' (canonK_pcomp ch ch) ch, idTab42,
    beq_unpack (canonK_pcomp (canonK_pcomp ch ch) ch) cn_pidn, h3, Bool.true_and]
  refine List.all_eq_true.2 fun k hk' => ?_
  have h := List.all_eq_true.1 hall k hk'
  rw [(htg k).2, (htg (4 * k)).2]
  rcases Bool.or_eq_true _ _ ▸ h with h | h
  · rw [h]
    rfl
  · obtain ⟨a, b⟩ := Bool.and_eq_true _ _ ▸ h
    rw [ncomm_of ch (htg k).1 a, ncomm_of ch (htg (4 * k)).1 b]
    simp only [Bool.and_self, Bool.or_true]

theorem z0_true : z0CommOK = true := by
  have hk := k22211z
  unfold z0K at hk
  obtain ⟨h1, h2⟩ := andB_iff.1 hk
  obtain ⟨c1, e1⟩ := htg 1
  obtain ⟨c4, e4⟩ := htg 4
  obtain ⟨c8, e8⟩ := htg 8
  obtain ⟨c16, e16⟩ := htg 16
  obtain ⟨c24, e24⟩ := htg 24
  unfold z0CommOK
  rw [e1, e4, e8, e16, e24, comp_unpack' c1 c16, comp_unpack' c4 c16,
    comp_unpack' (canonK_pcomp c4 c16) c1, comp_unpack' c1 c24, comp_unpack' c8 c24,
    comp_unpack' (canonK_pcomp c8 c24) c1,
    beq_unpack (canonK_pcomp c1 c16) (canonK_pcomp (canonK_pcomp c4 c16) c1),
    beq_unpack (canonK_pcomp c1 c24) (canonK_pcomp (canonK_pcomp c8 c24) c1), h1, h2]
  rfl

theorem unit_true : unitZ0OK = true := by
  have hk := k22211u
  unfold unitK at hk
  rw [sapp] at hk
  obtain ⟨a, hk⟩ := andB_iff.1 hk
  obtain ⟨b, hk⟩ := andB_iff.1 hk
  obtain ⟨c, d⟩ := andB_iff.1 hk
  have cr : Cn (RP 3) := cnRP (by decide)
  obtain ⟨c4, e4⟩ := htg 4
  obtain ⟨c8, e8⟩ := htg 8
  obtain ⟨c12, e12⟩ := htg 12
  unfold unitZ0OK
  rw [r4_eq, e4, e8, e12, beq_iff_eq.2 ((commPt_iff cr c4).1 a), ncomm_of cr c8 b,
    ncomm_of cr c12 c, comp_unpack' cr c8, comp_unpack' c8 c4, comp_unpack' (canonK_pcomp c8 c4) cr,
    beq_unpack (canonK_pcomp cr c8) (canonK_pcomp (canonK_pcomp c8 c4) cr), d]
  rfl

theorem gens_all {x : Nat} (hx : Cn x) :
    ((wordTabs wT₀).toList.all fun g => comp 42 (unpack 42 6 x) g == comp 42 g (unpack 42 6 x)) =
      allN 4 fun j => commPt 42 6 x (L34PT.G j) := by
  obtain ⟨hsz, hb⟩ := rT.2.2.2
  rw [Bool.eq_iff_iff, List.all_eq_true, CFSG.KS.Raw.Orb.allN_iff]
  constructor
  · intro H j hj
    have hj' : j < (wordTabs wT₀).size := by rw [hsz]; exact hj
    obtain ⟨e, cg⟩ := hb j hj
    have h := H _ (Array.mem_toList_iff.2 (Array.mem_iff_getElem.2 ⟨j, hj', rfl⟩))
    rw [← getElem!_pos (wordTabs wT₀) j hj', e, beq_iff_eq] at h
    exact (commPt_iff hx cg).2 h
  · intro H g hg
    obtain ⟨j, hj', rfl⟩ := Array.mem_iff_getElem.1 (Array.mem_toList_iff.1 hg)
    have hj : j < 4 := by rw [hsz] at hj'; exact hj'
    obtain ⟨e, cg⟩ := hb j hj
    rw [← getElem!_pos (wordTabs wT₀) j hj', e, beq_iff_eq]
    exact (commPt_iff hx cg).1 (H j hj)

theorem tgT0 : L34PT.T 0 = tgK L34R.G 0 ∧ L34PT.T 5 = tgK L34R.G 4 ∧
    L34PT.T 60 = tgK L34R.G 8 ∧ L34PT.T 51 = tgK L34R.G 12 ∧ L34PT.T 1 = tgK L34R.G 17 := by
  obtain ⟨a, h⟩ := andB_iff.1 kTg
  obtain ⟨b, h⟩ := andB_iff.1 h
  obtain ⟨c, h⟩ := andB_iff.1 h
  obtain ⟨d, e⟩ := andB_iff.1 h
  exact ⟨(Nat.eq_of_beq_eq_true a).symm, (Nat.eq_of_beq_eq_true b).symm,
    (Nat.eq_of_beq_eq_true c).symm, (Nat.eq_of_beq_eq_true d).symm, (Nat.eq_of_beq_eq_true e).symm⟩

theorem any_z {x z : Nat} (k : Nat) (hk : k ∈ [0, 4, 8, 12]) (hz : z = tgK L34R.G k)
    (h : Nat.beq x z = true) :
    ([0, 4, 8, 12].any fun k => unpack 42 6 x == wordTab (tg k)) = true := by
  refine List.any_eq_true.2 ⟨k, hk, ?_⟩
  rw [(htgK k).2, Nat.eq_of_beq_eq_true h, hz]
  exact beq_self_eq_true _

theorem cent_true : centROK = true := by
  unfold centROK
  rw [hR.1]
  refine pts_toList_all fun i hi => ?_
  have hx := pinR.canon i hi
  have h := scanSl_spec (f := centPt (L34PT.T 0) (L34PT.T 5) (L34PT.T 60) (L34PT.T 51))
    (T := L34R.T) (L := 1344) (K := 180) (by decide) (by decide) (fun s hs => by
      have h1 := cent22211All s hs
      unfold cent22211 at h1
      rwa [sapp, sapp, sapp, sapp] at h1) i hi
  unfold centPt at h
  rw [gens_all hx]
  rcases orB_iff.1 h with h | h
  · rw [notB_iff.1 h]
    rfl
  · rw [Bool.or_eq_true]
    right
    rcases orB_iff.1 h with h | h
    · exact any_z 0 (by simp) tgT0.1 h
    · rcases orB_iff.1 h with h | h
      · exact any_z 4 (by simp) tgT0.2.1 h
      · rcases orB_iff.1 h with h | h
        · exact any_z 8 (by simp) tgT0.2.2.1 h
        · exact any_z 12 (by simp) tgT0.2.2.2.1 h

theorem sec5_true : sec5OK = true := by
  unfold sec5OK
  rw [h0_true, z0_true, unit_true, k22211b, cent_true]
  rfl

end CertificateChecks.KernelLC.L34T3

end
