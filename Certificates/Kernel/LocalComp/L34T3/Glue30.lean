module

public import Certificates.Kernel.LocalComp.L34T3.C30a
public import Certificates.Kernel.LocalComp.L34T3.C30b
public import Certificates.Kernel.LocalComp.L34T3.Glue
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L34CertInputs
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34T3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34KSnd
open CFSG.KC.L34Scan CFSG.KC.L34Scan2 CFSG.KC.L34W CFSG.KC.L34Pow CertificateChecks.KernelLC.L34X
open CertificateChecks.KernelLC.L34Cert
open CFSG.PSL3Four.Native CFSG.ComponentClassification.Foote5.L34Unitary
open CFSG.KLie.CT (andB orB notB)

theorem unit23230All : ∀ s < 180, unit23230 s = true := chunks fun j hj => by
  match j, hj with
  | 0, _ => exact k30c0
  | 1, _ => exact k30c1
  | 2, _ => exact k30c2
  | 3, _ => exact k30c3

theorem nf_of' {a : Bool} (h : notB a = false) : a = true := by
  cases a
  · exact absurd h (by decide)
  · rfl

theorem memL_of {N x j : Nat} {T : Nat → Nat} (hj : j < N) (e : T j = x) : memL N T x = true := by
  unfold memL
  cases h : allN N fun q => notB (Nat.beq (T q) x)
  · rfl
  · have h' := CFSG.KS.Raw.Orb.allN_iff.1 h j hj
    rw [e, Nat.beq_refl] at h'
    exact absurd h' (by decide)

theorem hpowT {x : Nat} (hx : Cn x) (k : Nat) : tpow (unpack 42 6 x) k = unpack 42 6 (ppowK x k) :=
  (ppowK_spec hx (tpow (unpack 42 6 x)) rfl (fun _ => rfl) k).2

theorem cn_wK {x xi s si : Nat} (hx : Cn x) (hxi : Cn xi) (hs : Cn s) (hsi : Cn si) :
    Cn (wK x xi s si) := by
  unfold wK
  exact canonK_pcomp (canonK_pcomp (canonK_pcomp hxi (canonK_pcomp (canonK_pcomp
    (canonK_pcomp hsi hx) hs) hxi)) hx) (canonK_pcomp (canonK_pcomp (canonK_pcomp hx hsi) hxi) hs)

theorem wTab_eq {x s : Nat} (hx : Cn x) (hs : Cn s) :
    wTab (unpack 42 6 x) (unpack 42 6 s) = unpack 42 6 (wK x (ppowK x 944) s (ppowK s 7)) := by
  have cxi := ppowK_cn hx 944
  have csi := ppowK_cn hs 7
  unfold wTab tTab tInvTab
  rw [hpowT hx 944, hpowT hs 7]
  generalize ppowK x 944 = xi at cxi ⊢
  generalize ppowK s 7 = si at csi ⊢
  unfold wK
  rw [comp_unpack' csi hx, comp_unpack' (canonK_pcomp csi hx) hs,
    comp_unpack' (canonK_pcomp (canonK_pcomp csi hx) hs) cxi,
    comp_unpack' cxi (canonK_pcomp (canonK_pcomp (canonK_pcomp csi hx) hs) cxi),
    comp_unpack' (canonK_pcomp cxi (canonK_pcomp (canonK_pcomp (canonK_pcomp csi hx) hs) cxi)) hx,
    comp_unpack' hx csi, comp_unpack' (canonK_pcomp hx csi) cxi,
    comp_unpack' (canonK_pcomp (canonK_pcomp hx csi) cxi) hs,
    comp_unpack' (canonK_pcomp (canonK_pcomp cxi (canonK_pcomp (canonK_pcomp
      (canonK_pcomp csi hx) hs) cxi)) hx) (canonK_pcomp (canonK_pcomp (canonK_pcomp hx csi) cxi) hs)]

theorem witness_of {x : Nat} (hx : Cn x) (h : witU (pidn 42 6) x (ppowK x 944) = true) :
    ((pts 42 6 72 L34C4.P).any fun s => tpow s 8 == unpack 42 6 (pidn 42 6) &&
      !(DD2.1.contains (wTab (unpack 42 6 x) s))) = true := by
  unfold witU at h
  obtain ⟨a, ha, hf⟩ := ex_of_notB_allN h
  rw [sapp] at hf
  obtain ⟨h8, h7⟩ := andB_iff.1 (nf_of' hf)
  rw [sapp, notB_iff] at h7
  have cs : Cn (L34C4.P a) := CFSG.KS.Raw.Orb.allN_iff.1 k30c a ha
  rw [← Array.any_toList]
  refine pts_toList_any ⟨a, ha, ?_⟩
  rw [hpowT cs 8, beq_unpack (ppowK_cn cs 8) cn_pidn, h8, Bool.true_and, wTab_eq hx cs]
  have cw := cn_wK hx (ppowK_cn hx 944) cs (ppowK_cn cs 7)
  cases hc : DD2.1.contains (unpack 42 6 (wK x (ppowK x 944) (L34C4.P a) (ppowK (L34C4.P a) 7)))
  · rfl
  · exfalso
    have hm := (der2.2.2 _).1 (Array.mem_toList_iff.2 (Array.contains_iff_mem.1 hc))
    obtain ⟨j, hj, e⟩ := mem_pts hm
    have cd : Cn (L34D2.P j) := CFSG.KS.Raw.Orb.allN_iff.1 k30d j hj
    have hb := beq_unpack cw cd
    rw [e, beq_self_eq_true] at hb
    rw [memL_of hj (Nat.eq_of_beq_eq_true hb.symm).symm] at h7
    exact absurd h7 (by decide)

theorem unitary_true : unitaryCheck = true := by
  have hc4 : c₄Tabs = pts 42 6 72 L34C4.P := by
    unfold c₄Tabs
    rw [hS.1, cent4]
  have hd2 : d₂Tabs = DD2.1 := by
    unfold d₂Tabs d₁Tabs DD2 DD1
    rw [hc4]
  unfold unitaryCheck
  rw [hR.1]
  refine pts_all fun i hi => ?_
  have hx := pinR.canon i hi
  have h := scanSl_spec (f := unitPt (RP 3) (pidn 42 6)) (T := L34R.T) (L := 1344) (K := 180)
    (by decide) (by decide) (fun s hs => by
      have h1 := unit23230All s hs
      unfold unit23230 at h1
      rwa [sapp, sapp] at h1) i hi
  have cr : Cn (RP 3) := cnRP (by decide)
  unfold unitPt at h
  unfold unitaryAt
  rw [hc4, hd2, r4_eq, idTab42, hpowT hx 945, beq_unpack (ppowK_cn hx 945) cn_pidn]
  rcases orB_iff.1 h with h | h
  · rw [ncomm_of hx cr h]
    simp only [Bool.true_or]
  · rcases orB_iff.1 h with h | h
    · obtain ⟨q, hq, e⟩ := memL_spec h
      have hm : (pts 42 6 72 L34C4.P).contains (unpack 42 6 (L34R.T i)) = true := by
        rw [Array.contains_iff_mem, ← e]
        exact Array.mem_toList_iff.1 (pts_mem hq)
      rw [hm]
      simp only [Bool.or_true, Bool.true_or]
    · rcases orB_iff.1 h with h | h
      · simp only [with945_eq hx, notB_iff] at h
        rw [h]
        simp only [Bool.not_false, Bool.or_true, Bool.true_or]
      · rw [with944_eq hx] at h
        rw [witness_of hx h]
        simp only [Bool.or_true]

end CertificateChecks.KernelLC.L34T3

end
