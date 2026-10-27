module

public import Certificates.Kernel.HSStd.M12PinChecks
public import CFSG.Certificates.Kernel.L34CoverSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HFIM12Data
import CFSG.Certificates.Kernel.BfsPinSetSound
import CFSG.Certificates.Kernel.BfsPinUnpack
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.BfsReplay
import CFSG.Certificates.Kernel.Spor.PackWord

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHSStd.M12K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34Inv
open CFSG.PSL3Four.Native CFSG.EvenSporadicStandard.HSStd.HFI CertificateChecks.KernelHSStd
open CFSG.KLie.CT (andB orB notB anyN)

theorem bind : m12Gens.size = 2 ∧ ∀ k < 2, m12Gens[k]! = unpack 12 6 (M12.G k) :=
  CFSG.KC.BfsPin.binds_of_check kBind

theorem bindA : m12a₀T = unpack 12 6 (M12A.T 0) := by
  have h := kBindAB
  rw [Bool.and_eq_true] at h
  exact unpack_eq_of_bindArrK h.1

theorem bindB : m12b₀T = unpack 12 6 (M12B.T 0) := by
  have h := kBindAB
  rw [Bool.and_eq_true] at h
  exact unpack_eq_of_bindArrK h.2

theorem pinM : PinE 12 6 m12Gens 95040 2 95040 1440 66 17 M12.G M12.T M12.E M12.C M12.S M12.SI :=
  ⟨bind.1, bind.2, CFSG.KS.Raw.Orb.allN_iff.1 kPerm, kHead, rfl, by decide, le_refl _,
    fun s hs => M12.prAll s hs⟩

theorem pinA : PinO 12 6 m12Gens m12a₀T 891 2 396 10 (M12A.T 0) M12.G M12.GI M12A.T M12A.E M12A.S
    M12A.SI := ⟨bind.1, bind.2, bindA, kOrbA, by decide⟩

theorem pinB : PinO 12 6 m12Gens m12b₀T 891 2 495 10 (M12B.T 0) M12.G M12.GI M12B.T M12B.E M12B.S
    M12B.SI := ⟨bind.1, bind.2, bindB, kOrbB, by decide⟩

theorem kCentK : centK 12 6 95040 M12.T (M12A.T 0) 240 M12C.X M12C.P = true := by
  have he := kEnds
  simp only [Bool.and_eq_true] at he
  exact centK_of_slices (L := 1440) (K := 66) (CC := M12C.CC) rfl (fun s hs => M12C.csAll s hs)
    (Nat.eq_of_beq_eq_true he.1) (Nat.eq_of_beq_eq_true he.2) kList

theorem cA : canonK 12 6 (mask 6) (12 * 6) (M12A.T 0) = true := pinA.canon 0 (by decide)
theorem cB : canonK 12 6 (mask 6) (12 * 6) (M12B.T 0) = true := pinB.canon 0 (by decide)

theorem centA : centTabs 12 (pts 12 6 95040 M12.T) m12a₀T = pts 12 6 240 M12C.P :=
  cent_sound bindA cA pinM.canon kCentK

theorem canonP : ∀ k < 240, canonK 12 6 (mask 6) (12 * 6) (M12C.P k) = true := by
  intro k hk
  have h := CFSG.KS.Raw.Orb.allN_iff.1 kList k hk
  rw [CFSG.KC.BfsPin.strictB_app, CFSG.KC.L34KSnd.andB_iff] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨-, h3⟩ := CFSG.KC.L34KSnd.andB_iff.1 h2
  obtain ⟨-, h4⟩ := CFSG.KC.L34KSnd.andB_iff.1 h3
  rw [Nat.eq_of_beq_eq_true h4]
  exact pinM.canon _ (Nat.blt_eq.mp h1)

theorem hfiMem_eq (A : Array Tab) (x : Tab) : hfiMem A x = memTab A x := rfl

theorem hfiM12_true :
    hfiM12Check (enumBFS 12 m12Gens 95040)
      (orbitBFS 12 m12Gens (m12Gens.map (invTab 12)) m12a₀T 891)
      (orbitBFS 12 m12Gens (m12Gens.map (invTab 12)) m12b₀T 891) = true := by
  have hE := enum_sound pinM
  have hA := orbit_sound pinA
  have hB := orbit_sound pinB
  have hab := kAB
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hab
  obtain ⟨⟨⟨⟨⟨⟨⟨ha1, ha2⟩, hb1⟩, hb2⟩, hsa⟩, hna⟩, hsb⟩, hnb⟩ := hab
  have hcA := pinA.canon
  have hcB := pinB.canon
  unfold hfiM12Check
  simp only []
  rw [hE.1, hA.1, hB.1, centA]
  simp only [Bool.and_eq_true]
  have g2 : ((pts 12 6 95040 M12.T).size == 95040) = true := by rw [pts_size]; rfl
  have g4 : ((pts 12 6 396 M12A.T).size == 396) = true := by rw [pts_size]; rfl
  have g6 : ((pts 12 6 495 M12B.T).size == 495) = true := by rw [pts_size]; rfl
  have g7 : hfiMem (pts 12 6 95040 M12.T) m12a₀T = true := by
    rw [hfiMem_eq, bindA, memTab_pts pinM.canon cA]
    exact memK_of_wit (Nat.blt_eq.mp ha1) (Nat.eq_of_beq_eq_true ha2)
  have g8 : hfiMem (pts 12 6 95040 M12.T) m12b₀T = true := by
    rw [hfiMem_eq, bindB, memTab_pts pinM.canon cB]
    exact memK_of_wit (Nat.blt_eq.mp hb1) (Nat.eq_of_beq_eq_true hb2)
  have g9 : (comp 12 m12a₀T m12a₀T == idTab 12) = true := by rw [bindA, sq_id cA]; exact hsa
  have g10 : (!(m12a₀T == idTab 12)) = true := by rw [bindA, beq_id cA, hna]; rfl
  have g11 : (comp 12 m12b₀T m12b₀T == idTab 12) = true := by rw [bindB, sq_id cB]; exact hsb
  have g12 : (!(m12b₀T == idTab 12)) = true := by rw [bindB, beq_id cB, hnb]; rfl
  have g13 : coverOK 12 (pts 12 6 95040 M12.T) #[pts 12 6 396 M12A.T, pts 12 6 495 M12B.T] =
      true := by
    refine cover_sound (no := 2) (ON := M12O.N) (OT := M12O.T) (W := M12.W) (L := 1440) (K := 66)
      ⟨rfl, fun o ho => ?_⟩ pinM.canon rfl (fun s hs => M12.cvAll s hs)
    match o, ho with
    | 0, _ => rfl
    | 1, _ => rfl
  have g14 : (allBelow (pts 12 6 240 M12C.P).size fun k =>
      !(comp 12 (pts 12 6 240 M12C.P)[k]! (pts 12 6 240 M12C.P)[k]! == idTab 12 &&
        !(pts 12 6 240 M12C.P)[k]! == idTab 12 && !(pts 12 6 240 M12C.P)[k]! == m12a₀T &&
        hfiMem (pts 12 6 396 M12A.T) (pts 12 6 240 M12C.P)[k]! &&
        hfiMem (pts 12 6 396 M12A.T) (comp 12 m12a₀T (pts 12 6 240 M12C.P)[k]!)) ||
      anyBelow (pts 12 6 95040 M12.T).size fun j =>
        comp 12 (pts 12 6 95040 M12.T)[j]! m12a₀T ==
            comp 12 (pts 12 6 240 M12C.P)[k]! (pts 12 6 95040 M12.T)[j]! &&
          comp 12 (pts 12 6 95040 M12.T)[j]! (pts 12 6 240 M12C.P)[k]! ==
            comp 12 (comp 12 m12a₀T (pts 12 6 240 M12C.P)[k]!) (pts 12 6 95040 M12.T)[j]!) =
      true := by
    rw [CFSG.KS.BfsReplay.allBelow_iff]
    intro k hk
    rw [pts_size] at hk
    have hx := canonP k hk
    have hax := CFSG.KC.BfsPin.canonK_pcomp cA hx
    rw [pts_get' hk, bindA, sq_id hx, beq_id hx, beq_r hx cA, hfiMem_eq, hfiMem_eq,
      memTab_pts hcA hx, CFSG.KC.L34KSnd.comp_unpack' cA hx, memTab_pts hcA hax,
      Bool.or_eq_true, Bool.not_eq_true']
    by_cases hP : (Nat.beq (pcomp 12 6 (mask 6) (M12C.P k) (M12C.P k)) (pidn 12 6) &&
        !Nat.beq (M12C.P k) (pidn 12 6) && !Nat.beq (M12C.P k) (M12A.T 0) &&
        memK 396 M12A.T (M12C.P k) &&
        memK 396 M12A.T (pcomp 12 6 (mask 6) (M12A.T 0) (M12C.P k))) = true
    · right
      simp only [Bool.and_eq_true] at hP
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hP
      have hi : invNeK 12 6 (pidn 12 6) (M12A.T 0) (M12C.P k) = true := by
        unfold invNeK
        rw [andB_eq, andB_eq, notB_eq, notB_eq, h1]
        simp only [Bool.true_and, Bool.and_eq_true]
        exact ⟨h2, h3⟩
      obtain ⟨hj, e1, e2⟩ := conjWit_spec kWit k hk hi h4 h5
      have hh := pinM.canon _ hj
      rw [CFSG.KC.L34KSnd.anyBelow_iff]
      refine ⟨M12C.H k, by rw [pts_size]; exact hj, ?_⟩
      beta_reduce
      rw [pts_get' hj, CFSG.KC.L34KSnd.comp_unpack' hh cA, CFSG.KC.L34KSnd.comp_unpack' hx hh,
        CFSG.KC.L34KSnd.comp_unpack' hh hx, CFSG.KC.L34KSnd.comp_unpack' hax hh, e1, e2,
        Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
      exact ⟨rfl, rfl⟩
    · left
      exact eq_false_of_ne_true hP
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hE.2, g2⟩, hA.2⟩, g4⟩, hB.2⟩, g6⟩, g7⟩, g8⟩, g9⟩, g10⟩, g11⟩, g12⟩, g13⟩,
    g14⟩

end CertificateChecks.KernelHSStd.M12K

end
