module

public import Certificates.Kernel.LocalQT.He4148.Data
public import Certificates.Kernel.LocalQT.He4148.Glue
public import CFSG.Certificates.Kernel.SporSch.MathieuOC2Sound
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentHeInnerCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import CFSG.Certificates.Kernel.SporSch.MathieuOCSound
public import CFSG.Sporadic.HeldB.ClassCount
public import CFSG.Sporadic.HeldB.InnerCheck
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.Sporadic.Schreier.Outer

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLQT.He4148

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB CFSG.KC.BfsPin
open CFSG.QuasithinUnique.Id2519.HeInner

theorem bX : bindsK 105 7 XQ.S XQ.SI heSigmaP 0 = true := by quickRfl

theorem bD : bindsK 105 7 DQ.S DQ.SI heDpGens 0 = true := by quickRfl

theorem oX : Nat.beq (ordK XQ.LR 4) 40320 = true := by quickRfl

theorem oD : Nat.beq (ordK DQ.LR 3) 20160 = true := by quickRfl

theorem sXD : allN 5 (fun k => siftK 105 7 (mask 7) (105 * 7) (pidn 105 7) XQ.LR XQ.TRI XQ.BP 4 0
    (DQ.S k)) = true := by quickRfl

theorem sC1 : allN 9 (fun i => allN 5 (fun k => siftK 105 7 (mask 7) (105 * 7) (pidn 105 7)
    DQ.LR DQ.TRI DQ.BP 3 0
    (pcomp 105 7 (mask 7) (pcomp 105 7 (mask 7) (XQ.S i) (DQ.S k)) (XQ.SI i)))) = true := by
  quickRfl

theorem sC2 : allN 9 (fun i => allN 5 (fun k => siftK 105 7 (mask 7) (105 * 7) (pidn 105 7)
    DQ.LR DQ.TRI DQ.BP 3 0
    (pcomp 105 7 (mask 7) (pcomp 105 7 (mask 7) (XQ.SI i) (DQ.S k)) (XQ.S i)))) = true := by
  quickRfl

theorem sC3 : allN 9 (fun i => allN 9 (fun j => siftK 105 7 (mask 7) (105 * 7) (pidn 105 7)
    DQ.LR DQ.TRI DQ.BP 3 0
    (pcomp 105 7 (mask 7) (pcomp 105 7 (mask 7) (pcomp 105 7 (mask 7) (XQ.S i) (XQ.S j))
      (XQ.SI i)) (XQ.SI j)))) = true := by
  quickRfl

theorem len_X : heSigmaP.length = 9 := rfl

theorem len_D : heDpGens.length = 5 := rfl

theorem atX {j : Nat} (hj : j < 9) : BindAt 105 7 (XQ.S j) (XQ.SI j) (heSigmaP.getD j #[]) := by
  have h := bindsK_spec bX j (by rw [len_X]; exact hj)
  rwa [Nat.zero_add] at h

theorem atD {k : Nat} (hk : k < 5) : BindAt 105 7 (DQ.S k) (DQ.SI k) (heDpGens.getD k #[]) := by
  have h := bindsK_spec bD k (by rw [len_D]; exact hk)
  rwa [Nat.zero_add] at h

theorem repX {i : Nat} (hi : i < 9) : Rep 105 (unpack 105 7 (XQ.S i)) (heSigmaPerm i) ∧
    Rep 105 (unpack 105 7 (XQ.SI i)) (heSigmaPerm i)⁻¹ :=
  ⟨(bind_facts (atX hi)).2.2.1, (bind_facts (atX hi)).2.2.2⟩

theorem repD {k : Nat} (hk : k < 5) : Rep 105 (unpack 105 7 (DQ.S k)) (heDpPerm k) :=
  (bind_facts (atD hk)).2.2.1

theorem chainX : ChainK 105 7 (heSigmaP.map (permOrId 105)) heXpWords
    (#v[1, 0, 2, 3] : Vector (Fin 105) 4) XQ.S XQ.SI XQ.LR XQ.TR XQ.TRI 15 XQ.BP 7 16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, XQ.head, XQ.hl,
    by norm_num, XQ.hs⟩
  have hj' : j < heSigmaP.length := by simpa using hj
  rw [getD_map_lt _ #[] _ hj']
  exact imageList_bind (atX (len_X ▸ hj'))

theorem chainD : ChainK 105 7 (heDpGens.map (permOrId 105)) heDpWords
    (#v[1, 0, 2] : Vector (Fin 105) 3) DQ.S DQ.SI DQ.LR DQ.TR DQ.TRI 10 DQ.BP 7 16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, DQ.head, DQ.hl,
    by norm_num, DQ.hs⟩
  have hj' : j < heDpGens.length := by simpa using hj
  rw [getD_map_lt _ #[] _ hj']
  exact imageList_bind (atD (len_D ▸ hj'))

theorem xp_check : heXp.check = true ∧ heXp.orderCertificate = 40320 := by
  obtain ⟨h1, h2⟩ := chainK_check (by decide) (by decide) chainX
  exact ⟨h1, h2.trans (Nat.eq_of_beq_eq_true oX)⟩

theorem dp_check : heDp.check = true ∧ heDp.orderCertificate = 20160 := by
  obtain ⟨h1, h2⟩ := chainK_check (by decide) (by decide) chainD
  exact ⟨h1, h2.trans (Nat.eq_of_beq_eq_true oD)⟩

theorem dp_gens : (∀ k < 5, permChk 105 (heDpGens.getD k #[]) = true) ∧ heDpGens.length = 5 ∧
    heSigmaP.length = 9 :=
  ⟨fun _ hk => (bind_facts (atD hk)).2.1, len_D, len_X⟩

theorem canonX {i : Nat} (hi : i < 9) : canonK 105 7 (mask 7) (105 * 7) (XQ.S i) = true ∧
    canonK 105 7 (mask 7) (105 * 7) (XQ.SI i) = true :=
  ⟨(atX hi).2.2.2.1, (atX hi).2.2.2.2⟩

theorem canonD {k : Nat} (hk : k < 5) : canonK 105 7 (mask 7) (105 * 7) (DQ.S k) = true :=
  (atD hk).2.2.2.1

theorem sift_D {g : Equiv.Perm (Fin 105)} {G : Nat} (hc : canonK 105 7 (mask 7) (105 * 7) G = true)
    (hg : Rep 105 (unpack 105 7 G) g)
    (h : siftK 105 7 (mask 7) (105 * 7) (pidn 105 7) DQ.LR DQ.TRI DQ.BP 3 0 G = true) :
    heDp.sift g 0 = true :=
  chainK_sift (by decide) (by decide) chainD (imageList_of_rep (unpack_size' _ _ _) hg) hc h

theorem dp_rel : (∀ k < 5, heXp.sift (heDpPerm k) 0 = true) ∧
    (∀ i < 9, ∀ k < 5,
      heDp.sift (heSigmaPerm i * heDpPerm k * (heSigmaPerm i)⁻¹) 0 = true) ∧
    (∀ i < 9, ∀ k < 5,
      heDp.sift ((heSigmaPerm i)⁻¹ * heDpPerm k * heSigmaPerm i) 0 = true) ∧
    (∀ i < 9, ∀ j < 9,
      heDp.sift (heSigmaPerm i * heSigmaPerm j * (heSigmaPerm i)⁻¹ * (heSigmaPerm j)⁻¹) 0 =
        true) := by
  refine ⟨fun k hk => ?_, fun i hi k hk => ?_, fun i hi k hk => ?_, fun i hi j hj => ?_⟩
  · exact chainK_sift (by decide) (by decide) chainX
      (imageList_of_rep (unpack_size' _ _ _) (repD hk)) (canonD hk) (allN_spec sXD k hk)
  · obtain ⟨c, ci⟩ := canonX hi
    have c1 := canonK_pcomp c (canonD hk)
    exact sift_D (canonK_pcomp c1 ci)
      (rep_pcomp c1 ci (rep_pcomp c (canonD hk) (repX hi).1 (repD hk)) (repX hi).2)
      (allN_spec (allN_spec sC1 i hi) k hk)
  · obtain ⟨c, ci⟩ := canonX hi
    have c1 := canonK_pcomp ci (canonD hk)
    exact sift_D (canonK_pcomp c1 c)
      (rep_pcomp c1 c (rep_pcomp ci (canonD hk) (repX hi).2 (repD hk)) (repX hi).1)
      (allN_spec (allN_spec sC2 i hi) k hk)
  · obtain ⟨c, ci⟩ := canonX hi
    obtain ⟨d, di⟩ := canonX hj
    have c1 := canonK_pcomp c d
    have c2 := canonK_pcomp c1 ci
    exact sift_D (canonK_pcomp c2 di)
      (rep_pcomp c2 di (rep_pcomp c1 ci (rep_pcomp c d (repX hi).1 (repX hj).1) (repX hi).2)
        (repX hj).2)
      (allN_spec (allN_spec sC3 i hi) j hj)

end CertificateChecks.KernelLQT.He4148

end
