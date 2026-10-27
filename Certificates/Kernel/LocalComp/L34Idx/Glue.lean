module

public import Certificates.Kernel.LocalComp.L34Idx.C70a
public import Certificates.Kernel.LocalComp.L34Idx.C70b
public import Certificates.Kernel.LocalComp.L34Idx.Small
public import Certificates.Kernel.LocalComp.L34T3.Glue
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4RIdxCertInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34Idx

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34KSnd
open CFSG.KC.L34Scan CFSG.KC.L34Scan2 CFSG.KC.L34W CFSG.KC.L34Pow CertificateChecks.KernelLC.L34X
open CertificateChecks.KernelLC.L34Cert CertificateChecks.KernelLC.L34Para
open CertificateChecks.KernelLC.L34T3 (chunks sapp)
open CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.GrSLit.GrS4
open CFSG.KLie.CT (andB orB notB)

theorem idxAll : ∀ s < 180, idx22970 s = true := chunks fun j hj => by
  match j, hj with
  | 0, _ => exact k70c0
  | 1, _ => exact k70c1
  | 2, _ => exact k70c2
  | 3, _ => exact k70c3

theorem idxPtAll : ∀ i < 241920,
    idxPt 48 (L34PT.T 5) (L34PT.T 51) (pidn 42 6) (L34R.T i) = true :=
  scanSl_spec (L := 1344) (K := 180) (by decide) (by decide) fun s hs => by
    have h := idxAll s hs
    unfold idx22970 at h
    rwa [sapp, sapp, sapp] at h

theorem cnT0 {i : Nat} (hi : i < 64) : Cn (L34PT.T i) := rT.2.2.1 i hi

theorem cnY {q : Nat} (hq : q < 48) : Cn (L34IX.Y q) :=
  (andB_iff.1 (allN_spec kY q hq)).1

theorem cnYI {q : Nat} (hq : q < 48) : Cn (L34IX.YI q) :=
  (andB_iff.1 (andB_iff.1 (allN_spec kY q hq)).2).1

theorem yyi {q : Nat} (hq : q < 48) :
    pcomp 42 6 (mask 6) (L34IX.Y q) (L34IX.YI q) = pidn 42 6 :=
  Nat.eq_of_beq_eq_true (andB_iff.1 (andB_iff.1 (allN_spec kY q hq)).2).2

theorem powTab_eq {x : Nat} (hx : Cn x) (k : Nat) :
    powTab (unpack 42 6 x) k = unpack 42 6 (ppowK x k) :=
  (ppowK_spec hx (powTab (unpack 42 6 x)) rfl (fun _ => rfl) k).2

theorem pow4_beq {x : Nat} (hx : Cn x) :
    (powTab (unpack 42 6 x) 4 == idTab 42) = Nat.beq (ppowK x 4) (pidn 42 6) := by
  rw [powTab_eq hx, idTab42, beq_unpack (ppowK_cn hx 4) cn_pidn]

theorem mem_zT0 {i : Nat} (hi : i < 64) (h : allN 4 (fun j => commPt 42 6 (L34PT.T i) (L34PT.G j)) = true) :
    unpack 42 6 (L34PT.T i) ∈ (zT0Tabs (pts 42 6 64 L34PT.T)).toList := by
  obtain ⟨hsz, hb⟩ := rT.2.2.2
  unfold zT0Tabs
  rw [Array.mem_toList_iff, Array.mem_filter]
  refine ⟨Array.mem_toList_iff.1 (pts_mem hi), CFSG.KS.BfsReplay.allBelow_iff.2 fun j hj => ?_⟩
  rw [hsz] at hj
  obtain ⟨e, cg⟩ := hb j hj
  unfold commT
  rw [e, beq_iff_eq]
  exact (commPt_iff (cnT0 hi) cg).1 (allN_spec h j hj)

theorem comm_of_mem {y z : Tab} {Z : Array Tab}
    (h : (allBelow Z.size fun i => commT y Z[i]!) = true) (hz : z ∈ Z.toList) :
    comp 42 y z = comp 42 z y := by
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 (Array.mem_toList_iff.1 hz)
  have h' := CFSG.KS.BfsReplay.allBelow_iff.1 h i hi
  unfold commT at h'
  rwa [getElem!_pos Z i hi, beq_iff_eq] at h'

theorem mem_r2 {y : Tab}
    (hy : y ∈ (r2Tabs (pts 42 6 241920 L34R.T) (pts 42 6 20160 L34S.T)
      (zT0Tabs (pts 42 6 64 L34PT.T))).toList) :
    ∃ q < 48, y = unpack 42 6 (L34IX.Y q) := by
  unfold r2Tabs at hy
  rw [Array.mem_toList_iff, Array.mem_filter] at hy
  obtain ⟨hR', hp⟩ := hy
  obtain ⟨i, hi, rfl⟩ := mem_pts (Array.mem_toList_iff.2 hR')
  have cx := pinR.canon i hi
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
  obtain ⟨⟨h4, hz⟩, hS'⟩ := hp
  have h := idxPtAll i hi
  unfold idxPt at h
  obtain ⟨z5, z51⟩ := andB_iff.1 kZ
  rcases orB_iff.1 h with h | h
  · rw [notB_iff] at h
    have c5 := comm_of_mem hz (mem_zT0 (by decide) z5)
    have c51 := comm_of_mem hz (mem_zT0 (by decide) z51)
    rw [(commPt_iff cx (cnT0 (i := 5) (by decide))).2 c5,
      (commPt_iff cx (cnT0 (i := 51) (by decide))).2 c51] at h
    exact absurd h (by decide)
  rcases orB_iff.1 h with h | h
  · rw [pow4_beq cx] at h4
    rw [h4] at h
    exact absurd h (by decide)
  rcases orB_iff.1 h with h | h
  · obtain ⟨k, hk, e⟩ := memL_spec h
    obtain ⟨hq, he⟩ := andB_iff.1 (by simpa only [sapp] using allN_spec kTS k hk)
    have hf : found (indexOf (pts 42 6 20160 L34S.T)) (pts 42 6 20160 L34S.T)
        (unpack 42 6 (L34R.T i)) = true := by
      unfold pts
      exact found_pts (Nat.le_of_ble_eq_true hq) ((Nat.eq_of_beq_eq_true he).trans e)
    rw [hf] at hS'
    exact absurd hS' (by decide)
  · obtain ⟨q, hq, e⟩ := memL_spec h
    exact ⟨q, hq, by rw [e]⟩

theorem pair_true {q q' : Nat} (hq : q < 48) (hq' : q' < 48) :
    (invOK (unpack 42 6 (L34IX.Y q')) &&
      (!(powTab (comp 42 (unpack 42 6 (L34IX.Y q)) (invTab 42 (unpack 42 6 (L34IX.Y q')))) 4 ==
          idTab 42) ||
        found (indexOf (pts 42 6 20160 L34S.T)) (pts 42 6 20160 L34S.T)
          (comp 42 (unpack 42 6 (L34IX.Y q)) (invTab 42 (unpack 42 6 (L34IX.Y q')))))) = true := by
  have ei := invTab_eq_of_pcomp (cnY hq') (cnYI hq') (yyi hq')
  have hrow : q < 24 ∨ 24 ≤ q := Nat.lt_or_ge q 24
  have hp : pairPt q q' (L34IX.W (Nat.add (Nat.mul 48 q) q')) = true := by
    rcases hrow with h | h
    · have := allN_spec kP0 q h
      rw [show Nat.add 0 q = q from Nat.zero_add q, sapp] at this
      exact allN_spec this q' hq'
    · have := allN_spec kP1 (q - 24) (by omega)
      rw [sapp, show Nat.add 24 (q - 24) = q from Nat.add_sub_cancel' h] at this
      exact allN_spec this q' hq'
  unfold pairPt at hp
  rw [sapp] at hp
  have cp := canonK_pcomp (cnY hq) (cnYI hq')
  rw [ei, comp_unpack' (cnY hq) (cnYI hq'), pow4_beq cp, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · unfold invOK
    rw [ei, size_unpack, comp_inv_of_pcomp (cnY hq') (cnYI hq') (yyi hq')]
    rfl
  · rcases orB_iff.1 hp with h | h
    · rw [notB_iff.1 h]
      rfl
    · obtain ⟨hw, he⟩ := andB_iff.1 h
      have hf : found (indexOf (pts 42 6 20160 L34S.T)) (pts 42 6 20160 L34S.T)
          (unpack 42 6 (pcomp 42 6 (mask 6) (L34IX.Y q) (L34IX.YI q'))) = true := by
        unfold pts
        exact found_pts (Nat.le_of_ble_eq_true hw) (Nat.eq_of_beq_eq_true he)
      rw [hf, Bool.or_true]

theorem pairs_of {N : Array Tab} (hN : ∀ y ∈ N.toList, ∃ q < 48, y = unpack 42 6 (L34IX.Y q)) :
    (allBelow N.size fun i => allBelow N.size fun j =>
      invOK N[j]! && (!(powTab (comp 42 N[i]! (invTab 42 N[j]!)) 4 == idTab 42) ||
        found (indexOf (pts 42 6 20160 L34S.T)) (pts 42 6 20160 L34S.T)
          (comp 42 N[i]! (invTab 42 N[j]!)))) = true := by
  refine CFSG.KS.BfsReplay.allBelow_iff.2 fun i hi => CFSG.KS.BfsReplay.allBelow_iff.2 fun j hj => ?_
  obtain ⟨q, hq, eq⟩ := hN _ (Array.mem_toList_iff.2 (Array.getElem_mem hi))
  obtain ⟨q', hq', eq'⟩ := hN _ (Array.mem_toList_iff.2 (Array.getElem_mem hj))
  rw [getElem!_pos N i hi, getElem!_pos N j hj, eq, eq']
  exact pair_true hq hq'

theorem graphIdx_true : graphIdxOK = true := by
  unfold graphIdxOK
  dsimp only
  rw [hR.1, hS.1, rT.1]
  unfold r2PairsOK
  dsimp only
  exact pairs_of fun y hy => mem_r2 hy

end CertificateChecks.KernelLC.L34Idx

end
