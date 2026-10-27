module

public import Certificates.Kernel.HSStd.M12FyChecks
public import CFSG.Certificates.Kernel.LeftOrbSound
public import CFSG.Certificates.Kernel.GrpWitSound
public import CFSG.Certificates.Kernel.Spor.HNAOrbSound
public import Certificates.Kernel.HSStd.PumpU3Glue
public import Certificates.Kernel.HSStd.PumpH43Glue
import CFSG.Certificates.Kernel.BfsPinSetSound
import CFSG.Certificates.Kernel.BfsPinUnpack
import CFSG.Certificates.Kernel.BfsPinAlg
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Certificates.Kernel.L34InvSound
public import CFSG.Certificates.Kernel.SporSch.MathieuOCSound
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHSStd.M12Fy

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34Inv CFSG.KC.GrpWit
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
open CFSG.EvenSporadicStandard.HSStd.FiveY
open CertificateChecks.KernelHSStd.PumpU3 (enumOKL_of_enumOK)
open CertificateChecks.KernelHSStd.PumpH43 (arrCertOKL_of)
open CFSG.KLie.CT (fget andB orB notB)

theorem all_pts {c : ArrCert} {N : Nat} {U : Nat → Array Nat}
    (hm : ∀ x, x ∈ c.pts ↔ ∃ i < N, U i = x) {f : Array Nat → Bool}
    (h : ∀ i < N, f (U i) = true) : c.pts.toList.all f = true := by
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨i, hi, rfl⟩ := (hm x).1 (Array.mem_toList_iff.1 hx)
  exact h i hi

theorem any_pts {c : ArrCert} {N : Nat} {U : Nat → Array Nat}
    (hm : ∀ x, x ∈ c.pts ↔ ∃ i < N, U i = x) {f : Array Nat → Bool} {i : Nat} (hi : i < N)
    (h : f (U i) = true) : c.pts.toList.any f = true := by
  rw [List.any_eq_true]
  exact ⟨U i, Array.mem_toList_iff.2 ((hm _).2 ⟨i, hi, rfl⟩), h⟩

theorem hps : ∀ p ∈ m12Keys, p < 12 := by decide

theorem m12OK_true : m12OK = true := by
  have hb := kBind
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq, and_assoc] at hb
  obtain ⟨sM, bM, sC, bC, sD, bD, bI0, bI1, nQ0, nQ1, nM, nC, nD, NM, NC, ND, NQ0, NQ1, r0, r1,
    tM, tC, tD, gQ⟩ := hb
  have gM : ∀ k < 2, m12Gens[k]! = unpack 12 6 (M.G k) := fun k hk =>
    unpack_eq_of_bindArrK (CFSG.KS.Raw.Orb.allN_iff.1 bM k hk)
  have gC : ∀ k < 4, m12CGens[k]! = unpack 12 6 (C.G k) := fun k hk =>
    unpack_eq_of_bindArrK (CFSG.KS.Raw.Orb.allN_iff.1 bC k hk)
  have gD : ∀ k < 2, m12DGens[k]! = unpack 12 6 (D.G k) := fun k hk =>
    unpack_eq_of_bindArrK (CFSG.KS.Raw.Orb.allN_iff.1 bD k hk)
  have gQ0 : ∀ k < 2, m12Gens[k]! = unpack 12 6 (Q0.G k) := fun k hk => by
    have h := CFSG.KS.Raw.Orb.allN_iff.1 gQ k hk
    rw [Bool.and_eq_true] at h
    rw [Nat.eq_of_beq_eq_true h.1]
    exact gM k hk
  have gQ1 : ∀ k < 2, m12Gens[k]! = unpack 12 6 (Q1.G k) := fun k hk => by
    have h := CFSG.KS.Raw.Orb.allN_iff.1 gQ k hk
    rw [Bool.and_eq_true] at h
    rw [Nat.eq_of_beq_eq_true h.2]
    exact gM k hk
  have eI0 : m12Inv0 = unpack 12 6 (Q0.T Q0.r0) := unpack_eq_of_bindArrK bI0
  have eI1 : m12Inv1 = unpack 12 6 (Q1.T Q1.r0) := unpack_eq_of_bindArrK bI1
  have clM : ∀ i < M.N, CFSG.KC.LeftOrb.closPtL 12 6 2 M.N M.G M.T M.E i = true := fun i hi => by
    have h := M.cl i (by rw [NM] at hi; omega)
    rwa [nM] at h
  have trM : ∀ i < M.N, CFSG.KC.ConjOrb.treePt 2 M.N 0 M.E M.D i = true := fun i hi =>
    M.tr i (by rw [NM] at hi; omega)
  have hMh : CFSG.KC.ConjOrb.headK 12 6 2 M.G M.GI = true := by rw [← nM]; exact M.h
  have clC : ∀ i < C.N, CFSG.KC.LeftOrb.closPtL 12 6 4 C.N C.G C.T C.E i = true := fun i hi => by
    have h := C.cl i (by rw [NC] at hi; omega)
    rwa [nC] at h
  have trC : ∀ i < C.N, CFSG.KC.ConjOrb.treePt 4 C.N 0 C.E C.D i = true := fun i hi =>
    C.tr i (by rw [NC] at hi; omega)
  have hCh : CFSG.KC.ConjOrb.headK 12 6 4 C.G C.GI = true := by rw [← nC]; exact C.h
  have clD : ∀ i < D.N, CFSG.KC.LeftOrb.closPtL 12 6 2 D.N D.G D.T D.E i = true := fun i hi => by
    have h := D.cl i (by rw [ND] at hi; omega)
    rwa [nD] at h
  have trD : ∀ i < D.N, CFSG.KC.ConjOrb.treePt 2 D.N 0 D.E D.D i = true := fun i hi =>
    D.tr i (by rw [ND] at hi; omega)
  have hDh : CFSG.KC.ConjOrb.headK 12 6 2 D.G D.GI = true := by rw [← nD]; exact D.h
  obtain ⟨okM, memM, szM⟩ := CFSG.KC.LeftOrb.enumBfs_of_left (fuel := 100000) sM gM hMh clM trM
    (by rw [NM]; omega) tM hps M.k (by rw [NM]; omega)
  obtain ⟨okC, memC, szC⟩ := CFSG.KC.LeftOrb.enumBfs_of_left (fuel := 2000) sC gC hCh clC trC
    (by rw [NC]; omega) tC hps C.k (by rw [NC]; omega)
  obtain ⟨okD, memD, szD⟩ := CFSG.KC.LeftOrb.enumBfs_of_left (fuel := 2000) sD gD hDh clD trD
    (by rw [ND]; omega) tD hps D.k (by rw [ND]; omega)
  have cQ0 : ∀ i < Q0.N, CFSG.KC.ConjOrb.closPt 12 6 Q0.ng Q0.N Q0.G Q0.GI Q0.T Q0.E i = true :=
    fun i hi => Q0.cl i (by rw [NQ0] at hi; omega)
  have tQ0 : ∀ i < Q0.N, CFSG.KC.ConjOrb.treePt 2 Q0.N Q0.r0 Q0.E Q0.D0 i = true :=
    fun i hi => Q0.tr0 i (by rw [NQ0] at hi; omega)
  have cQ1 : ∀ i < Q1.N, CFSG.KC.ConjOrb.closPt 12 6 Q1.ng Q1.N Q1.G Q1.GI Q1.T Q1.E i = true :=
    fun i hi => Q1.cl i (by rw [NQ1] at hi; omega)
  have tQ1 : ∀ i < Q1.N, CFSG.KC.ConjOrb.treePt 2 Q1.N Q1.r0 Q1.E Q1.D0 i = true :=
    fun i hi => Q1.tr0 i (by rw [NQ1] at hi; omega)
  have hp := kPerms
  simp only [Bool.and_eq_true] at hp
  obtain ⟨⟨⟨pC, pD⟩, pQ0⟩, pQ1⟩ := hp
  have vI0 : validA 12 m12Inv0 = true := by
    rw [eI0]
    exact validA_unpack (permsK_spec pQ0 _ (by rw [← NQ0]; exact r0))
  have vI1 : validA 12 m12Inv1 = true := by
    rw [eI1]
    exact validA_unpack (permsK_spec pQ1 _ (by rw [← NQ1]; exact r1))
  obtain ⟨okQ0, memQ0, szQ0⟩ := CFSG.KC.ConjOrb.arrBfs_of_orb (ng := 2) (fuel := 2000)
    (act := m12Act) (root := m12Inv0) (gs := m12Gens) (ps := m12Keys) (by rw [nQ0]) gQ0
    (fun _ _ _ => rfl) Q0.h cQ0 tQ0 r0 eI0 vI0 hps Q0.k (by rw [NQ0]; omega)
  obtain ⟨okQ1, memQ1, szQ1⟩ := CFSG.KC.ConjOrb.arrBfs_of_orb (ng := 2) (fuel := 2000)
    (act := m12Act) (root := m12Inv1) (gs := m12Gens) (ps := m12Keys) (by rw [nQ1]) gQ1
    (fun _ _ _ => rfl) Q1.h cQ1 tQ1 r1 eI1 vI1 hps Q1.k (by rw [NQ1]; omega)
  unfold m12OK m12Pts m12Pts0 m12Pts1 m12CPts m12DPts m12Cert m12CCert m12DCert m12Cls0 m12Cls1
  rw [sM]
  simp only [Bool.and_eq_true, and_assoc]
  have hsz : szOK 12 6 = true := (CFSG.KC.ConjOrb.headK_spec hMh).1
  have ppC : ∀ i < 240, PP 12 6 (C.T i) := fun i hi => PP_of_permOK hsz (permsK_spec pC i hi)
  have ppD : ∀ i < 60, PP 12 6 (D.T i) := fun i hi => PP_of_permOK hsz (permsK_spec pD i hi)
  have ppQ0 : ∀ i < 396, PP 12 6 (Q0.T i) := fun i hi => PP_of_permOK hsz (permsK_spec pQ0 i hi)
  have ppQ1 : ∀ i < 495, PP 12 6 (Q1.T i) := fun i hi => PP_of_permOK hsz (permsK_spec pQ1 i hi)
  have cM : ∀ i < 95040, canonK 12 6 (mask 6) (12 * 6) (M.T i) = true := fun i hi =>
    (CFSG.KC.LeftOrb.closPtL_spec (clM i (by rw [NM]; exact hi))).1
  have pa : PP 12 6 (Q0.T Q0.r0) := ppQ0 _ (by rw [← NQ0]; exact r0)
  have pb : PP 12 6 (Q1.T Q1.r0) := ppQ1 _ (by rw [← NQ1]; exact r1)
  have pe := PP.id hsz
  have hi := kInv
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hi
  obtain ⟨⟨⟨ia1, ia2⟩, ib1⟩, ib2⟩ := hi
  have memQ0' : ∀ x, x ∈ (arrBfs m12Act 2 (keyA 12 m12Keys) m12Inv0 2000).pts ↔
      ∃ i < 396, unpack 12 6 (Q0.T i) = x := by rw [← NQ0]; exact memQ0
  have memQ1' : ∀ x, x ∈ (arrBfs m12Act 2 (keyA 12 m12Keys) m12Inv1 2000).pts ↔
      ∃ i < 495, unpack 12 6 (Q1.T i) = x := by rw [← NQ1]; exact memQ1
  have memM' : ∀ x, x ∈ (enumBfs 12 m12Gens m12Keys 100000).pts ↔
      ∃ i < 95040, unpack 12 6 (M.T i) = x := by rw [← NM]; exact memM
  have memC' : ∀ x, x ∈ (enumBfs 12 m12CGens m12Keys 2000).pts ↔
      ∃ i < 240, unpack 12 6 (C.T i) = x := by rw [← NC]; exact memC
  have memD' : ∀ x, x ∈ (enumBfs 12 m12DGens m12Keys 2000).pts ↔
      ∃ i < 60, unpack 12 6 (D.T i) = x := by rw [← ND]; exact memD
  have g3 : isInvol12 m12Inv0 = true := by
    unfold isInvol12
    rw [vI0, eI0, compA_PP pa pa, idA_eq hsz, eqA_PP (pa.mul pa) pe, eqA_PP pa pe, ia1, ia2]
    rfl
  have g4 : isInvol12 m12Inv1 = true := by
    unfold isInvol12
    rw [vI1, eI1, compA_PP pb pb, idA_eq hsz, eqA_PP (pb.mul pb) pe, eqA_PP pb pe, ib1, ib2]
    rfl
  have key := covSl_spec (N := 95040) (L := 1440) (K := 66) rfl (fun s hs => cvAll s hs)
  have g9 : ((enumBfs 12 m12Gens m12Keys 100000).pts.toList.all fun x =>
      !eqA 12 (compA 12 x x) (idA 12) || eqA 12 x (idA 12) ||
        (arrBfs m12Act 2 (keyA 12 m12Keys) m12Inv0 2000).pts.toList.any (eqA 12 x) ||
        (arrBfs m12Act 2 (keyA 12 m12Keys) m12Inv1 2000).pts.toList.any (eqA 12 x)) = true := by
    refine all_pts memM' fun i hi => ?_
    have hc := cM i hi
    have hpe := CFSG.KC.L34KSnd.canon_pidn hsz
    rw [compA_unpack hc hc, idA_eq hsz, eqA_unpack (CFSG.KC.BfsPin.canonK_pcomp hc hc) hpe,
      eqA_unpack hc hpe]
    simp only [Bool.or_eq_true, Bool.not_eq_true']
    rcases key i hi with h1 | h1 | ⟨o, ho, j, hj, e⟩
    · left; left; right
      rw [h1]
      exact Nat.beq_refl _
    · left; left; left
      exact h1
    · match o, ho with
      | 0, _ =>
        left
        right
        change Q0.T j = M.T i at e
        change j < Q0.N at hj
        have hj' : j < 396 := by rw [← NQ0]; exact hj
        refine any_pts memQ0' hj' ?_
        rw [eqA_unpack hc (ppQ0 j hj').1, e]
        exact Nat.beq_refl _
      | 1, _ =>
        right
        change Q1.T j = M.T i at e
        change j < Q1.N at hj
        have hj' : j < 495 := by rw [← NQ1]; exact hj
        refine any_pts memQ1' hj' ?_
        rw [eqA_unpack hc (ppQ1 j hj').1, e]
        exact Nat.beq_refl _
  have g12 : (allLt m12CGens.size fun k =>
      eqA 12 (compA 12 m12Inv0 m12CGens[k]!) (compA 12 m12CGens[k]! m12Inv0) &&
        (enumBfs 12 m12Gens m12Keys 100000).pts.toList.any (eqA 12 m12CGens[k]!)) = true := by
    rw [allLt_iff, sC]
    intro k hk
    obtain ⟨e1, hj, e2⟩ := centMemK_spec kCent k hk
    have hgk := ((CFSG.KC.ConjOrb.headK_spec hCh).2 k hk).1
    rw [gC k hk, eI0, compA_unpack pa.1 hgk, compA_unpack hgk pa.1,
      eqA_unpack (CFSG.KC.BfsPin.canonK_pcomp pa.1 hgk) (CFSG.KC.BfsPin.canonK_pcomp hgk pa.1), e1,
      Nat.beq_refl, Bool.true_and]
    refine any_pts memM' hj ?_
    rw [eqA_unpack hgk (cM _ hj), e2]
    exact Nat.beq_refl _
  have g16 : ((enumBfs 12 m12CGens m12Keys 2000).pts.toList.all fun x =>
      (enumBfs 12 m12CGens m12Keys 2000).pts.toList.all fun y =>
        (enumBfs 12 m12DGens m12Keys 2000).pts.toList.any (eqA 12 (commutatorA 12 x y))) = true := by
    refine all_pts memC' fun a ha => all_pts memC' fun b hb => ?_
    have hq30 : a / 30 < 8 := Nat.div_lt_of_lt_mul (by omega)
    have hlo : Nat.mul 30 (a / 30) ≤ a := Nat.mul_div_le a 30
    have hhi : a < Nat.mul 30 (a / 30) + 30 := by
      have := Nat.lt_mul_div_succ a (show 0 < 30 by norm_num)
      change a < 30 * (a / 30) + 30
      rw [Nat.mul_succ] at this
      exact this
    obtain ⟨hq, e⟩ := commK_spec (cmAll (a / 30) hq30) a hlo hhi b
      (by rw [NC]; exact hb)
    rw [ND] at hq
    obtain ⟨e1, pc⟩ := CFSG.KS.HNA.commutatorA_unpack (ppC a ha) (ppC b hb)
    refine any_pts memD' hq ?_
    rw [e1, eqA_PP pc (ppD _ hq), e]
    exact Nat.beq_refl _
  have g17 : ((enumBfs 12 m12DGens m12Keys 2000).pts.toList.all fun d =>
      !eqA 12 (compA 12 d d) (idA 12) ||
        (arrBfs m12Act 2 (keyA 12 m12Keys) m12Inv0 2000).pts.toList.any
          (eqA 12 (compA 12 m12Inv0 d))) = true := by
    refine all_pts memD' fun d hd => ?_
    have pd := ppD d hd
    rw [compA_PP pd pd, idA_eq hsz, eqA_PP (pd.mul pd) pe]
    cases hsq : Nat.beq (pcomp 12 6 (mask 6) (D.T d) (D.T d)) (pidn 12 6)
    · rfl
    · obtain ⟨hj, e⟩ := invWitK_spec kInvD d hd hsq
      rw [Bool.not_true, Bool.false_or]
      refine any_pts memQ0' hj ?_
      rw [eI0, compA_PP pa pd, eqA_PP (pa.mul pd) (ppQ0 _ hj), e]
      exact Nat.beq_refl _
  refine ⟨enumOKL_of_enumOK okM, ?_, g3, g4, arrCertOKL_of okQ0, ?_, arrCertOKL_of okQ1, ?_, g9,
    enumOKL_of_enumOK okC, ?_, g12, enumOKL_of_enumOK okD, ?_, g16, g17⟩
  · rw [szM, NM]; rfl
  · rw [szQ0, NQ0]; rfl
  · rw [szQ1, NQ1]; rfl
  · rw [szC, NC]; rfl
  · rw [szD, ND]; rfl

end CertificateChecks.KernelHSStd.M12Fy

end
