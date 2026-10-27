module

public import Certificates.Kernel.TitsOver.Five.Checks
public import Certificates.Kernel.TitsOver.Five.PTests
public import Certificates.Kernel.TitsOver.Five.LTests
public import Certificates.Kernel.TitsOver.Five.LB0
public import Certificates.Kernel.TitsOver.Five.LB1
public import Certificates.Kernel.TitsOver.Five.LB2
public import Certificates.Kernel.TitsOver.Five.LB3
public import Certificates.Kernel.TitsOver.Five.LocChecks
public import Certificates.Kernel.TitsOver.Five.LocN
public import Certificates.Kernel.MaxD2.TitsD.Glue
public import Certificates.Kernel.TitsOver.TitsBase
public import CFSG.Certificates.Kernel.TitsOver.Pair
public import CFSG.Certificates.Kernel.TitsOver.MaxB

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsOver.Five

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.PEnum CFSG.KS.Row
open CFSG.KS.TitsOver CertificateChecks.KernelSpor.Tits2264 CertificateChecks.KernelEvenBN
open CFSG.StandardType.TitsFive CFSG.StandardType.TitsOvergroup CFSG.StandardType.TitsGenerators
open CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four.Native CertificateChecks.KernelMaxD2
open CertificateChecks.KernelTitsOver (titsBase titsD_baseFaithful baseOK_tits)

theorem gTb : pairData.gT.size = 2 ∧ ∀ k < 2, pairData.gT[k]! = unpack 1755 11 (Dk k) := by
  refine ⟨rfl, fun k hk => ?_⟩
  interval_cases k
  · exact titsDArr_eq (by decide)
  · exact titsDArr_eq (by decide)

theorem gTbL : lMaxData.gT.size = 2 ∧ ∀ k < 2, lMaxData.gT[k]! = unpack 1755 11 (Dk k) := gTb

theorem hInv : checkInv pairData = true := checkInv_ofT gTb.1 gTb.2 dArrs_perm

theorem hSound : Sound pairData titsS := by
  have hlen : titsS.length = pairData.gT.size := by simp [titsS, pairData]
  have hG : pairG pairData titsS = CFSG.Sporadic.Schreier.Tits.titsD :=
    (titsD_eq_closure_titsS).symm
  refine ⟨fun j => ?_, hlen, hInv, ?_⟩
  · rcases j with _ | _ | j
    · exact tab_titsDGen (j := 0) (by norm_num)
    · exact tab_titsDGen (j := 1) (by norm_num)
    · have h1 : pairData.gT.getD (j + 1 + 1) (idTab pairData.n) = idTab 1755 := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [gTb.1]; omega)]
        rfl
      rw [h1]
      exact TabRep.idTab
  · have h2 : Nat.card ↥(pairG pairData titsS) =
        Nat.card ↥(CFSG.Sporadic.Schreier.Tits.titsD : Subgroup (Equiv.Perm (Fin 1755))) :=
      congrArg (fun H : Subgroup (Equiv.Perm (Fin 1755)) => Nat.card ↥H) hG
    exact h2.trans CFSG.Sporadic.Schreier.Tits.card_titsD

theorem hBF : CFSG.Sporadic.Schreier.BaseFaithful (pairG pairData titsS) titsBase := by
  have hG : pairG pairData titsS = CFSG.Sporadic.Schreier.Tits.titsD :=
    (titsD_eq_closure_titsS).symm
  rw [hG]
  exact titsD_baseFaithful

theorem hgP : GensOK 1755 11 2 TitsD.RE.G (pGens pairData) :=
  gens_bindT (D := pairData) gTb.1 gTb.2 dArrs_perm (ws := pairData.pW) rfl fun j hj => by
    interval_cases j
    · exact ⟨TitsD.k_rg0, (PK.allN_iff.1 TitsD.k_rgc) 0 (by decide)⟩
    · exact ⟨TitsD.k_rg1, (PK.allN_iff.1 TitsD.k_rgc) 1 (by decide)⟩

theorem hgN : GensOK 1755 11 5 TitsD.NE.G (nGens pairData) :=
  gens_bindT (D := pairData) gTb.1 gTb.2 dArrs_perm (ws := pairData.nW) rfl fun j hj =>
    band_e ((PK.allN_iff.1 TitsD.k_ng) j hj)

theorem hEP : enumBFS pairData.n (pGens pairData) pairData.pOrder =
      penumRec 1755 11 TitsD.RE.cnt TitsD.RE.T TitsD.RE.PL ∧
    enumOK pairData.n (pGens pairData) (penumRec 1755 11 TitsD.RE.cnt TitsD.RE.T TitsD.RE.PL) =
      true :=
  penumK_left_sound szOK1755 hgP TitsD.k_rh
    (fun i hi => penumSl_spec TitsD.k_rsl i (Nat.zero_le _) (by exact hi) hi)

theorem hEN : enumBFS pairData.n (nGens pairData) pairData.nOrder =
      penumRec 1755 11 TitsD.NE.cnt TitsD.NE.T TitsD.NE.PL ∧
    enumOK pairData.n (nGens pairData) (penumRec 1755 11 TitsD.NE.cnt TitsD.NE.T TitsD.NE.PL) =
      true :=
  penumK_left_sound szOK1755 hgN TitsD.k_nh (fun i hi => TitsD.n_pt hi)

theorem hP : checkP pairData = true := checkP_ofT hEP rfl

theorem hN : checkN pairData = true := checkN_ofT hEN rfl

theorem hNorm : checkNormal pairData = true :=
  checkNormal_ofT szOK1755 hEP.1 (fun i hi => (pt_spec (penumSl_spec TitsD.k_rsl i (Nat.zero_le _)
    (by exact hi) hi)).1) hgP hgN (fun j hj => (PK.allN_iff.1 TitsD.k_ngi) j hj) fun j hj i hi => by
      have h := band_e ((PK.allN_iff.1 ((PK.allN_iff.1 TitsD.k_norm) j hj)) i hi)
      exact ⟨⟨_, h.1⟩, ⟨_, h.2⟩⟩

theorem hgL : GensOK 1755 11 4 LE.G (sideGens pairData 0) :=
  gens_bindT (D := pairData) gTb.1 gTb.2 dArrs_perm (ws := pairData.sideW.getD 0 []) rfl
    fun j hj => band_e ((PK.allN_iff.1 k_lg) j hj)

theorem hgL2 : GensOK 1755 11 4 LE.G (Certificates.MaxD2Perm.nGens lMaxData) :=
  nGens_bindM (D := lMaxData) gTbL.1 gTbL.2 dArrs_perm rfl fun j hj =>
    band_e ((PK.allN_iff.1 k_lg) j hj)

theorem hLin : ∀ j < 4, InH (pairG pairData titsS) 11 (LE.G j) := fun j hj =>
  inH_of_wordT hSound gTb.1 gTb.2 dArrs_perm (band_e ((PK.allN_iff.1 k_lg) j hj)).1
    (band_e ((PK.allN_iff.1 k_lg) j hj)).2

theorem lb_pt : ∀ i < LE.cnt, penumPtBK 1755 11 (mask 11) (1755 * 11) LE.G LE.k LE.cnt 6
    (r32 TitsD.PT) LE.T LE.PL LE.POS LE.SRT LE.SRI i = true := by
  intro i hi
  have e : LE.cnt = 7800 := rfl
  have sl : ∀ q < 20, penumSlBK 1755 11 (mask 11) (1755 * 11) LE.G LE.k LE.cnt 6 (r32 TitsD.PT)
      LE.T LE.PL LE.POS LE.SRT LE.SRI (400 * q) 400 = true := by
    intro q hq
    interval_cases q
    exacts [l_sl0, l_sl400, l_sl800, l_sl1200, l_sl1600, l_sl2000, l_sl2400, l_sl2800, l_sl3200,
      l_sl3600, l_sl4000, l_sl4400, l_sl4800, l_sl5200, l_sl5600, l_sl6000, l_sl6400, l_sl6800,
      l_sl7200, l_sl7600]
  exact penumSlB_spec (sl (i / 400) (by omega)) i (by omega) (by omega) hi

theorem hEL : (enumBFS 1755 (sideGens pairData 0) 7800 = penumRec 1755 11 LE.cnt LE.T LE.PL ∧
      enumOK 1755 (sideGens pairData 0) (penumRec 1755 11 LE.cnt LE.T LE.PL) = true) ∧
    ∀ i < LE.cnt, InH (pairG pairData titsS) 11 (LE.T i) :=
  penumBK_left_sound szOK1755 hgL hLin hBF baseOK_tits k_lh lb_pt

theorem hEL2 : (enumBFS 1755 (Certificates.MaxD2Perm.nGens lMaxData) 7800 =
      penumRec 1755 11 LE.cnt LE.T LE.PL ∧
      enumOK 1755 (Certificates.MaxD2Perm.nGens lMaxData) (penumRec 1755 11 LE.cnt LE.T LE.PL) =
        true) ∧ ∀ i < LE.cnt, InH (pairG pairData titsS) 11 (LE.T i) :=
  penumBK_left_sound szOK1755 hgL2 hLin hBF baseOK_tits k_lh lb_pt

theorem hSide : checkSide pairData = true :=
  checkSide_ofT (scnt := fun _ => LE.cnt) (ST := fun _ => LE.T) (SPL := fun _ => LE.PL) rfl
    fun k hk => by
      have hk0 : k = 0 := by change k < 1 at hk; omega
      subst hk0
      exact ⟨hEL.1.1, hEL.1.2, rfl⟩

@[expose] noncomputable def PkP : Pk where
  n := 1755
  w := 11
  kG := 2
  Gp := Dk
  GIp := DIk
  rcnt := 0
  RG := fun _ => 0
  RGI := fun _ => 0
  RT := fun _ => 0
  RPL := fun _ => 0
  RPOS := fun _ => 0
  RSRT := fun _ => 0
  RSRI := fun _ => 0
  kN := TitsD.NE.k
  cnt := TitsD.NE.cnt
  NG := TitsD.NE.G
  NGI0 := TitsD.NE.GI
  NT := TitsD.NE.T
  NPL := TitsD.NE.PL
  NPOS := TitsD.NE.POS
  NSRT := TitsD.NE.SRT
  NSRI := TitsD.NE.SRI
  NGI := TitsD.NGI
  nr := 25
  REP := REP
  REPI := REPI
  np := 6
  kw := 66
  PT := r32 TitsD.PT
  FS := TitsD.FS
  KS := TitsD.KS
  RB := RB
  H := H
  CN := r32 CN
  TP := 0
  TPI := 0
  th := 0
  CH := fun _ => 0
  NH := fun _ => 0
  L := r32 TitsD.L
  hi := 28
  cw := 11
  nl := r32 TitsD.MISC 1
  MK := rg 512 (mask 512) MK 0
  mj := 0
  mi := 0

theorem p_all : ∀ q < 8, allN 3 (fun d => repK 1755 11 6 66 TitsD.NE.cnt (r32 TitsD.PT) TitsD.NE.T
    TitsD.FS TitsD.KS REP REPI RB H (Nat.add (Nat.add 1 (Nat.mul 3 q)) d)) = true := by
  intro q hq
  interval_cases q
  exacts [p_t0, p_t1, p_t2, p_t3, p_t4, p_t5, p_t6, p_t7]

theorem hCP : HypsC PkP pairData.fpPts pairData.nOrder pairData.gOrder where
  hn := szOK1755
  hNt := fun i hi => (pt_spec (TitsD.n_pt hi)).1
  hNL := enum_facts szOK1755 TitsD.k_nh (fun i hi => TitsD.n_pt hi)
    (fun j hj => (PK.allN_iff.1 TitsD.k_ngi) j hj) TitsD.k_lab
  hNc := rfl
  hR0 := Nat.eq_of_beq_eq_true k_r0
  hRi := fun i hi => (PK.allN_iff.1 k_ri) i hi
  hPts := ⟨rfl, fun t ht => ⟨Nat.eq_of_beq_eq_true (band_e ((PK.allN_iff.1 TitsD.k_pts) t ht)).1,
    Nat.blt_eq.mp (band_e ((PK.allN_iff.1 TitsD.k_pts) t ht)).2⟩⟩
  hS := fun s hs => (PK.allN_iff.1 TitsD.k_srt) s hs
  hTest := by
    intro i h0 hi
    have h := (PK.allN_iff.1 (p_all ((i - 1) / 3) (by change i < 25 at hi; omega)))
      ((i - 1) % 3) (by omega)
    have e : Nat.add (Nat.add 1 (Nat.mul 3 ((i - 1) / 3))) ((i - 1) % 3) = i := by
      change 1 + 3 * ((i - 1) / 3) + (i - 1) % 3 = i
      omega
    rw [e] at h
    exact h
  hCnt := by
    intro i h0 hi
    have h := (PK.allN_iff.1 k_cnt) (i - 1) (by change i < 25 at hi; omega)
    have e : Nat.succ (i - 1) = i := by omega
    rw [e] at h
    exact Nat.eq_of_beq_eq_true h
  hSum := Nat.eq_of_beq_eq_true k_sum
  hM := by decide
  hMK := fun i hi => Nat.eq_of_beq_eq_true ((PK.allN_iff.1 k_mk) i hi)
  hMd := by
    intro i hi j hj hij
    refine Or.inl fun e => ?_
    have h := bnot_e (bif_t (Nat.blt_eq.mpr hij) ((PK.allN_iff.1 ((PK.allN_iff.1 k_mkd) i hi)) j hj))
    change (rg 512 (mask 512) MK 0 i).beq (rg 512 (mask 512) MK 0 j) = false at h
    change rg 512 (mask 512) MK 0 i = rg 512 (mask 512) MK 0 j at e
    rw [e, Nat.beq_refl] at h
    exact absurd h (by decide)

theorem hr : RepB 1755 11 25 REP (repT pairData) :=
  repT_bindT szOK1755 gTb.1 gTb.2 dArrs_perm rfl (Nat.eq_of_beq_eq_true k_r0)
    fun i hi => (PK.allN_iff.1 k_rw) i hi

theorem hri : RepB 1755 11 25 REPI (repI pairData) :=
  repI_bindT hr fun i hi => (PK.allN_iff.1 k_ri) i hi

theorem hCover : checkCover pairData = true :=
  checkCover_ofT hCP rfl hEN.1 hr hri (by decide)

theorem hb : PairB pairData 11 25 TitsD.RE.G PGI REP REPI where
  hn := szOK1755
  hP2 := rfl
  hgP := fun l hl => ⟨(hgP.2 l hl).1, (PK.allN_iff.1 k_pgi) l hl⟩
  hr := hr
  hri := hri
  hRi := fun i hi => (PK.allN_iff.1 k_ri) i hi
  hnr := rfl

theorem kind23 : ∀ i < 24, pairData.kind[i]! ≠ 0 → i = 23 := by decide

theorem hGen : checkGen pairData = true :=
  checkGen_ofT hSound hBF baseOK_tits hb gTb.1 gTb.2 rfl rfl fun i hi hk => by
    have h := (PK.allN_iff.1 k_gen) i hi
    have h' := band_e (bif_t (by rw [hk]; rfl) h)
    exact ⟨Nat.eq_of_beq_eq_true h'.1, fun j hj => (PK.allN_iff.1 h'.2) j hj⟩

theorem hE0 : sideEnum pairData 0 = penumRec 1755 11 LE.cnt LE.T LE.PL := by
  unfold sideEnum
  exact hEL.1.1

theorem kind23' : pairData.kind[23]! - 1 = 0 := by decide

theorem hSideMem : checkSideMem pairData = true := by
  refine checkSideMem_ofT (D := pairData) (w := 11) (scnt := fun _ => LE.cnt) (ST := fun _ => LE.T)
    (SPL := fun _ => LE.PL) hb ?_ (fun k _ q hq => (hEL.2 q hq).1) ?_
  · intro k hk
    have hk0 : k = 0 := by change k < 1 at hk; omega
    subst hk0
    exact hE0
  · intro i hi hk
    have h23 := kind23 i hi hk
    subst h23
    rw [kind23']
    exact ⟨Nat.zero_lt_one, r32 LSM 0, Nat.blt_eq.mp k_sm1, Nat.eq_of_beq_eq_true k_sm2⟩

theorem hSideGen : checkSideGen pairData sideGenWords = true :=
  checkSideGen_ofT (SG := fun _ j => LE.G j) hSound hBF baseOK_tits hb
    (fun k hk j hj => by
      have hk0 : k = 0 := by change k < 1 at hk; omega
      subst hk0
      exact (hgL.2 j (by rw [← hgL.1]; exact hj)).1)
    rfl fun i hi hk => by
      have h23 := kind23 i hi hk
      subst h23
      rw [kind23']
      refine ⟨Nat.zero_lt_one, by rw [hgL.1]; rfl, fun j hj => ?_⟩
      exact (PK.allN_iff.1 k_sg) j (by rw [← hgL.1]; exact hj)

theorem hPair : pairCheck pairData = true := by
  unfold pairCheck
  rw [hInv, hP, hN, hNorm, hSide, hCover, hGen, hSideMem]
  rfl

@[expose] noncomputable def PkL : Pk where
  n := 1755
  w := 11
  kG := 2
  Gp := Dk
  GIp := DIk
  rcnt := 0
  RG := fun _ => 0
  RGI := fun _ => 0
  RT := fun _ => 0
  RPL := fun _ => 0
  RPOS := fun _ => 0
  RSRT := fun _ => 0
  RSRI := fun _ => 0
  kN := LE.k
  cnt := LE.cnt
  NG := LE.G
  NGI0 := LE.GI
  NT := LE.T
  NPL := LE.PL
  NPOS := LE.POS
  NSRT := LE.SRT
  NSRI := LE.SRI
  NGI := LGI
  nr := 7
  REP := LREP
  REPI := LREPI
  np := 3
  kw := 33
  PT := r32 LPT
  FS := LFS
  KS := LKS
  RB := LRB
  H := LH
  CN := r32 LCN
  TP := 0
  TPI := 0
  th := 0
  CH := fun _ => 0
  NH := fun _ => 0
  L := r32 LL
  hi := 28
  cw := 11
  nl := r32 LMISC 0
  MK := rg 128 (mask 128) LMK 0
  mj := 0
  mi := 0
  RB2 := LRB2
  H2 := LH2
  PQ := fun i j => r32 LPQ (Nat.add (Nat.mul 7 i) j)

theorem lT0 : LE.T 0 = pidn 1755 11 := by
  have h := k_lh
  unfold penumHdK at h
  simp only [PK.bAnd_eq, Bool.and_eq_true] at h
  exact Nat.eq_of_beq_eq_true h.2.2.1

theorem hCL : HypsC PkL lMaxData.fpPts lMaxData.nOrder lMaxData.gOrder where
  hn := szOK1755
  hNt := fun i hi => (hEL2.2 i hi).1
  hNL := lperm_of_tree (par := parOf LE.PL) (lab := labOf LE.PL) szOK1755 lT0
    (fun i hi h0 => by
      obtain ⟨a, b, c, -⟩ := (penumPtB_spec (lb_pt i hi)).1 h0
      exact ⟨a, b, c⟩)
    (fun j hj => (PK.allN_iff.1 k_lgi) j hj) l_lab
  hNc := rfl
  hR0 := Nat.eq_of_beq_eq_true k_lr0
  hRi := fun i hi => (PK.allN_iff.1 k_lri) i hi
  hPts := ⟨rfl, fun t ht => ⟨Nat.eq_of_beq_eq_true (band_e ((PK.allN_iff.1 k_lpts) t ht)).1,
    Nat.blt_eq.mp (band_e ((PK.allN_iff.1 k_lpts) t ht)).2⟩⟩
  hS := fun s hs => (PK.allN_iff.1 l_srt) s hs
  hTest := by
    intro i h0 hi
    change i < 7 at hi
    interval_cases i
    exacts [l_t1, l_t2, l_t3, l_t4, l_t5, l_t6]
  hCnt := by
    intro i h0 hi
    have h := (PK.allN_iff.1 k_lcnt) (i - 1) (by change i < 7 at hi; omega)
    have e : Nat.succ (i - 1) = i := by omega
    rw [e] at h
    exact Nat.eq_of_beq_eq_true h
  hSum := Nat.eq_of_beq_eq_true k_lsum
  hM := by decide
  hMK := fun i hi => Nat.eq_of_beq_eq_true ((PK.allN_iff.1 k_lmk) i hi)
  hMd := by
    intro i hi j hj hij
    have h := bif_t (Nat.blt_eq.mpr hij) ((PK.allN_iff.1 ((PK.allN_iff.1 l_pk) i hi)) j hj)
    by_cases e : rg 128 (mask 128) LMK 0 i = rg 128 (mask 128) LMK 0 j
    · right
      rw [e, Nat.beq_refl] at h
      exact h
    · exact Or.inl e

theorem hrL : RepB 1755 11 7 LREP (Certificates.MaxD2Perm.repT lMaxData) :=
  repT_bindM szOK1755 gTbL.1 gTbL.2 dArrs_perm rfl (Nat.eq_of_beq_eq_true k_lr0)
    fun i hi => (PK.allN_iff.1 k_lrw) i hi

theorem hriL : RepB 1755 11 7 LREPI (Certificates.MaxD2Perm.repI lMaxData) :=
  repI_bindM hrL fun i hi => (PK.allN_iff.1 k_lri) i hi

theorem hEnL : Certificates.MaxD2Perm.nEnum lMaxData = penumRec 1755 11 LE.cnt LE.T LE.PL := by
  unfold Certificates.MaxD2Perm.nEnum
  exact hEL2.1.1

theorem hLgen : Certificates.MaxD2Perm.dcGenerate lMaxData (Certificates.MaxD2Perm.repT lMaxData)
    (Certificates.MaxD2Perm.repI lMaxData) = true :=
  dcGenerate_ofM (D := lMaxData) (w := 11) (kG := 2) (Gp := Dk) (kN := 4) (NG := LE.G) (NGI := LGI)
    szOK1755 gTbL.1 gTbL.2 hgL2 (fun j hj => (PK.allN_iff.1 k_lgi) j hj) hrL hriL
    (fun i hi => (PK.allN_iff.1 k_lri) i hi) rfl rfl fun i hi => by
      have h := band_e ((PK.allN_iff.1 k_lgen) i hi)
      exact ⟨Nat.eq_of_beq_eq_true h.1, fun j hj => (PK.allN_iff.1 h.2) j hj⟩

theorem hLMax : lMaxCheck = true := by
  have h1 : Certificates.MaxD2Perm.checkInv lMaxData = true :=
    checkInv_ofM (D := lMaxData) gTbL.1 gTbL.2 dArrs_perm
  have h2 : Certificates.MaxD2Perm.checkN lMaxData = true :=
    checkN_ofM (D := lMaxData) (w := 11) (cnt := LE.cnt) (T := LE.T) (PL := LE.PL) hEL2.1 rfl
  have h3 : invsOK lMaxData.n (Certificates.MaxD2Perm.nGens lMaxData)
      (Certificates.MaxD2Perm.nGensI lMaxData) = true :=
    invsN_ofM (D := lMaxData) (w := 11) (kN := 4) (NG := LE.G) (NGI := LGI) hgL2
      (fun j hj => (PK.allN_iff.1 k_lgi) j hj)
  have h4 : Certificates.MaxD2Perm.checkMax lMaxData = true :=
    checkMax_ofM (D := lMaxData) (C := PkL) hCL rfl hEnL hrL hriL hLgen
  unfold lMaxCheck
  rw [h1, h2, h3, h4]
  rfl

theorem lTabs_eq : lTabs () = Certificates.MaxD2Perm.nGens lMaxData := rfl

@[expose] noncomputable def PkC : Pk where
  n := 1755
  w := 11
  kG := 4
  Gp := LE.G
  GIp := LGI
  rcnt := CRE.cnt
  RG := CRE.G
  RGI := CRE.GI
  RT := CRE.T
  RPL := CRE.PL
  RPOS := CRE.POS
  RSRT := CRE.SRT
  RSRI := CRE.SRI
  kN := CNE.k
  cnt := CNE.cnt
  NG := CNE.G
  NGI0 := CNE.GI
  NT := CNE.T
  NPL := CNE.PL
  NPOS := CNE.POS
  NSRT := CNE.SRT
  NSRI := CNE.SRI
  NGI := CNGI
  nr := 2
  REP := CREP
  REPI := CREPI
  np := 1
  kw := 11
  PT := r32 CPT
  FS := CFS
  KS := CKS
  RB := CRB
  H := CH
  CN := r32 CCN
  TP := CTT 0
  TPI := CTT 1
  th := r32 CMISC 0
  CH := CCH
  NH := CNH
  L := r32 CL
  hi := 28
  cw := 11
  nl := r32 CMISC 1
  MK := rg 2048 (mask 2048) CMK 0
  mj := 2
  mi := 0

theorem cn_pt {i : Nat} (hi : i < CNE.cnt) : penumPtK 1755 11 (mask 11) (1755 * 11) false CNE.G
    CNE.GI CNE.k CNE.cnt CNE.T CNE.PL CNE.POS CNE.SRT CNE.SRI i = true := by
  have e : CNE.cnt = 300 := rfl
  have sl : ∀ lo, lo < 3 → penumSlK 1755 11 (mask 11) (1755 * 11) false CNE.G CNE.GI CNE.k CNE.cnt
      CNE.T CNE.PL CNE.POS CNE.SRT CNE.SRI (100 * lo) 100 = true := by
    intro lo hlo
    interval_cases lo
    exacts [cn_sl0, cn_sl100, cn_sl200]
  exact penumSl_spec (sl (i / 100) (by omega)) i (by omega) (by omega) hi

theorem hypsC : Hyps (lLocalData ()) PkC := by
  constructor
  case hn => exact szOK1755
  case hDn => exact rfl
  case hGs => exact rfl
  case hGb =>
    intro j hj
    change (lTabs ())[j]! = _
    rw [lTabs_eq]
    exact (hgL2.2 j hj).1
  case hGp => exact k_lgi
  case hRG => exact fun j hj => band_e ((PK.allN_iff.1 c_rg) j hj)
  case hRh => exact c_rh
  case hRp => exact fun i hi => penumSl_spec c_rsl i (Nat.zero_le _) (by exact hi) hi
  case hRc => exact rfl
  case hNk => exact rfl
  case hNG => exact fun j hj => band_e ((PK.allN_iff.1 c_ng) j hj)
  case hNh => exact c_nh
  case hNp => exact fun i hi => cn_pt hi
  case hNc => exact rfl
  case hNI => exact fun j hj => (PK.allN_iff.1 c_ngi) j hj
  case hNorm => exact fun j hj i hi => band_e ((PK.allN_iff.1 ((PK.allN_iff.1 c_norm) j hj)) i hi)
  case hMj => exact (by decide : 2 < 4)
  case hMi => exact (by decide : 0 < 2)
  case hMv =>
    dsimp only [PkC]
    exact c_mv
  case hTw => exact c_tw
  case hTp => exact c_tp
  case hTh => exact Nat.blt_eq.mp c_th1
  case hTn => exact Nat.eq_of_beq_eq_true c_th2
  case hTk => exact c_tk
  case hC => exact fun k hk => (PK.allN_iff.1 c_cent) k hk
  case hRn => exact rfl
  case hR0 => exact Nat.eq_of_beq_eq_true c_r0
  case hRw =>
    intro i hi
    have hi0 : i = 0 := by change i < 1 at hi; omega
    subst hi0
    exact c_rw
  case hRi => exact fun i hi => (PK.allN_iff.1 c_ri) i hi
  case hPts =>
    refine ⟨rfl, fun t ht => ?_⟩
    have ht0 : t = 0 := by change t < 1 at ht; omega
    subst ht0
    exact ⟨Nat.eq_of_beq_eq_true c_pts1, Nat.blt_eq.mp c_pts2⟩
  case hS => exact fun s hs => (PK.allN_iff.1 c_srt) s hs
  case hTest =>
    intro i h0 hi
    have hi1 : i = 1 := by change i < 2 at hi; omega
    subst hi1
    exact c_test
  case hCnt =>
    intro i h0 hi
    have hi1 : i = 1 := by change i < 2 at hi; omega
    subst hi1
    exact Nat.eq_of_beq_eq_true c_cnt
  case hSum => exact Nat.eq_of_beq_eq_true c_sum
  case hL => exact c_lab
  case hM => exact (by decide : 1755 ≤ 64 * 28)
  case hMK => exact fun i hi => Nat.eq_of_beq_eq_true ((PK.allN_iff.1 c_mk) i hi)
  case hMd =>
    intro i hi j hj hij
    have hi0 : i = 0 := by change j < 2 at hj; omega
    have hj1 : j = 1 := by change j < 2 at hj; omega
    subst hi0 hj1
    refine Or.inl fun e => ?_
    have h := c_mkd
    rw [Bool.not_eq_true'] at h
    change rg 2048 (mask 2048) CMK 0 0 = rg 2048 (mask 2048) CMK 0 1 at e
    rw [e, Nat.beq_refl] at h
    exact absurd h (by decide)
  case hGl => exact rfl
  case hGen =>
    intro i hi
    have hi0 : i = 0 := by change i < 1 at hi; omega
    subst hi0
    exact ⟨Nat.eq_of_beq_eq_true c_gen1, fun j hj => (PK.allN_iff.1 c_gen2) j hj⟩

theorem hLoc : Certificates.MaxD2Perm.check (lLocalData ()) = true := check_of hypsC

theorem titsFive_check : titsFiveCheck () = true := by
  unfold titsFiveCheck
  rw [hPair, hSideGen, hLMax, hLoc]
  rfl

end CertificateChecks.KernelTitsOver.Five

end
