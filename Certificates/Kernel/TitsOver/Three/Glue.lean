module

public import Certificates.Kernel.TitsOver.Three.Checks
public import Certificates.Kernel.TitsOver.Three.Gen
public import Certificates.Kernel.TitsOver.Three.Lens
public import Certificates.Kernel.TitsOver.Three.NChk
public import Certificates.Kernel.TitsOver.Three.PTests
public import Certificates.Kernel.TitsOver.Three.S0B0
public import Certificates.Kernel.TitsOver.Three.S0B1
public import Certificates.Kernel.TitsOver.Three.S1B0
public import Certificates.Kernel.TitsOver.Three.S1B1
public import Certificates.Kernel.TitsOver.Three.S2B0
public import Certificates.Kernel.TitsOver.Three.S2B1
public import Certificates.Kernel.TitsOver.Three.S2B2
public import Certificates.Kernel.TitsOver.Three.S2B3
public import Certificates.Kernel.TitsOver.Three.S3B0
public import Certificates.Kernel.TitsOver.Three.S3B1
public import Certificates.Kernel.TitsOver.Three.S3B2
public import Certificates.Kernel.TitsOver.Three.S3B3
public import Certificates.Kernel.TitsOver.Three.Loc0Checks
public import Certificates.Kernel.TitsOver.Three.Loc1Checks
public import Certificates.Kernel.TitsOver.Three.LocN0
public import Certificates.Kernel.TitsOver.Three.LocN1
public import Certificates.Kernel.TitsOver.TitsBase
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
public import Certificates.Kernel.EvenBN.DWord
public import CFSG.Certificates.Kernel.TitsOver.Pair

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsOver.Three

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.PEnum CFSG.KS.Row
open CFSG.KS.TitsOver CertificateChecks.KernelSpor.Tits2264 CertificateChecks.KernelEvenBN
open CFSG.StandardType.TitsThree CFSG.StandardType.TitsOvergroup CFSG.StandardType.TitsGenerators
open CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four.Native
open CertificateChecks.KernelTitsOver (titsBase titsD_baseFaithful baseOK_tits)

theorem gTb : pairData.gT.size = 2 ∧ ∀ k < 2, pairData.gT[k]! = unpack 1755 11 (Dk k) := by
  refine ⟨rfl, fun k hk => ?_⟩
  interval_cases k
  · exact titsDArr_eq (by decide)
  · exact titsDArr_eq (by decide)

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

theorem hgP : GensOK 1755 11 2 PE.G (pGens pairData) :=
  gens_bindT (D := pairData) gTb.1 gTb.2 dArrs_perm (ws := pairData.pW) rfl fun j hj =>
    band_e ((PK.allN_iff.1 k_pg) j hj)

theorem hgN : GensOK 1755 11 4 NE.G (nGens pairData) :=
  gens_bindT (D := pairData) gTb.1 gTb.2 dArrs_perm (ws := pairData.nW) rfl fun j hj =>
    band_e ((PK.allN_iff.1 k_ng) j hj)

theorem p_pt {i : Nat} (hi : i < PE.cnt) : penumPtK 1755 11 (mask 11) (1755 * 11) false PE.G PE.GI
    PE.k PE.cnt PE.T PE.PL PE.POS PE.SRT PE.SRI i = true :=
  penumSl_spec k_psl i (Nat.zero_le _) (by exact hi) hi

theorem n_pt {i : Nat} (hi : i < NE.cnt) : penumPtK 1755 11 (mask 11) (1755 * 11) false NE.G NE.GI
    NE.k NE.cnt NE.T NE.PL NE.POS NE.SRT NE.SRI i = true := by
  have e : NE.cnt = 216 := rfl
  by_cases h : i < 108
  · exact penumSl_spec n_sl0 i (Nat.zero_le _) (by omega) hi
  · exact penumSl_spec n_sl108 i (by omega) (by omega) hi

theorem hEP : enumBFS pairData.n (pGens pairData) pairData.pOrder =
      penumRec 1755 11 PE.cnt PE.T PE.PL ∧
    enumOK pairData.n (pGens pairData) (penumRec 1755 11 PE.cnt PE.T PE.PL) = true :=
  penumK_left_sound szOK1755 hgP k_ph (fun i hi => p_pt hi)

theorem hEN : enumBFS pairData.n (nGens pairData) pairData.nOrder =
      penumRec 1755 11 NE.cnt NE.T NE.PL ∧
    enumOK pairData.n (nGens pairData) (penumRec 1755 11 NE.cnt NE.T NE.PL) = true :=
  penumK_left_sound szOK1755 hgN k_nh (fun i hi => n_pt hi)

theorem hP : checkP pairData = true := checkP_ofT hEP rfl

theorem hN : checkN pairData = true := checkN_ofT hEN rfl

theorem hNorm : checkNormal pairData = true :=
  checkNormal_ofT szOK1755 hEP.1 (fun i hi => (pt_spec (p_pt hi)).1) hgP hgN
    (fun j hj => (PK.allN_iff.1 k_ngi) j hj) fun j hj i hi => by
      have h := band_e ((PK.allN_iff.1 ((PK.allN_iff.1 k_norm) j hj)) i hi)
      exact ⟨⟨_, h.1⟩, ⟨_, h.2⟩⟩

theorem hgS0 : GensOK 1755 11 6 S0E.G (sideGens pairData 0) :=
  gens_bindT (D := pairData) gTb.1 gTb.2 dArrs_perm (ws := pairData.sideW.getD 0 []) rfl
    fun j hj => band_e ((PK.allN_iff.1 k_sg0) j hj)
theorem hgS1 : GensOK 1755 11 6 S1E.G (sideGens pairData 1) :=
  gens_bindT (D := pairData) gTb.1 gTb.2 dArrs_perm (ws := pairData.sideW.getD 1 []) rfl
    fun j hj => band_e ((PK.allN_iff.1 k_sg1) j hj)
theorem hgS2 : GensOK 1755 11 10 S2E.G (sideGens pairData 2) :=
  gens_bindT (D := pairData) gTb.1 gTb.2 dArrs_perm (ws := pairData.sideW.getD 2 []) rfl
    fun j hj => band_e ((PK.allN_iff.1 k_sg2) j hj)
theorem hgS3 : GensOK 1755 11 10 S3E.G (sideGens pairData 3) :=
  gens_bindT (D := pairData) gTb.1 gTb.2 dArrs_perm (ws := pairData.sideW.getD 3 []) rfl
    fun j hj => band_e ((PK.allN_iff.1 k_sg3) j hj)

theorem s0_pt : ∀ i < S0E.cnt, penumPtBK 1755 11 (mask 11) (1755 * 11) S0E.G S0E.k S0E.cnt 6
    (r32 CertificateChecks.KernelMaxD2.TitsD.PT) S0E.T S0E.PL S0E.POS S0E.SRT S0E.SRI i = true := by
  intro i hi
  have e : S0E.cnt = 5616 := rfl
  have sl : ∀ q < 15, penumSlBK 1755 11 (mask 11) (1755 * 11) S0E.G S0E.k S0E.cnt 6
      (r32 CertificateChecks.KernelMaxD2.TitsD.PT) S0E.T S0E.PL S0E.POS S0E.SRT S0E.SRI (400 * q)
      400 = true := by
    intro q hq
    interval_cases q
    exacts [s0_sl0, s0_sl400, s0_sl800, s0_sl1200, s0_sl1600, s0_sl2000, s0_sl2400, s0_sl2800,
      s0_sl3200, s0_sl3600, s0_sl4000, s0_sl4400, s0_sl4800, s0_sl5200, s0_sl5600]
  exact penumSlB_spec (sl (i / 400) (by omega)) i (by omega) (by omega) hi

theorem s1_pt : ∀ i < S1E.cnt, penumPtBK 1755 11 (mask 11) (1755 * 11) S1E.G S1E.k S1E.cnt 6
    (r32 CertificateChecks.KernelMaxD2.TitsD.PT) S1E.T S1E.PL S1E.POS S1E.SRT S1E.SRI i = true := by
  intro i hi
  have e : S1E.cnt = 5616 := rfl
  have sl : ∀ q < 15, penumSlBK 1755 11 (mask 11) (1755 * 11) S1E.G S1E.k S1E.cnt 6
      (r32 CertificateChecks.KernelMaxD2.TitsD.PT) S1E.T S1E.PL S1E.POS S1E.SRT S1E.SRI (400 * q)
      400 = true := by
    intro q hq
    interval_cases q
    exacts [s1_sl0, s1_sl400, s1_sl800, s1_sl1200, s1_sl1600, s1_sl2000, s1_sl2400, s1_sl2800,
      s1_sl3200, s1_sl3600, s1_sl4000, s1_sl4400, s1_sl4800, s1_sl5200, s1_sl5600]
  exact penumSlB_spec (sl (i / 400) (by omega)) i (by omega) (by omega) hi

theorem s2_pt : ∀ i < S2E.cnt, penumPtBK 1755 11 (mask 11) (1755 * 11) S2E.G S2E.k S2E.cnt 6
    (r32 CertificateChecks.KernelMaxD2.TitsD.PT) S2E.T S2E.PL S2E.POS S2E.SRT S2E.SRI i = true := by
  intro i hi
  have e : S2E.cnt = 11232 := rfl
  have sl : ∀ q < 29, penumSlBK 1755 11 (mask 11) (1755 * 11) S2E.G S2E.k S2E.cnt 6
      (r32 CertificateChecks.KernelMaxD2.TitsD.PT) S2E.T S2E.PL S2E.POS S2E.SRT S2E.SRI (400 * q)
      400 = true := by
    intro q hq
    interval_cases q
    exacts [s2_sl0, s2_sl400, s2_sl800, s2_sl1200, s2_sl1600, s2_sl2000, s2_sl2400, s2_sl2800,
      s2_sl3200, s2_sl3600, s2_sl4000, s2_sl4400, s2_sl4800, s2_sl5200, s2_sl5600, s2_sl6000,
      s2_sl6400, s2_sl6800, s2_sl7200, s2_sl7600, s2_sl8000, s2_sl8400, s2_sl8800, s2_sl9200,
      s2_sl9600, s2_sl10000, s2_sl10400, s2_sl10800, s2_sl11200]
  exact penumSlB_spec (sl (i / 400) (by omega)) i (by omega) (by omega) hi

theorem s3_pt : ∀ i < S3E.cnt, penumPtBK 1755 11 (mask 11) (1755 * 11) S3E.G S3E.k S3E.cnt 6
    (r32 CertificateChecks.KernelMaxD2.TitsD.PT) S3E.T S3E.PL S3E.POS S3E.SRT S3E.SRI i = true := by
  intro i hi
  have e : S3E.cnt = 11232 := rfl
  have sl : ∀ q < 29, penumSlBK 1755 11 (mask 11) (1755 * 11) S3E.G S3E.k S3E.cnt 6
      (r32 CertificateChecks.KernelMaxD2.TitsD.PT) S3E.T S3E.PL S3E.POS S3E.SRT S3E.SRI (400 * q)
      400 = true := by
    intro q hq
    interval_cases q
    exacts [s3_sl0, s3_sl400, s3_sl800, s3_sl1200, s3_sl1600, s3_sl2000, s3_sl2400, s3_sl2800,
      s3_sl3200, s3_sl3600, s3_sl4000, s3_sl4400, s3_sl4800, s3_sl5200, s3_sl5600, s3_sl6000,
      s3_sl6400, s3_sl6800, s3_sl7200, s3_sl7600, s3_sl8000, s3_sl8400, s3_sl8800, s3_sl9200,
      s3_sl9600, s3_sl10000, s3_sl10400, s3_sl10800, s3_sl11200]
  exact penumSlB_spec (sl (i / 400) (by omega)) i (by omega) (by omega) hi

theorem hE0 : (enumBFS 1755 (sideGens pairData 0) 5616 = penumRec 1755 11 S0E.cnt S0E.T S0E.PL ∧
      enumOK 1755 (sideGens pairData 0) (penumRec 1755 11 S0E.cnt S0E.T S0E.PL) = true) ∧
    ∀ i < S0E.cnt, InH (pairG pairData titsS) 11 (S0E.T i) :=
  penumBK_left_sound szOK1755 hgS0
    (fun j hj => inH_of_wordT hSound gTb.1 gTb.2 dArrs_perm (band_e ((PK.allN_iff.1 k_sg0) j hj)).1
      (band_e ((PK.allN_iff.1 k_sg0) j hj)).2) hBF baseOK_tits k_sh0 s0_pt
theorem hE1 : (enumBFS 1755 (sideGens pairData 1) 5616 = penumRec 1755 11 S1E.cnt S1E.T S1E.PL ∧
      enumOK 1755 (sideGens pairData 1) (penumRec 1755 11 S1E.cnt S1E.T S1E.PL) = true) ∧
    ∀ i < S1E.cnt, InH (pairG pairData titsS) 11 (S1E.T i) :=
  penumBK_left_sound szOK1755 hgS1
    (fun j hj => inH_of_wordT hSound gTb.1 gTb.2 dArrs_perm (band_e ((PK.allN_iff.1 k_sg1) j hj)).1
      (band_e ((PK.allN_iff.1 k_sg1) j hj)).2) hBF baseOK_tits k_sh1 s1_pt
theorem hE2 : (enumBFS 1755 (sideGens pairData 2) 11232 = penumRec 1755 11 S2E.cnt S2E.T S2E.PL ∧
      enumOK 1755 (sideGens pairData 2) (penumRec 1755 11 S2E.cnt S2E.T S2E.PL) = true) ∧
    ∀ i < S2E.cnt, InH (pairG pairData titsS) 11 (S2E.T i) :=
  penumBK_left_sound szOK1755 hgS2
    (fun j hj => inH_of_wordT hSound gTb.1 gTb.2 dArrs_perm (band_e ((PK.allN_iff.1 k_sg2) j hj)).1
      (band_e ((PK.allN_iff.1 k_sg2) j hj)).2) hBF baseOK_tits k_sh2 s2_pt
theorem hE3 : (enumBFS 1755 (sideGens pairData 3) 11232 = penumRec 1755 11 S3E.cnt S3E.T S3E.PL ∧
      enumOK 1755 (sideGens pairData 3) (penumRec 1755 11 S3E.cnt S3E.T S3E.PL) = true) ∧
    ∀ i < S3E.cnt, InH (pairG pairData titsS) 11 (S3E.T i) :=
  penumBK_left_sound szOK1755 hgS3
    (fun j hj => inH_of_wordT hSound gTb.1 gTb.2 dArrs_perm (band_e ((PK.allN_iff.1 k_sg3) j hj)).1
      (band_e ((PK.allN_iff.1 k_sg3) j hj)).2) hBF baseOK_tits k_sh3 s3_pt

@[expose] noncomputable def SPL (k r : Nat) : Nat :=
  nIf(Nat.beq k 0, S0E.PL r, nIf(Nat.beq k 1, S1E.PL r, nIf(Nat.beq k 2, S2E.PL r, S3E.PL r)))

theorem side_eq : ∀ k < 4, sideEnum pairData k = penumRec 1755 11 (SC k) (ST k) (SPL k) ∧
    enumOK 1755 (sideGens pairData k) (penumRec 1755 11 (SC k) (ST k) (SPL k)) = true ∧
    SC k = pairData.sideOrder.getD k 0 ∧ ∀ q < SC k, InH (pairG pairData titsS) 11 (ST k q) := by
  intro k hk
  interval_cases k
  · have e1 : ST 0 = S0E.T := rfl
    have e2 : SPL 0 = S0E.PL := rfl
    have e3 : SC 0 = S0E.cnt := rfl
    rw [e1, e2, e3]
    refine ⟨by unfold sideEnum; exact hE0.1.1, hE0.1.2, rfl, hE0.2⟩
  · have e1 : ST 1 = S1E.T := rfl
    have e2 : SPL 1 = S1E.PL := rfl
    have e3 : SC 1 = S1E.cnt := rfl
    rw [e1, e2, e3]
    refine ⟨by unfold sideEnum; exact hE1.1.1, hE1.1.2, rfl, hE1.2⟩
  · have e1 : ST 2 = S2E.T := rfl
    have e2 : SPL 2 = S2E.PL := rfl
    have e3 : SC 2 = S2E.cnt := rfl
    rw [e1, e2, e3]
    refine ⟨by unfold sideEnum; exact hE2.1.1, hE2.1.2, rfl, hE2.2⟩
  · have e1 : ST 3 = S3E.T := rfl
    have e2 : SPL 3 = S3E.PL := rfl
    have e3 : SC 3 = S3E.cnt := rfl
    rw [e1, e2, e3]
    refine ⟨by unfold sideEnum; exact hE3.1.1, hE3.1.2, rfl, hE3.2⟩

theorem hSide : checkSide pairData = true :=
  checkSide_ofT (scnt := SC) (ST := ST) (SPL := SPL) rfl fun k hk => by
    obtain ⟨e, hok, hc, -⟩ := side_eq k hk
    refine ⟨?_, hok, hc⟩
    have : sideEnum pairData k = enumBFS pairData.n (sideGens pairData k)
      (pairData.sideOrder.getD k 0) := rfl
    rw [← this]
    exact e

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
  kN := NE.k
  cnt := NE.cnt
  NG := NE.G
  NGI0 := NE.GI
  NT := NE.T
  NPL := NE.PL
  NPOS := NE.POS
  NSRT := NE.SRT
  NSRI := NE.SRI
  NGI := NGI
  nr := 457
  REP := REP
  REPI := REPI
  np := 2
  kw := 22
  PT := r32 PT
  FS := FS
  KS := KS
  RB := RB
  H := H
  CN := r32 CN
  TP := 0
  TPI := 0
  th := 0
  CH := fun _ => 0
  NH := fun _ => 0
  L := r32 L
  hi := 28
  cw := 11
  nl := r32 MISC 0
  MK := rg 4096 (mask 4096) MK 0
  mj := 0
  mi := 0

theorem p_all : ∀ q < 19, allN 24 (fun d => repK 1755 11 2 22 NE.cnt (r32 PT) NE.T FS KS REP REPI RB
    H (Nat.add (Nat.add 1 (Nat.mul 24 q)) d)) = true := by
  intro q hq
  interval_cases q
  exacts [p_t0, p_t1, p_t2, p_t3, p_t4, p_t5, p_t6, p_t7, p_t8, p_t9, p_t10, p_t11, p_t12, p_t13,
    p_t14, p_t15, p_t16, p_t17, p_t18]

theorem hCP : HypsC PkP pairData.fpPts pairData.nOrder pairData.gOrder where
  hn := szOK1755
  hNt := fun i hi => (pt_spec (n_pt hi)).1
  hNL := enum_facts szOK1755 k_nh (fun i hi => n_pt hi) (fun j hj => (PK.allN_iff.1 k_ngi) j hj) k_lab
  hNc := rfl
  hR0 := Nat.eq_of_beq_eq_true k_r0
  hRi := fun i hi => (PK.allN_iff.1 k_ri) i hi
  hPts := ⟨rfl, fun t ht => ⟨Nat.eq_of_beq_eq_true (band_e ((PK.allN_iff.1 k_pts) t ht)).1,
    Nat.blt_eq.mp (band_e ((PK.allN_iff.1 k_pts) t ht)).2⟩⟩
  hS := fun s hs => (PK.allN_iff.1 k_srt) s hs
  hTest := by
    intro i h0 hi
    have h := (PK.allN_iff.1 (p_all ((i - 1) / 24) (by change i < 457 at hi; omega)))
      ((i - 1) % 24) (by omega)
    have e : Nat.add (Nat.add 1 (Nat.mul 24 ((i - 1) / 24))) ((i - 1) % 24) = i := by
      change 1 + 24 * ((i - 1) / 24) + (i - 1) % 24 = i
      omega
    rw [e] at h
    exact h
  hCnt := by
    intro i h0 hi
    have h := (PK.allN_iff.1 k_cnt) (i - 1) (by change i < 457 at hi; omega)
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
    change (rg 4096 (mask 4096) MK 0 i).beq (rg 4096 (mask 4096) MK 0 j) = false at h
    change rg 4096 (mask 4096) MK 0 i = rg 4096 (mask 4096) MK 0 j at e
    rw [e, Nat.beq_refl] at h
    exact absurd h (by decide)

theorem hr : RepB 1755 11 457 REP (repT pairData) :=
  repT_bindT szOK1755 gTb.1 gTb.2 dArrs_perm rfl (Nat.eq_of_beq_eq_true k_r0)
    fun i hi => (PK.allN_iff.1 k_rw) i hi

theorem hri : RepB 1755 11 457 REPI (repI pairData) :=
  repI_bindT hr fun i hi => (PK.allN_iff.1 k_ri) i hi

theorem hCover : checkCover pairData = true :=
  checkCover_ofT hCP rfl hEN.1 hr hri (by decide)

theorem hb : PairB pairData 11 457 PE.G PGI REP REPI where
  hn := szOK1755
  hP2 := rfl
  hgP := fun l hl => ⟨(hgP.2 l hl).1, (PK.allN_iff.1 k_pgi) l hl⟩
  hr := hr
  hri := hri
  hRi := fun i hi => (PK.allN_iff.1 k_ri) i hi
  hnr := rfl

theorem gen_all : ∀ i < 456, genK i = true := by
  intro i hi
  have hq : i / 114 < 4 := by omega
  have h : ∀ q < 4, allN 114 (fun d => genK (Nat.add (114 * q) d)) = true := by
    intro q hq
    interval_cases q
    exacts [k_gen0, k_gen1, k_gen2, k_gen3]
  have h' := (PK.allN_iff.1 (h (i / 114) hq)) (i % 114) (by omega)
  have e : Nat.add (114 * (i / 114)) (i % 114) = i := by
    change 114 * (i / 114) + i % 114 = i
    omega
  rw [e] at h'
  exact h'

theorem hGen : checkGen pairData = true :=
  checkGen_ofT hSound hBF baseOK_tits hb gTb.1 gTb.2
    ((Nat.eq_of_beq_eq_true k_klen).trans (Nat.eq_of_beq_eq_true k_rlen).symm)
    ((Nat.eq_of_beq_eq_true k_glen).trans (Nat.eq_of_beq_eq_true k_rlen).symm) fun i hi hk => by
    have h := gen_all i hi
    unfold genK at h
    have h' := band_e (bif_t (by rw [hk]; rfl) h)
    exact ⟨Nat.eq_of_beq_eq_true h'.1, fun j hj => (PK.allN_iff.1 h'.2) j hj⟩

theorem hSideMem : checkSideMem pairData = true := by
  refine checkSideMem_ofT (D := pairData) (w := 11) (scnt := SC) (ST := ST) (SPL := SPL) hb
    (fun k hk => (side_eq k hk).1) (fun k hk q hq => ((side_eq k hk).2.2.2 q hq).1) ?_
  intro i hi hk
  have hkl := Nat.blt_eq.mp ((PK.allN_iff.1 k_kind) i hi)
  have h := (PK.allN_iff.1 k_sm) i hi
  have hf : Nat.beq (pairData.kind[i]!) 0 = false := Bool.eq_false_iff.2 fun e => hk
    (Nat.eq_of_beq_eq_true e)
  have h' := band_e (bif_f hf h)
  exact ⟨by change pairData.kind[i]! - 1 < 4; omega, r32 SMQ i, Nat.blt_eq.mp h'.1,
    Nat.eq_of_beq_eq_true h'.2⟩

theorem hPair : pairCheck pairData = true := by
  unfold pairCheck
  rw [hInv, hP, hN, hNorm, hSide, hCover, hGen, hSideMem]
  rfl

theorem memW_len : ∀ k < 2, (memWords.getD k []).length = 4 := by decide

theorem hMemW : checkMemW pairData memWords = true :=
  checkMemW_ofT (scnt := SC) (ST := ST) (SPL := SPL) hSound hBF baseOK_tits gTb.1 gTb.2 dArrs_perm
    (by decide) (fun k hk => (side_eq k (by change k < 2 at hk; omega)).1)
    (fun k hk q hq => (side_eq k (by change k < 2 at hk; omega)).2.2.2 q hq) fun k hk wd hwd => by
      obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hwd
      have hl' : l < 4 := by rw [← memW_len k hk]; exact hl
      have h := band_e ((PK.allN_iff.1 ((PK.allN_iff.1 k_mw) k hk)) l hl')
      refine ⟨r32 MWQ (Nat.add (Nat.mul 4 k) l), Nat.blt_eq.mp h.1, ?_⟩
      have e : (memWords.getD k []).getD l [] = (memWords.getD k [])[l] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
      rw [← e]
      exact h.2

@[expose] noncomputable def PkC0 : Pk where
  n := 1755
  w := 11
  kG := 6
  Gp := S0E.G
  GIp := SGI0
  rcnt := C0RE.cnt
  RG := C0RE.G
  RGI := C0RE.GI
  RT := C0RE.T
  RPL := C0RE.PL
  RPOS := C0RE.POS
  RSRT := C0RE.SRT
  RSRI := C0RE.SRI
  kN := C0NE.k
  cnt := C0NE.cnt
  NG := C0NE.G
  NGI0 := C0NE.GI
  NT := C0NE.T
  NPL := C0NE.PL
  NPOS := C0NE.POS
  NSRT := C0NE.SRT
  NSRI := C0NE.SRI
  NGI := C0NGI
  nr := 2
  REP := C0REP
  REPI := C0REPI
  np := 1
  kw := 11
  PT := r32 C0PT
  FS := C0FS
  KS := C0KS
  RB := C0RB
  H := C0H
  CN := r32 C0CN
  TP := C0TT 0
  TPI := C0TT 1
  th := r32 C0MISC 0
  CH := C0CH
  NH := C0NH
  L := r32 C0L
  hi := 28
  cw := 11
  nl := r32 C0MISC 1
  MK := rg 1024 (mask 1024) C0MK 0
  mj := 2
  mi := 0

@[expose] noncomputable def PkC1 : Pk where
  n := 1755
  w := 11
  kG := 6
  Gp := S1E.G
  GIp := SGI1
  rcnt := C1RE.cnt
  RG := C1RE.G
  RGI := C1RE.GI
  RT := C1RE.T
  RPL := C1RE.PL
  RPOS := C1RE.POS
  RSRT := C1RE.SRT
  RSRI := C1RE.SRI
  kN := C1NE.k
  cnt := C1NE.cnt
  NG := C1NE.G
  NGI0 := C1NE.GI
  NT := C1NE.T
  NPL := C1NE.PL
  NPOS := C1NE.POS
  NSRT := C1NE.SRT
  NSRI := C1NE.SRI
  NGI := C1NGI
  nr := 2
  REP := C1REP
  REPI := C1REPI
  np := 2
  kw := 22
  PT := r32 C1PT
  FS := C1FS
  KS := C1KS
  RB := C1RB
  H := C1H
  CN := r32 C1CN
  TP := C1TT 0
  TPI := C1TT 1
  th := r32 C1MISC 0
  CH := C1CH
  NH := C1NH
  L := r32 C1L
  hi := 28
  cw := 11
  nl := r32 C1MISC 1
  MK := rg 1024 (mask 1024) C1MK 0
  mj := 3
  mi := 0

theorem c0n_pt {i : Nat} (hi : i < C0NE.cnt) : penumPtK 1755 11 (mask 11) (1755 * 11) false C0NE.G
    C0NE.GI C0NE.k C0NE.cnt C0NE.T C0NE.PL C0NE.POS C0NE.SRT C0NE.SRI i = true := by
  have e : C0NE.cnt = 432 := rfl
  have sl : ∀ lo, lo < 4 → penumSlK 1755 11 (mask 11) (1755 * 11) false C0NE.G C0NE.GI C0NE.k
      C0NE.cnt C0NE.T C0NE.PL C0NE.POS C0NE.SRT C0NE.SRI (108 * lo) 108 = true := by
    intro lo hlo
    interval_cases lo
    exacts [c0n_sl0, c0n_sl108, c0n_sl216, c0n_sl324]
  exact penumSl_spec (sl (i / 108) (by omega)) i (by omega) (by omega) hi

theorem c1n_pt {i : Nat} (hi : i < C1NE.cnt) : penumPtK 1755 11 (mask 11) (1755 * 11) false C1NE.G
    C1NE.GI C1NE.k C1NE.cnt C1NE.T C1NE.PL C1NE.POS C1NE.SRT C1NE.SRI i = true := by
  have e : C1NE.cnt = 432 := rfl
  have sl : ∀ lo, lo < 4 → penumSlK 1755 11 (mask 11) (1755 * 11) false C1NE.G C1NE.GI C1NE.k
      C1NE.cnt C1NE.T C1NE.PL C1NE.POS C1NE.SRT C1NE.SRI (108 * lo) 108 = true := by
    intro lo hlo
    interval_cases lo
    exacts [c1n_sl0, c1n_sl108, c1n_sl216, c1n_sl324]
  exact penumSl_spec (sl (i / 108) (by omega)) i (by omega) (by omega) hi

theorem hyps0 : Hyps (lLocalData 0 ()) PkC0 := by
  constructor
  case hn => exact szOK1755
  case hDn => exact rfl
  case hGs => exact rfl
  case hGb => exact fun j hj => (hgS0.2 j hj).1
  case hGp => exact k_sgi0
  case hRG => exact fun j hj => band_e ((PK.allN_iff.1 c0_rg) j hj)
  case hRh => exact c0_rh
  case hRp => exact fun i hi => penumSl_spec c0_rsl i (Nat.zero_le _) (by exact hi) hi
  case hRc => exact rfl
  case hNk => exact rfl
  case hNG => exact fun j hj => band_e ((PK.allN_iff.1 c0_ng) j hj)
  case hNh => exact c0_nh
  case hNp => exact fun i hi => c0n_pt hi
  case hNc => exact rfl
  case hNI => exact fun j hj => (PK.allN_iff.1 c0_ngi) j hj
  case hNorm => exact fun j hj i hi => band_e ((PK.allN_iff.1 ((PK.allN_iff.1 c0_norm) j hj)) i hi)
  case hMj => exact (by decide : 2 < 6)
  case hMi => exact (by decide : 0 < 2)
  case hMv =>
    dsimp only [PkC0]
    exact c0_mv
  case hTw => exact c0_tw
  case hTp => exact c0_tp
  case hTh => exact Nat.blt_eq.mp c0_th1
  case hTn => exact Nat.eq_of_beq_eq_true c0_th2
  case hTk => exact c0_tk
  case hC => exact fun k hk => (PK.allN_iff.1 c0_cent) k hk
  case hRn => exact rfl
  case hR0 => exact Nat.eq_of_beq_eq_true c0_r0
  case hRw =>
    intro i hi
    have hi0 : i = 0 := by change i < 1 at hi; omega
    subst hi0
    exact c0_rw
  case hRi => exact fun i hi => (PK.allN_iff.1 c0_ri) i hi
  case hPts =>
    refine ⟨rfl, fun t ht => ?_⟩
    have ht0 : t = 0 := by change t < 1 at ht; omega
    subst ht0
    exact ⟨Nat.eq_of_beq_eq_true c0_pts1, Nat.blt_eq.mp c0_pts2⟩
  case hS => exact fun s hs => (PK.allN_iff.1 c0_srt) s hs
  case hTest =>
    intro i h0 hi
    have hi1 : i = 1 := by change i < 2 at hi; omega
    subst hi1
    exact c0_test
  case hCnt =>
    intro i h0 hi
    have hi1 : i = 1 := by change i < 2 at hi; omega
    subst hi1
    exact Nat.eq_of_beq_eq_true c0_cnt
  case hSum => exact Nat.eq_of_beq_eq_true c0_sum
  case hL => exact c0_lab
  case hM => exact (by decide : 1755 ≤ 64 * 28)
  case hMK => exact fun i hi => Nat.eq_of_beq_eq_true ((PK.allN_iff.1 c0_mk) i hi)
  case hMd =>
    intro i hi j hj hij
    have hi0 : i = 0 := by change j < 2 at hj; omega
    have hj1 : j = 1 := by change j < 2 at hj; omega
    subst hi0 hj1
    refine Or.inl fun e => ?_
    have h := c0_mkd
    rw [Bool.not_eq_true'] at h
    change rg 1024 (mask 1024) C0MK 0 0 = rg 1024 (mask 1024) C0MK 0 1 at e
    rw [e, Nat.beq_refl] at h
    exact absurd h (by decide)
  case hGl => exact rfl
  case hGen =>
    intro i hi
    have hi0 : i = 0 := by change i < 1 at hi; omega
    subst hi0
    exact ⟨Nat.eq_of_beq_eq_true c0_gen1, fun j hj => (PK.allN_iff.1 c0_gen2) j hj⟩

theorem hyps1 : Hyps (lLocalData 1 ()) PkC1 := by
  constructor
  case hn => exact szOK1755
  case hDn => exact rfl
  case hGs => exact rfl
  case hGb => exact fun j hj => (hgS1.2 j hj).1
  case hGp => exact k_sgi1
  case hRG => exact fun j hj => band_e ((PK.allN_iff.1 c1_rg) j hj)
  case hRh => exact c1_rh
  case hRp => exact fun i hi => penumSl_spec c1_rsl i (Nat.zero_le _) (by exact hi) hi
  case hRc => exact rfl
  case hNk => exact rfl
  case hNG => exact fun j hj => band_e ((PK.allN_iff.1 c1_ng) j hj)
  case hNh => exact c1_nh
  case hNp => exact fun i hi => c1n_pt hi
  case hNc => exact rfl
  case hNI => exact fun j hj => (PK.allN_iff.1 c1_ngi) j hj
  case hNorm => exact fun j hj i hi => band_e ((PK.allN_iff.1 ((PK.allN_iff.1 c1_norm) j hj)) i hi)
  case hMj => exact (by decide : 3 < 6)
  case hMi => exact (by decide : 0 < 2)
  case hMv =>
    dsimp only [PkC1]
    exact c1_mv
  case hTw => exact c1_tw
  case hTp => exact c1_tp
  case hTh => exact Nat.blt_eq.mp c1_th1
  case hTn => exact Nat.eq_of_beq_eq_true c1_th2
  case hTk => exact c1_tk
  case hC => exact fun k hk => (PK.allN_iff.1 c1_cent) k hk
  case hRn => exact rfl
  case hR0 => exact Nat.eq_of_beq_eq_true c1_r0
  case hRw =>
    intro i hi
    have hi0 : i = 0 := by change i < 1 at hi; omega
    subst hi0
    exact c1_rw
  case hRi => exact fun i hi => (PK.allN_iff.1 c1_ri) i hi
  case hPts =>
    exact ⟨rfl, fun t ht => ⟨Nat.eq_of_beq_eq_true (band_e ((PK.allN_iff.1 c1_pts) t ht)).1,
      Nat.blt_eq.mp (band_e ((PK.allN_iff.1 c1_pts) t ht)).2⟩⟩
  case hS => exact fun s hs => (PK.allN_iff.1 c1_srt) s hs
  case hTest =>
    intro i h0 hi
    have hi1 : i = 1 := by change i < 2 at hi; omega
    subst hi1
    exact c1_test
  case hCnt =>
    intro i h0 hi
    have hi1 : i = 1 := by change i < 2 at hi; omega
    subst hi1
    exact Nat.eq_of_beq_eq_true c1_cnt
  case hSum => exact Nat.eq_of_beq_eq_true c1_sum
  case hL => exact c1_lab
  case hM => exact (by decide : 1755 ≤ 64 * 28)
  case hMK => exact fun i hi => Nat.eq_of_beq_eq_true ((PK.allN_iff.1 c1_mk) i hi)
  case hMd =>
    intro i hi j hj hij
    have hi0 : i = 0 := by change j < 2 at hj; omega
    have hj1 : j = 1 := by change j < 2 at hj; omega
    subst hi0 hj1
    refine Or.inl fun e => ?_
    have h := c1_mkd
    rw [Bool.not_eq_true'] at h
    change rg 1024 (mask 1024) C1MK 0 0 = rg 1024 (mask 1024) C1MK 0 1 at e
    rw [e, Nat.beq_refl] at h
    exact absurd h (by decide)
  case hGl => exact rfl
  case hGen =>
    intro i hi
    have hi0 : i = 0 := by change i < 1 at hi; omega
    subst hi0
    exact ⟨Nat.eq_of_beq_eq_true c1_gen1, fun j hj => (PK.allN_iff.1 c1_gen2) j hj⟩

theorem hLoc : allBelow 2 (fun k => Certificates.MaxD2Perm.check (lLocalData k ())) = true := by
  rw [allBelow_iff']
  intro k hk
  interval_cases k
  · exact check_of hyps0
  · exact check_of hyps1

theorem titsThree_check : titsThreeCheck () = true := by
  unfold titsThreeCheck
  rw [hPair, hMemW, hLoc]
  rfl

end CertificateChecks.KernelTitsOver.Three

end
