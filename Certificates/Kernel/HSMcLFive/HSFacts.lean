module

public import Certificates.Kernel.HSMcLFive.HSChecks
public import Certificates.Kernel.HS100.Five
public import Certificates.Kernel.HS100.Chain
public import CFSG.Certificates.Kernel.FiveLocKSound
public import CFSG.Certificates.Kernel.Misc.PermWitSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Misc.ArrEnumSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHSMcLFive

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail CFSG.KC.BfsPin
open CFSG.KC.B3S3K CFSG.KC.K426K CFSG.KC.FiveLocK CFSG.RankThree.Native CFSG.RankThree.PartOne
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer
open CertificateChecks.KernelHS100
open CFSG.Monster.B.Co2 (allLt_iff)

theorem arrF {j : ℕ} (hj : j < 82) : hs100FiveArr j = unpack 100 7 (F j) := fiveArr_eq j hj

theorem pF {j : ℕ} (hj : j < 82) : permB 100 7 (F j) = true := Orb.allN_iff.1 permF j hj

theorem bindLit {gs : Array (Array ℕ)} {m c : ℕ} {G : ℕ → ℕ} (hs : gs.size = m) (hc : c + m ≤ 82)
    (hgs : ∀ j < m, gs[j]! = hs100FiveArr (c + j)) (hG : allN m (fun j => Nat.beq (G j) (F (c + j))) = true) :
    BindA 100 7 gs m G :=
  ⟨hs, fun j hj => by rw [hgs j hj, arrF (by omega), Nat.eq_of_beq_eq_true (Orb.allN_iff.1 hG j hj)]⟩

theorem bindF {gs : Array (Array ℕ)} {m c : ℕ} (hs : gs.size = m) (hc : c + m ≤ 82)
    (hgs : ∀ j < m, gs[j]! = hs100FiveArr (c + j)) : BindA 100 7 gs m (fun j => F (c + j)) :=
  bindLit hs hc hgs (Orb.allN_iff.2 fun _ _ => Nat.beq_refl _)

theorem permFc {m c : ℕ} (hc : c + m ≤ 82) : ∀ j < m, permB 100 7 (F (c + j)) = true :=
  fun _ hj => pF (by omega)

theorem bindL : BindA 100 7 hs100FiveLines 31 (fun j => F (2 + j)) :=
  bindF (by simp [hs100FiveLines]) (by norm_num) fun j hj => by
    unfold hs100FiveLines
    rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn, Nat.add_comm]

theorem bindH : BindA 100 7 hs100FiveTransporters 31 (fun j => F (33 + j)) :=
  bindF (by simp [hs100FiveTransporters]) (by norm_num) fun j hj => by
    unfold hs100FiveTransporters
    rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn, Nat.add_comm]

theorem line_eq {j : ℕ} (hj : j < 31) : hs100FiveLines[j]! = unpack 100 7 (F (2 + j)) :=
  bindL.2 j hj

theorem bindC0 : BindA 100 7 hs100FiveC0Gens 3 (fun j => F (64 + j)) :=
  bindF rfl (by norm_num) fun j hj => by interval_cases j <;> rfl

theorem bindC2 : BindA 100 7 hs100FiveC2Gens 4 (fun j => F (67 + j)) :=
  bindF rfl (by norm_num) fun j hj => by interval_cases j <;> rfl

theorem bindC23 : BindA 100 7 hs100FiveC23Gens 4 (fun j => F (71 + j)) :=
  bindF rfl (by norm_num) fun j hj => by interval_cases j <;> rfl

theorem bindA0 : BindA 100 7 hs100FiveA0Gens 2 (fun j => F (75 + j)) :=
  bindF rfl (by norm_num) fun j hj => by interval_cases j <;> rfl

theorem bindA23 : BindA 100 7 hs100FiveA23Gens 3 (fun j => F (77 + j)) :=
  bindF rfl (by norm_num) fun j hj => by interval_cases j <;> rfl

theorem hps : ∀ p ∈ hs100RBaseArr.toList, p < 100 := by decide

theorem keys_eq : hs100RBaseArr.toList = hs100FiveKeys := rfl

theorem hpk : ∀ p ∈ hs100FiveKeys, p < 100 := by decide

theorem hgD0 : Nat.beq (ED.G 0) (cmt 100 7 (F 68) (F 69)) = true := hgens.2.2.2.1

theorem hgD1 : Nat.beq (ED.G 1) (F 69) = true := hgens.2.2.2.2

theorem getOfFn {N : ℕ} {T : ℕ → ℕ} {pts : Array (Array ℕ)}
    (h : pts = Array.ofFn (n := N) fun i => unpack 100 7 (T i.val)) :
    pts.size = N ∧ ∀ i < N, pts[i]! = unpack 100 7 (T i) := by
  subst h
  exact ⟨Array.size_ofFn, fun i hi => by rw [getElem!_pos _ i (by simpa using hi),
    Array.getElem_ofFn]⟩

theorem c0f : hs100FiveC0Cert.pts.size = 50 ∧ ∀ i < 50, hs100FiveC0Cert.pts[i]! = unpack 100 7 (C0.T i) :=
  getOfFn c0_pts

theorem c2f : hs100FiveC2Cert.pts.size = 600 ∧
    ∀ i < 600, hs100FiveC2Cert.pts[i]! = unpack 100 7 (C2.T i) := getOfFn c2_pts

theorem c23f : hs100FiveC23Cert.pts.size = 1000 ∧
    ∀ i < 1000, hs100FiveC23Cert.pts[i]! = unpack 100 7 (C23.T i) := getOfFn c23_pts

theorem c0p : ∀ i < 50, permB 100 7 (C0.T i) = true := fun i hi => permB_of_pp (c0_pp i hi)

theorem c2p : ∀ i < 600, permB 100 7 (C2.T i) = true := fun i hi => permB_of_pp (c2_pp i hi)

theorem c23p : ∀ i < 1000, permB 100 7 (C23.T i) = true := fun i hi => permB_of_pp (c23_pp i hi)

abbrev EnumFacts (gs : Array (Array ℕ)) (c : ArrCert) (N : ℕ) (T : ℕ → ℕ) : Prop :=
  enumOK 100 gs hs100FiveKeys c = true ∧ c.pts.size = N ∧ ∀ i < N, c.pts[i]! = unpack 100 7 (T i)

theorem enumQ : EnumFacts hs100FiveQGens hs100FiveQCert 125 EQ.T := by
  have h := enum_of (ps := hs100FiveKeys) (fuel := 130)
    (bindLit (gs := hs100FiveQGens) (m := 2) (G := EQ.G) (c := 0) rfl (by norm_num) (fun j hj => by interval_cases j <;> rfl)
      hgens.1) (fun k hk => by
        rw [Nat.eq_of_beq_eq_true (Orb.allN_iff.1 hgens.1 k hk)]
        exact pF (by omega)) EQ.ok (hpk) EQ.keys (by rw [Nat.eq_of_beq_eq_true hnums.1]; omega)
  rw [Nat.eq_of_beq_eq_true hnums.1] at h
  exact h

theorem enumA0 : EnumFacts hs100FiveA0Gens hs100FiveA0Cert 25 EA0.T := by
  have h := enum_of (ps := hs100FiveKeys) (fuel := 30)
    (bindLit (gs := hs100FiveA0Gens) (m := 2) (G := EA0.G) (c := 75) rfl (by norm_num) (fun j hj => by interval_cases j <;> rfl)
      hgens.2.1) (fun k hk => by
        rw [Nat.eq_of_beq_eq_true (Orb.allN_iff.1 hgens.2.1 k hk)]
        exact pF (by omega)) EA0.ok (hpk) EA0.keys
    (by rw [Nat.eq_of_beq_eq_true hnums.2.2.1]; omega)
  rw [Nat.eq_of_beq_eq_true hnums.2.2.1] at h
  exact h

theorem enumA23 : EnumFacts hs100FiveA23Gens hs100FiveA23Cert 125 EA23.T := by
  have h := enum_of (ps := hs100FiveKeys) (fuel := 130)
    (bindLit (gs := hs100FiveA23Gens) (m := 3) (G := EA23.G) (c := 77) rfl (by norm_num) (fun j hj => by interval_cases j <;> rfl)
      hgens.2.2.1) (fun k hk => by
        rw [Nat.eq_of_beq_eq_true (Orb.allN_iff.1 hgens.2.2.1 k hk)]
        exact pF (by omega)) EA23.ok (hpk) EA23.keys
    (by rw [Nat.eq_of_beq_eq_true hnums.2.2.2.2.1]; omega)
  rw [Nat.eq_of_beq_eq_true hnums.2.2.2.2.1] at h
  exact h

theorem pQ : ∀ i < 125, permB 100 7 (EQ.T i) = true := fun i hi =>
  Orb.allN_iff.1 EQ.perm i (by rw [Nat.eq_of_beq_eq_true hnums.1]; exact hi)

theorem pA0 : ∀ i < 25, permB 100 7 (EA0.T i) = true := fun i hi =>
  Orb.allN_iff.1 EA0.perm i (by rw [Nat.eq_of_beq_eq_true hnums.2.2.1]; exact hi)

theorem pA23 : ∀ i < 125, permB 100 7 (EA23.T i) = true := fun i hi =>
  Orb.allN_iff.1 EA23.perm i (by rw [Nat.eq_of_beq_eq_true hnums.2.2.2.2.1]; exact hi)

theorem pD : ∀ i < 60, permB 100 7 (ED.T i) = true := fun i hi =>
  Orb.allN_iff.1 ED.perm i (by rw [Nat.eq_of_beq_eq_true hnums.2.2.2.2.2.2.1]; exact hi)

theorem pCmt : permB 100 7 (cmt 100 7 (F 68) (F 69)) = true :=
  permB_pcomp hsz (permB_pcomp hsz (pF (by norm_num)) (pF (by norm_num)))
    (permB_pcomp hsz (permB_pinvS hsz (pF (by norm_num))) (permB_pinvS hsz (pF (by norm_num))))

theorem dGen0 : hs100FiveDGens[0]! = unpack 100 7 (cmt 100 7 (F 68) (F 69)) := by
  change commutatorA 100 hs100FiveC2Gens[1]! hs100FiveC2Gens[2]! = _
  rw [bindC2.2 1 (by norm_num), bindC2.2 2 (by norm_num),
    commutator_unpack hsz (pF (by norm_num)) (pF (by norm_num))]
  rfl

private theorem arr2_get1 {α} [Inhabited α] (a b : α) : #[a, b][1]! = b := rfl

theorem bindD : BindA 100 7 hs100FiveDGens 2 ED.G := by
  refine ⟨rfl, fun j hj => ?_⟩
  interval_cases j
  · rw [dGen0, Nat.eq_of_beq_eq_true hgD0]
  · rw [Nat.eq_of_beq_eq_true hgD1, hs100FiveDGens, arr2_get1]
    exact bindC2.2 2 (by norm_num)

theorem pDG : ∀ l < 2, permB 100 7 (ED.G l) = true := by
  intro l hl
  interval_cases l
  · rw [Nat.eq_of_beq_eq_true hgD0]
    exact pCmt
  · rw [Nat.eq_of_beq_eq_true hgD1]
    exact pF (by norm_num)

theorem dpts : hs100FiveDCert.pts = Array.ofFn (n := ED.N) fun i => unpack 100 7 (ED.T i.val) :=
  enumBfs_pts_base bindD.1 bindD.2 ED.ok (hpk) ED.keys
    (by rw [Nat.eq_of_beq_eq_true hnums.2.2.2.2.2.2.1]; omega)

theorem denum : enumOK 100 hs100FiveDGens hs100FiveKeys hs100FiveDCert = true :=
  enumOK_of_bfsK_base bindD.1 bindD.2 (fun k hk => pDG k hk) ED.ok (hpk) ED.keys
    (by rw [Nat.eq_of_beq_eq_true hnums.2.2.2.2.2.2.1]; omega)

theorem dfacts : hs100FiveDCert.pts.size = 60 ∧
    ∀ i < 60, hs100FiveDCert.pts[i]! = unpack 100 7 (ED.T i) := by
  have h := getOfFn dpts
  rw [Nat.eq_of_beq_eq_true hnums.2.2.2.2.2.2.1] at h
  exact h

theorem dsimple : conjSimpleOK 100 hs100FiveKeys hs100FiveDCert = true := by
  have hN := Nat.eq_of_beq_eq_true hnums.2.2.2.2.2.2.1
  refine CFSG.KC.PermWit.conjSimpleOK_of_ctree (WT := WT) hsz (hpk) denum dpts
    (fun i hi => pD i (by rw [← hN]; exact hi)) (Nat.eq_of_beq_eq_true dT0)
    (fun i hi j hj e => ?_) (fun k hk => ?_)
  · have hK : keysSK 100 7 hs100FiveKeys ED.N ED.T ED.SK = true := ED.keys
    rw [keyA_unpack hpk, keyA_unpack hpk] at e
    exact keysSK_spec hK i hi j hj e
  · have h := Orb.allN_iff.1 ctree k hk
    rw [Bool.or_eq_true] at h
    exact h.imp id fun h' => Orb.allN_iff.1 h'

theorem binds0 : Binds 100 7 H0.S 15 8 H0.BP hs100Case0Arrs hs100Case0BaseArr := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [hs100Case0Arrs], fun j hj => ?_,
    by decide +kernel, bget0⟩
  have h := CFSG.KC.Misc.HexFlat.hexTable3_sound H0X.all j hj
  rw [← H0X.eq] at h
  rw [hs100Case0Arrs, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn, h,
    ← Nat.eq_of_beq_eq_true (Orb.allN_iff.1 hchains.1 j hj)]

theorem binds2 : Binds 100 7 H2.S 15 10 H2.BP hs100Case2Arrs hs100Case2BaseArr := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [hs100Case2Arrs], fun j hj => ?_,
    by decide +kernel, bget2⟩
  have h := CFSG.KC.Misc.HexFlat.hexTable3_sound H2X.all j hj
  rw [← H2X.eq] at h
  rw [hs100Case2Arrs, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn, h,
    ← Nat.eq_of_beq_eq_true (Orb.allN_iff.1 hchains.2.1 j hj)]

theorem binds23 : Binds 100 7 H23.S 13 9 H23.BP hs100Case23Arrs hs100Case23BaseArr := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [hs100Case23Arrs], fun j hj => ?_,
    by decide +kernel, bget23⟩
  have h := CFSG.KC.Misc.HexFlat.hexTable3_sound H23X.all j hj
  rw [← H23X.eq] at h
  rw [hs100Case23Arrs, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn, h,
    ← Nat.eq_of_beq_eq_true (Orb.allN_iff.1 hchains.2.2 j hj)]

theorem pHP {j : ℕ} (hj : j < 16) : permB 100 7 (HP.F j) = true := Orb.allN_iff.1 pHPall j hj

theorem caseChain_of {kS nb BP : ℕ} {PS PSI LR TR TRI : ℕ → ℕ} {S : Array (Array ℕ)}
    {base : Array ℕ} {W : Array (List ℤ)} {D : List (List ℤ)} (hb : Binds 100 7 PS kS nb BP S base)
    (hp : allN kS (fun j => permOK 100 7 (mask 7) (100 * 7) (PS j) (PSI j)) = true)
    (hh : headK 100 7 (mask 7) (100 * 7) (pidn 100 7) PS PSI kS 3 D nb BP = true)
    (hl : LevelsOK 100 7 PS PSI LR TR TRI kS nb BP)
    (hs : ∀ i < nb, ∀ s < 1, schK 100 7 (mask 7) (100 * 7) (pidn 100 7) PS PSI LR TR TRI kS BP nb i
      (stepsAt 100 7 PS kS BP i) (s * 100) 100 = true)
    (hW : CFSG.Sporadic.Schreier.Co3.Native.wordsArr 3 kS D = W) (hk : 3 ≤ kS)
    (h : (Nat.beq (PS 0) (HP.F 0) && Nat.beq (PS 1) (HP.F 1) && Nat.beq (PS 2) (HP.F 15)) = true) :
    caseChainOK 100 S base W (hs100Arr 0) (hs100Arr 1) (hs100Arr 15) = true := by
  have hc := rawChainK_sound (chunks := 1) hb hh hl (by norm_num) hs
  rw [hW] at hc
  have hP : ∀ j < kS, permB 100 7 (PS j) = true := fun j hj =>
    permB_of_pp (pp_of_permOK hsz (Orb.allN_iff.1 hp j hj))
  simp only [Bool.and_eq_true] at h
  unfold caseChainOK
  rw [hc, hb.2.2.2.2.1 0 (by omega), hb.2.2.2.2.1 1 (by omega), hb.2.2.2.2.1 2 (by omega),
    hs100Arr_eq 0 (by norm_num), hs100Arr_eq 1 (by norm_num), hs100Arr_eq 15 (by norm_num),
    eqA_unpack' hsz (hP 0 (by omega)) (pHP (by norm_num)),
    eqA_unpack' hsz (hP 1 (by omega)) (pHP (by norm_num)),
    eqA_unpack' hsz (hP 2 (by omega)) (pHP (by norm_num)), h.1.1, h.1.2, h.2]
  rfl

theorem chain0 : caseChainOK 100 hs100Case0Arrs hs100Case0BaseArr hs100Case0Words (hs100Arr 0)
    (hs100Arr 1) (hs100Arr 15) = true :=
  caseChain_of binds0 hperm0 H0.head H0.hl H0.hs (by decide +kernel) (by norm_num) hheads.1

theorem chain2 : caseChainOK 100 hs100Case2Arrs hs100Case2BaseArr hs100Case2Words (hs100Arr 0)
    (hs100Arr 1) (hs100Arr 15) = true :=
  caseChain_of binds2 hperm2 H2.head H2.hl H2.hs (by decide +kernel) (by norm_num) hheads.2.1

theorem chain23 : caseChainOK 100 hs100Case23Arrs hs100Case23BaseArr hs100Case23Words
    (hs100Arr 0) (hs100Arr 1) (hs100Arr 15) = true :=
  caseChain_of binds23 hperm23 H23.head H23.hl H23.hs (by decide +kernel) (by norm_num) hheads.2.2

theorem siftPF {G : ℕ} (h : siftOK 100 7 5 HC.LR HC.TRI HC.BP G = true) :
    siftA 100 hs100PLevels hs100BaseArr 0 (unpack 100 7 G) = true :=
  siftA_of_siftOK binds HC.perm HC.hl h

theorem siftRF {G : ℕ} (h : siftOK 100 7 6 KernelMisc.HSMcL.C2.LR KernelMisc.HSMcL.C2.TRI
    KernelMisc.HSMcL.C2.BP G = true) : siftA 100 hs100RLevels hs100RBaseArr 0 (unpack 100 7 G) = true :=
  siftA_of_siftOK KernelMisc.HSMcL.c2_binds KernelMisc.HSMcL.c2_perm KernelMisc.HSMcL.C2.hl h

theorem qfacts : linesOK 100 hs100FiveQGens hs100FiveKeys hs100FiveQCert hs100FiveLines = true ∧
    allLt hs100FiveQGens.size
      (fun l => siftA 100 hs100PLevels hs100BaseArr 0 hs100FiveQGens[l]!) = true ∧
    transOK 100 hs100FiveTransporters hs100FiveLines hs100FiveRec hs100RLevels hs100RBaseArr = true ∧
    hs100FiveRec.getD 0 0 = 0 ∧ hs100FiveRec.getD 2 0 = 2 ∧ hs100FiveRec.getD 23 0 = 23 ∧
    allLt 31 (fun j => hs100FiveRec.getD j 0 == 0 || hs100FiveRec.getD j 0 == 2 ||
      hs100FiveRec.getD j 0 == 23) = true := by
  obtain ⟨h1, h2, h3⟩ := enumQ
  refine ⟨linesOK_of hsz h1 h2 h3 pQ bindL lines, ?_,
    transOK_of hsz bindH bindL (permFc (by norm_num)) (fun j hj => by
      rw [bindH.2 j hj]
      exact siftRF (Orb.allN_iff.1 siftH j hj)) trans, by decide, by decide, by decide,
    by rw [allLt_iff]; decide⟩
  rw [allLt_iff]
  intro l hl
  have hl2 : l < 2 := hl
  rw [(bindF (gs := hs100FiveQGens) (m := 2) (c := 0) rfl (by norm_num)
    (fun j hj => by interval_cases j <;> rfl)).2 l hl2]
  exact siftPF (by simpa only [Nat.zero_add] using Orb.allN_iff.1 siftQ l hl2)

theorem case0 : caseChainOK 100 hs100Case0Arrs hs100Case0BaseArr hs100Case0Words (hs100Arr 0)
      (hs100Arr 1) (hs100Arr 15) = true ∧
    centOK 100 hs100Case0Arrs hs100Case0BaseArr hs100FiveLines[0]! hs100Case0Rels
      hs100FiveC0Gens hs100FiveKeys hs100FiveC0Cert 50 = true ∧
    normalOK 100 hs100FiveC0Gens hs100FiveA0Gens hs100FiveKeys hs100FiveC0Cert hs100FiveA0Cert
      25 hs100PLevels hs100BaseArr = true ∧
    selfCentOK 100 hs100FiveA0Gens hs100FiveC0Cert hs100FiveA0Cert = true ∧
    eqA 100 hs100FiveC0Gens[0]! hs100FiveLines[0]! = true := by
  obtain ⟨a1, a2, a3⟩ := enumA0
  refine ⟨chain0, ?_, ?_, ?_, ?_⟩
  · rw [centOK_eq, line_eq (by norm_num)]
    have htail : allN (rcnt (H0.LR 0)) (ptailBranchK 100 7 H0.LR H0.TR H0.BP (F 2) (pw 100 7 (F 2))
        hs100Case0Rels 50 C0.T 8) = true := by
      rw [Nat.eq_of_beq_eq_true rc.1, show (50 : ℕ) = C0.N from rfl]
      exact ptailBranchIdxK_le (ES := C0.S) (allN_of_blocks (L := 25) (K := 4)
        (f := ptailBranchIdxK 100 7 H0.LR H0.TR H0.BP (F 2) (pw 100 7 (F 2)) hs100Case0Rels C0.N C0.T
          C0.S 8) tailX_all)
    exact centOKP_of hsz binds0 hperm0 H0.hl (pF (by norm_num)) rels0 bindC0 comm0
      (fun k hk => siftA_of_siftOK binds0 hperm0 H0.hl (Orb.allN_iff.1 siftC0 k hk)) c0_enumOK
      c0f.1 c0f.2 c0p (by norm_num) htail
  · rw [normalOK_eq]
    exact normalOKP_of hsz a1 a2 a3 pA0 c0f.1 c0f.2 c0p bindC0 (permFc (by norm_num)) bindA0
      (permFc (by norm_num)) (fun l hl => siftPF (Orb.allN_iff.1 siftA0 l hl)) rfl normal0
  · exact selfCentOK_of hsz a2 a3 pA0 c0f.1 c0f.2 c0p bindA0 (permFc (by norm_num)) self0
  · rw [bindC0.2 0 (by norm_num), line_eq (by norm_num), eqA_unpack' hsz (pF (by norm_num))
      (pF (by norm_num))]
    exact eq0

theorem case2 : caseChainOK 100 hs100Case2Arrs hs100Case2BaseArr hs100Case2Words (hs100Arr 0)
      (hs100Arr 1) (hs100Arr 15) = true ∧
    centOK 100 hs100Case2Arrs hs100Case2BaseArr hs100FiveLines[2]! hs100Case2Rels
      hs100FiveC2Gens hs100FiveKeys hs100FiveC2Cert 600 = true ∧
    derivedOK 100 hs100FiveC2Gens hs100FiveDGens hs100FiveKeys hs100FiveC2Cert hs100FiveDCert
      hs100FiveDWit[0]! hs100FiveDWit[1]! hs100FiveLines[2]! hs100PLevels hs100BaseArr = true ∧
    eqA 100 hs100FiveC2Gens[0]! hs100FiveLines[2]! = true := by
  refine ⟨chain2, ?_, ?_, ?_⟩
  · rw [centOK_eq, line_eq (by norm_num)]
    have htail : allN (rcnt (H2.LR 0)) (ptailBranchK 100 7 H2.LR H2.TR H2.BP (F 4) (pw 100 7 (F 4))
        hs100Case2Rels 600 C2.T 10) = true := by
      rw [Nat.eq_of_beq_eq_true rc.2.1, show (600 : ℕ) = C2.N from rfl]
      exact ptailBranchIdxK_le (ES := C2.S) (allN_of_blocks (L := 25) (K := 4)
        (f := ptailBranchIdxK 100 7 H2.LR H2.TR H2.BP (F 4) (pw 100 7 (F 4)) hs100Case2Rels C2.N C2.T
          C2.S 10) tailY_all)
    exact centOKP_of hsz binds2 hperm2 H2.hl (pF (by norm_num)) rels2 bindC2 comm2
      (fun k hk => siftA_of_siftOK binds2 hperm2 H2.hl (Orb.allN_iff.1 siftC2 k hk)) c2_enumOK
      c2f.1 c2f.2 c2p (by norm_num) htail
  · have hc : hs100FiveDWit[0]! = unpack 100 7 (F 80) := by
      change hs100FiveArr 80 = _
      exact arrF (by norm_num)
    have hd : hs100FiveDWit[1]! = unpack 100 7 (F 81) := by
      change hs100FiveArr 81 = _
      exact arrF (by norm_num)
    rw [hc, hd, line_eq (by norm_num)]
    refine derivedOK_of (derivedLeOK_of hsz denum dfacts.1 dfacts.2 pD bindC2 (permFc (by norm_num))
      bindD pDG rfl derivedLe) (validA_of (pF (by norm_num))) (validA_of (pF (by norm_num)))
      (any_of_memIdxK hsz c2f.1 c2f.2 c2p cdMem.1) (any_of_memIdxK hsz c2f.1 c2f.2 c2p cdMem.2)
      ?_ ?_ dsimple (zPart_of hsz c2f.1 c2f.2 c2p bindD pDG (pF (by norm_num)) zD) ?_
    · rw [bindC2.2 2 (by norm_num), commutator_unpack hsz (pF (by norm_num)) (pF (by norm_num)),
        eqA_unpack' hsz (pF (by norm_num)) (permB_pcomp hsz (permB_pcomp hsz (pF (by norm_num))
          (pF (by norm_num))) (permB_pcomp hsz (permB_pinvS hsz (pF (by norm_num)))
            (permB_pinvS hsz (pF (by norm_num)))))]
      exact cdComm
    · rw [bindD.2 0 (by norm_num), bindD.2 1 (by norm_num),
        commA_unpack hsz (pDG 0 (by norm_num)) (pDG 1 (by norm_num))]
      simpa using dNC
    · rw [allLt_iff]
      intro l hl
      have hl2 : l < 2 := hl
      rw [bindD.2 l hl2]
      exact siftPF (Orb.allN_iff.1 siftD l hl2)
  · rw [bindC2.2 0 (by norm_num), line_eq (by norm_num), eqA_unpack' hsz (pF (by norm_num))
      (pF (by norm_num))]
    exact eq2

theorem case23 : caseChainOK 100 hs100Case23Arrs hs100Case23BaseArr hs100Case23Words
      (hs100Arr 0) (hs100Arr 1) (hs100Arr 15) = true ∧
    centOK 100 hs100Case23Arrs hs100Case23BaseArr hs100FiveLines[23]! hs100Case23Rels
      hs100FiveC23Gens hs100FiveKeys hs100FiveC23Cert 1000 = true ∧
    normalOK 100 hs100FiveC23Gens hs100FiveA23Gens hs100FiveKeys hs100FiveC23Cert
      hs100FiveA23Cert 125 hs100PLevels hs100BaseArr = true ∧
    zCentOK 100 hs100FiveA23Gens hs100FiveC23Cert hs100FiveA23Cert hs100FiveLines[23]! = true ∧
    eqA 100 hs100FiveC23Gens[0]! hs100FiveLines[23]! = true := by
  obtain ⟨a1, a2, a3⟩ := enumA23
  refine ⟨chain23, ?_, ?_, ?_, ?_⟩
  · rw [centOK_eq, line_eq (by norm_num)]
    have htail : allN (rcnt (H23.LR 0)) (ptailBranchK 100 7 H23.LR H23.TR H23.BP (F 25)
        (pw 100 7 (F 25)) hs100Case23Rels 1000 C23.T 9) = true := by
      rw [Nat.eq_of_beq_eq_true rc.2.2, show (1000 : ℕ) = C23.N from rfl]
      exact ptailBranchIdxK_le (ES := C23.S) (allN_of_blocks (L := 25) (K := 4)
        (f := ptailBranchIdxK 100 7 H23.LR H23.TR H23.BP (F 25) (pw 100 7 (F 25)) hs100Case23Rels
          C23.N C23.T C23.S 9) tailZ_all)
    exact centOKP_of hsz binds23 hperm23 H23.hl (pF (by norm_num)) rels23 bindC23 comm23
      (fun k hk => siftA_of_siftOK binds23 hperm23 H23.hl (Orb.allN_iff.1 siftC23 k hk))
      c23_enumOK c23f.1 c23f.2 c23p (by norm_num) htail
  · rw [normalOK_eq]
    exact normalOKP_of hsz a1 a2 a3 pA23 c23f.1 c23f.2 c23p bindC23 (permFc (by norm_num)) bindA23
      (permFc (by norm_num)) (fun l hl => siftPF (Orb.allN_iff.1 siftA23 l hl)) rfl normal23
  · rw [line_eq (by norm_num)]
    exact zCentOK_of hsz a2 a3 pA23 c23f.1 c23f.2 c23p bindA23 (permFc (by norm_num))
      (pF (by norm_num)) z23.1 z23.2
  · rw [bindC23.2 0 (by norm_num), line_eq (by norm_num), eqA_unpack' hsz (pF (by norm_num))
      (pF (by norm_num))]
    exact eq23

end CertificateChecks.KernelHSMcLFive

end
