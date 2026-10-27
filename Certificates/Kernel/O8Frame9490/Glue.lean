module

public import Certificates.Kernel.O8Frame9490.Checks
public import Certificates.Kernel.OmegaEight.Bridge3002
import CFSG.Certificates.Kernel.Spor.RawSiftK
import CFSG.Certificates.Kernel.U62PairMat

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8F

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CertificateChecks.KernelO8
open CFSG.KC.O8F CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Omega8Frame
open CFSG.EvenSmallLie.OmegaEightMinus CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.KC.Misc.PairCount (unpack_get)

theorem allLt_true {n : Nat} {p : Nat → Bool} :
    CFSG.Monster.B.Co2.Native.allLt n p = true ↔ ∀ i < n, p i = true := by
  unfold CFSG.Monster.B.Co2.Native.allLt
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  exact ⟨fun h i hi => h ⟨i, hi⟩ (List.mem_finRange _), fun h i _ => h i i.2⟩

theorem band {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem eqA_refl136 (t : Array Nat) : eqA 136 t t = true := by
  rw [eqA, allLt_true]
  intro i _
  simp

theorem fget_lt8 (X i : Nat) : CFSG.KLie.CT.fget X i 8 < 2 ^ 8 := by
  rw [CFSG.KC.U62P.Snd.fget_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos 8)

theorem fget_pg8 (X i : Nat) : CFSG.KLie.CT.fget X i 8 = pg 8 255 X i :=
  CFSG.KC.O8.PA.fget_eq_pg X i 8

theorem arrEqK_sound {n w : Nat} {t : Array Nat} {P : Nat} (h : arrEqK n w t P = true) :
    t = unpack n w P := by
  unfold arrEqK at h
  obtain ⟨h1, h2⟩ := band h
  have hs : t.size = n := Nat.eq_of_beq_eq_true h1
  apply Array.ext
  · simp [unpack, hs]
  · intro i hi1 hi2
    have hi : i < n := hs ▸ hi1
    have e := Nat.eq_of_beq_eq_true ((CFSG.KC.O8.PA.ctAllN_iff).1 h2 i hi)
    rw [← getElem!_pos t i hi1, ← getElem!_pos (unpack n w P) i hi2, unpack_get hi, ← e]
    simp [Array.getD, hi1, getElem!_pos]

theorem fnK_eq {f : Nat → Nat} (h : fnLtK NSM f = true) :
    (Array.ofFn (n := 136) fun j => nsIdx[f nsArr[j.val]!]!) = unpack 136 8 (fnK NSM NIM f) := by
  have hb := (CFSG.KC.O8.PA.ctAllN_iff).1 h
  unfold unpack
  congr 1
  funext i
  have hi := i.2
  have hl : f (pg 8 255 NSM i.val) < 256 := by
    have := hb i.val hi
    rwa [Nat.blt_eq, fget_pg8] at this
  have hc : ∀ k, nsMap NSM NIM f k < 2 ^ 8 := fun k => fget_lt8 _ _
  rw [← CFSG.KC.O8.PA.fget_eq_pg, fnK, CFSG.KC.U62P.Snd.fget_orN hc, if_pos hi]
  unfold nsMap
  rw [fget_pg8, fget_pg8, ns_bindM i.val hi, ni_bindM _ hl]

theorem getElem!_ofFn136 {f : Fin 136 → Nat} {k : Nat} (hk : k < 136) :
    (Array.ofFn f)[k]! = f ⟨k, hk⟩ := by
  rw [getElem!_pos _ k (by simp [hk])]
  simp

theorem cn_lt {x : Nat} (h : cnM x = true) {p : Nat} (hp : p < 136) : (unpack 136 8 x)[p]! < 136 := by
  rw [unpack_get hp]
  exact Nat.blt_eq.mp (allN_spec (range_of_canonK h) p hp)

theorem okK_iff {x : Nat} (h : okK x = true) :
    cnM x = true ∧ pmM x = true ∧ cnM (pinvM x) = true := by
  unfold okK at h
  obtain ⟨h1, h2⟩ := band h
  exact ⟨h1, band h2⟩

theorem conjA_cjM {g x : Nat} (hg : okK g = true) (hx : cnM x = true) :
    conjA (unpack 136 8 g) (unpack 136 8 x) = unpack 136 8 (cjM g x) := by
  obtain ⟨c1, c2, c3⟩ := okK_iff hg
  unfold conjA
  rw [invCand_pinvM c2, compA_pcM c1 hx, compA_pcM (cn_pcM c1 hx) c3]
  rfl

theorem cn_cj {g x : Nat} (hg : okK g = true) (hx : cnM x = true) : cnM (cjM g x) = true :=
  cn_cjM (okK_iff hg).1 (okK_iff hg).2.2 hx

theorem kBind' : (∀ j < 3, betaArrs[j]! = unpack 136 8 (J.S j)) ∧
    (∀ j < 4, t0S[j]! = unpack 136 8 (T.S j)) ∧ tauArr = unpack 136 8 TauK ∧
    sArr = unpack 136 8 SK :=
  ⟨fun j hj => arrEqK_sound (allN_spec kBindB j hj), fun j hj => arrEqK_sound (allN_spec kBindT j hj),
    arrEqK_sound kBindTau, arrEqK_sound kBindS⟩

theorem gen_ok {x : Nat} (hx : x ∈ [BK 0, BK 1, BK 2, CK, TauK, SK]) :
    okK x = true ∧ siftOm x = true := by
  have := List.all_eq_true.1 kGen x hx
  exact band this

theorem beta_eq {i : Nat} (hi : i < 3) : betaArrs[i]! = unpack 136 8 (BK i) := kBind'.1 i hi

theorem bk_ok {i : Nat} (hi : i < 3) : okK (BK i) = true := by
  interval_cases i
  · exact (gen_ok (by simp)).1
  · exact (gen_ok (by simp)).1
  · exact (gen_ok (by simp)).1

theorem c_eq : cArr = unpack 136 8 CK := kBind'.2.1 3 (by norm_num)

theorem t0_eq {k : Nat} (hk : k < 4) : t0S[k]! = unpack 136 8 ([BK 0, BK 1, BK 2, CK].getD k 0) := by
  interval_cases k
  · exact (kBind'.1 0 (by norm_num))
  · exact (kBind'.1 1 (by norm_num))
  · exact (kBind'.1 2 (by norm_num))
  · exact c_eq

theorem t0_mem {k : Nat} (hk : k < 4) :
    [BK 0, BK 1, BK 2, CK].getD k 0 ∈ [BK 0, BK 1, BK 2, CK, TauK, SK] := by
  interval_cases k <;> simp

theorem ng_eq {g : Nat} (hg : g < 3) : nGens[g]! = unpack 136 8 (NGK g) ∧ okK (NGK g) = true := by
  have e0 : NGK 0 = CK := rfl
  have e1 : NGK 1 = TauK := rfl
  have e2 : NGK 2 = SK := rfl
  interval_cases g
  · rw [e0]
    exact ⟨c_eq, (gen_ok (by simp)).1⟩
  · rw [e1]
    exact ⟨kBind'.2.2.1, (gen_ok (by simp)).1⟩
  · rw [e2]
    exact ⟨kBind'.2.2.2, (gen_ok (by simp)).1⟩

theorem idA_eq : idA 136 = unpack 136 8 pidM := idA_eqM

theorem cn_id : cnM pidM = true := kPidM'.1

theorem bindsJ : Binds 136 8 J.S 3 3 J.BP betaArrs ((frameBase.map Fin.val).toArray) := by
  refine ⟨by norm_num, by norm_num, by norm_num, rfl, kBind'.1, rfl, fun t ht => ?_⟩
  interval_cases t <;> rfl

theorem bindsT : Binds 136 8 T.S 4 3 T.BP t0S ((frameBase.map Fin.val).toArray) := by
  refine ⟨by norm_num, by norm_num, by norm_num, rfl, kBind'.2.1, rfl, fun t ht => ?_⟩
  interval_cases t <;> rfl

theorem chain_k : CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Omega8Frame.chainCheck = true := by
  unfold CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Omega8Frame.chainCheck j0W t0W
  simp only [Bool.and_eq_true]
  rw [CFSG.KC.O8.wordsOf_eq, CFSG.KC.O8.wordsOf_eq]
  refine ⟨⟨⟨rawChainK_sound (chunks := 4) bindsJ J.head J.hl (by decide) J.hs, ?_⟩,
    rawChainK_sound (chunks := 4) bindsT T.head T.hl (by decide) T.hs⟩, ?_⟩
  · rw [rawOrbitSizesK_sound bindsJ (CFSG.KS.Raw.Orb.head_facts J.head).1 J.hl]
    decide +kernel
  · rw [rawOrbitSizesK_sound bindsT (CFSG.KS.Raw.Orb.head_facts T.head).1 T.hl]
    decide +kernel

theorem siftOm_sound {x : Nat} (h : okK x = true) (hs : siftOm x = true) :
    siftA 136 omegaLevels (omegaBase.map Fin.val).toArray 0 (unpack 136 8 x) = true := by
  obtain ⟨c1, c2, -⟩ := okK_iff h
  have hG : Nat.shiftRight x (136 * 8) = 0 := by
    have h' := c1
    unfold cnM canonK at h'
    simp only [bAnd_iff] at h'
    exact Nat.eq_of_beq_eq_true h'.2.1
  unfold omegaLevels
  rw [siftK_eq bindsOmM (CFSG.KS.Raw.Orb.head_facts OmM.head).1 OmM.hl rfl hG (range_of_permOK c2)]
  exact hs

theorem siftJ_sound {x : Nat} (h : cnM x = true) (hs : siftJ x = true) :
    siftA 136 j0Levels (frameBase.map Fin.val).toArray 0 (unpack 136 8 x) = true := by
  have hG : Nat.shiftRight x (136 * 8) = 0 := by
    have h' := h
    unfold cnM canonK at h'
    simp only [bAnd_iff] at h'
    exact Nat.eq_of_beq_eq_true h'.2.1
  unfold j0Levels
  rw [siftK_eq bindsJ (CFSG.KS.Raw.Orb.head_facts J.head).1 J.hl rfl hG (range_of_canonK h)]
  exact hs

theorem suppA_eq (x : Nat) : suppA (unpack 136 8 x) = suppK x := by
  unfold suppA suppK
  refine List.countP_congr fun i hi => ?_
  rw [List.mem_range] at hi
  rw [unpack_get hi, at8]
  have hm : pg 8 (mask 8) x i = pg 8 255 x i := rfl
  rw [hm]
  cases e : Nat.beq (pg 8 255 x i) i
  · have : pg 8 255 x i ≠ i := fun h => by rw [h, Nat.beq_refl] at e; exact absurd e (by decide)
    simp [this]
  · simp [Nat.eq_of_beq_eq_true e]

theorem six_eq {k : Nat} (hk : k < 6) :
    sixArrs[k]! = unpack 136 8 (sixK k) ∧ cnM (sixK k) = true := by
  have ev : ∀ i < 3, sixArrs[2 * i]! = betaArrs[i]! ∧ sixK (2 * i) = BK i ∧
      sixArrs[2 * i + 1]! = invCand 136 betaArrs[i]! ∧ sixK (2 * i + 1) = pinvM (BK i) := by
    intro i hi
    interval_cases i <;> exact ⟨rfl, rfl, rfl, rfl⟩
  have hk' : k = 2 * (k / 2) ∨ k = 2 * (k / 2) + 1 := by omega
  have hi : k / 2 < 3 := by omega
  obtain ⟨a1, a2, a3, a4⟩ := ev (k / 2) hi
  have hb := okK_iff (bk_ok hi)
  rcases hk' with e | e
  · rw [e, a1, a2, beta_eq hi]
    exact ⟨rfl, hb.1⟩
  · rw [e, a3, a4, beta_eq hi, invCand_pinvM hb.2.1]
    exact ⟨rfl, hb.2.2⟩

theorem mem_k : CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Omega8Frame.memCheck = true := by
  unfold CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Omega8Frame.memCheck
  simp only [Bool.and_eq_true, allLt_true, Bool.or_eq_true, beq_iff_eq]
  have b0 := okK_iff (bk_ok (i := 0) (by norm_num))
  have b1 := okK_iff (bk_ok (i := 1) (by norm_num))
  have b2 := okK_iff (bk_ok (i := 2) (by norm_num))
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨fun k hk => ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, fun g hg i hi => ?_⟩, ?_⟩, ?_⟩,
    fun k hk => ?_⟩, fun k hk l hl => ?_⟩
  · have := gen_ok (t0_mem hk)
    rw [t0_eq hk]
    exact siftOm_sound this.1 this.2
  · have := gen_ok (x := TauK) (by simp)
    rw [kBind'.2.2.1]
    exact siftOm_sound this.1 this.2
  · have := gen_ok (x := SK) (by simp)
    rw [kBind'.2.2.2]
    exact siftOm_sound this.1 this.2
  · rw [kBind'.2.2.1]
    exact isInvA_ofM (okK_iff (gen_ok (x := TauK) (by simp)).1).2.1
  · rw [kBind'.2.2.2]
    exact isInvA_ofM (okK_iff (gen_ok (x := SK) (by simp)).1).2.1
  · obtain ⟨e, ho⟩ := ng_eq hg
    have hb := okK_iff (bk_ok hi)
    rw [e, beta_eq hi, conjA_cjM ho hb.1]
    exact siftJ_sound (cn_cj ho hb.1) (allN_spec (allN_spec kConj g hg) i hi)
  · have ho := (gen_ok (x := CK) (by simp)).1
    rw [c_eq, beta_eq (i := 0) (by norm_num), beta_eq (i := 1) (by norm_num), conjA_cjM ho b0.1,
      eqA_pcM (cn_cj ho b0.1) b1.1]
    exact kRel0
  · have ho := (gen_ok (x := CK) (by simp)).1
    rw [c_eq, beta_eq (i := 1) (by norm_num), beta_eq (i := 2) (by norm_num), conjA_cjM ho b1.1,
      eqA_pcM (cn_cj ho b1.1) b2.1]
    exact kRel1
  · have h := band (allN_spec kSix k hk)
    rw [(six_eq hk).1, suppA_eq]
    exact Nat.eq_of_beq_eq_true h.1
  · have h := band (allN_spec kSix k hk)
    have h2 := allN_spec h.2 l hl
    rw [(six_eq hk).1, (six_eq hl).1, eqA_pcM (six_eq hk).2 (six_eq hl).2]
    simp only [Bool.or_eq_true, beq_iff_eq] at h2 ⊢
    rcases h2 with h2 | h2
    · exact Or.inl (Nat.eq_of_beq_eq_true h2)
    · exact Or.inr h2

end CertificateChecks.KernelO8F

end
