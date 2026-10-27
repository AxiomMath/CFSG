module

public import Certificates.Kernel.HS3850.H2CM5
public import Certificates.Kernel.HS3850.Facts25371
public import CFSG.Certificates.Kernel.Spor.MulHTSound

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHS3850.H2C

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.HSAutN CFSG.KD.LQT.HN
open CFSG.KD.LQT.C4126 CFSG.KS.MulH CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.ComponentClassification.HarrisLit.N36.HS2C

theorem and_of {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by simpa using h

theorem hc_eq {k : Nat} (hk : k < 43) : hsCentTbl k = tabT (unpack 3850 12 (HC.F k)) := by
  rw [← (CFSG.KD.HS3850.cent_parts hk).1, tabT_natArr]

theorem cHC {k : Nat} (hk : k < 43) : Cn (HC.F k) := (CFSG.KD.HS3850.cent_parts hk).2

theorem small' : permK (HC.F 24) = true ∧ permK G5 = true ∧ permK X7 = true ∧ permK X5 = true ∧
    HC.F 28 = wfoldR ls8 SW7 ∧ HC.F 26 = wfoldR ls8 SW5 ∧
    Nat.beq (pc (HC.F 28) (HC.F 21)) (pc (HC.F 21) (HC.F 28)) = true ∧
    Nat.beq (pc (HC.F 26) (HC.F 21)) (pc (HC.F 21) (HC.F 26)) = true ∧
    Nat.beq (pw 7 (HC.F 28)) idn = true ∧ Nat.beq (pw 5 (HC.F 26)) idn = true := by
  have h := small
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h1, h2, h3, h4, (Nat.eq_of_beq_eq_true h5).symm, (Nat.eq_of_beq_eq_true h6).symm, h7, h8,
    h9, h10⟩

theorem permK_spec {P : Nat} (h : permK P = true) : Cn P ∧ Cn (pinv P) ∧
    invEqK 3850 12 (mask 12) (3850 * 12) P (pinv P) = true := by
  unfold permK at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem binds' : M7.k = 2 ∧ M7.cnt = 347 ∧ (∀ j < 2, M7.G j = idn) ∧ M7.GI 0 = HC.F 28 ∧
    M7.GI 1 = X7 ∧ penumHdTK idn M7.cnt M7.T M7.PL = true ∧
    M5.k = 2 ∧ M5.cnt = 732 ∧ (∀ j < 2, M5.G j = idn) ∧ M5.GI 0 = HC.F 26 ∧
    M5.GI 1 = X5 ∧ penumHdTK idn M5.cnt M5.T M5.PL = true := by
  have h := binds
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  exact ⟨h1, h2, fun j hj => Nat.eq_of_beq_eq_true (allN_spec h3 j hj), h4, h5, h6, h7, h8,
    fun j hj => Nat.eq_of_beq_eq_true (allN_spec h9 j hj), h10, h11, h12⟩

theorem pw_unpack {P : Nat} (hP : Cn P) : ∀ e,
    powT 3850 e (tabT (unpack 3850 12 P)) = tabT (unpack 3850 12 (pw e P)) ∧ Cn (pw e P)
  | 0 => by
    refine ⟨?_, cIdn⟩
    change idT 3850 = tabT (unpack 3850 12 idn)
    rw [idT_tabT, CFSG.KC.BfsPin.idA_eq (w := 12) (by decide)]
    rfl
  | e + 1 => by
    obtain ⟨h1, h2⟩ := pw_unpack hP e
    refine ⟨?_, CFSG.KD.HS3850.cn_pc hP h2⟩
    change compT 3850 (tabT (unpack 3850 12 P)) (powT 3850 e (tabT (unpack 3850 12 P))) =
      tabT (unpack 3850 12 (pc P (pw e P)))
    rw [h1, compT_unpack hP h2]
    rfl

theorem idT_eq : idT 3850 = tabT (unpack 3850 12 idn) := by
  rw [idT_tabT, CFSG.KC.BfsPin.idA_eq (w := 12) (by decide)]
  rfl

theorem slices {cnt K cap : Nat} {G GI T PL POS SRT SRI HS HSI : Nat → Nat}
    (hK : cnt ≤ 32 * K)
    (h : ∀ s < K, slK cnt (fun i => penumPtTK 3850 12 (mask 12) (3850 * 12) true G GI 2 cnt cap
      T PL POS SRT SRI i && hsortPtK 3850 12 (mask 12) cnt T HS HSI i) (32 * s) 32 = true) :
    (∀ i < cnt, penumPtTK 3850 12 (mask 12) (3850 * 12) true G GI 2 cnt cap T PL POS SRT SRI i =
      true) ∧ ∀ i < cnt, hsortPtK 3850 12 (mask 12) cnt T HS HSI i = true := by
  have hp : ∀ i < cnt, (penumPtTK 3850 12 (mask 12) (3850 * 12) true G GI 2 cnt cap T PL POS SRT
      SRI i && hsortPtK 3850 12 (mask 12) cnt T HS HSI i) = true := by
    intro i hi
    have hs : i / 32 < K := by omega
    exact slK_spec (h (i / 32) hs) i (by omega) (by omega) hi
  exact ⟨fun i hi => (and_of (hp i hi)).1, fun i hi => (and_of (hp i hi)).2⟩

theorem big_of {gens : Array Table} {cap N : Nat} {G GI T PL POS SRT SRI HS HSI : Nat → Nat}
    {cnt : Nat} (hperm : gens.all (permOK 3850) = true) (hG : ∀ j < 2, G j = pidn 3850 12)
    (hg : TabsOK 3850 12 2 GI gens) (hh : penumHdTK (pidn 3850 12) cnt T PL = true)
    (hp : ∀ i < cnt, penumPtTK 3850 12 (mask 12) (3850 * 12) true G GI 2 cnt cap T PL POS SRT SRI i =
      true)
    (hs : ∀ i < cnt, hsortPtK 3850 12 (mask 12) cnt T HS HSI i = true) (hN : N ≤ cnt) :
    big gens cap N = true := by
  obtain ⟨e1, e2, e3⟩ := mulHT_sound (by decide) hG hg hh hp hs
  unfold big
  rw [e1, hperm, e2, e3, hRec_size]
  simpa using hN

theorem all2 {a b : Table} {f : Table → Bool} (ha : f a = true) (hb : f b = true) :
    #[a, b].all f = true := by
  rw [Array.all_eq_true]
  intro i hi
  have hi2 : i < 2 := by simpa using hi
  interval_cases i
  · exact ha
  · exact hb


theorem hs2CCheck_true : hs2CCheck = true := by
  obtain ⟨k24, kG5, kX7, kX5, w7, w5, c7, c5, o7, o5⟩ := small'
  obtain ⟨m7k, m7c, m7G, m7G0, m7G1, m7h, m5k, m5c, m5G, m5G0, m5G1, m5h⟩ := binds'
  obtain ⟨c24, c24i, i24⟩ := permK_spec k24
  obtain ⟨cG5, cG5i, iG5⟩ := permK_spec kG5
  obtain ⟨cX7, cX7i, iX7⟩ := permK_spec kX7
  obtain ⟨cX5, cX5i, iX5⟩ := permK_spec kX5
  have c21 := cHC (k := 21) (by norm_num)
  have c23 := cHC (k := 23) (by norm_num)
  have c25 := cHC (k := 25) (by norm_num)
  have c26 := cHC (k := 26) (by norm_num)
  have c28 := cHC (k := 28) (by norm_num)
  have et : t2C = tabT (unpack 3850 12 (HC.F 21)) := hc_eq (by norm_num)
  have ey7 : y7 = tabT (unpack 3850 12 (HC.F 28)) := hc_eq (by norm_num)
  have ey5 : y5 = tabT (unpack 3850 12 (HC.F 26)) := hc_eq (by norm_num)
  have eg7 : g7 = tabT (unpack 3850 12 (HC.F 24)) := hc_eq (by norm_num)
  have eg5 : g5 = tabT (unpack 3850 12 G5) := by
    unfold g5
    rw [hc_eq (k := 25) (by norm_num), hc_eq (k := 23) (by norm_num), compT_unpack c25 c23]
    rfl
  have eig7 : invT 3850 g7 = tabT (unpack 3850 12 (pinv (HC.F 24))) := by
    rw [eg7, invT_unpack (by norm_num) i24]
  have eig5 : invT 3850 g5 = tabT (unpack 3850 12 (pinv G5)) := by
    rw [eg5, invT_unpack (by norm_num) iG5]
  have ex7 : x7 = tabT (unpack 3850 12 X7) := by
    unfold x7
    rw [eig7, eg7, ey7, compT_unpack c24 c28,
      compT_unpack (p := pcomp 3850 12 (mask 12) (HC.F 24) (HC.F 28)) (CFSG.KD.HS3850.cn_pc c24 c28)
        c24i]
    rfl
  have ex5 : x5 = tabT (unpack 3850 12 X5) := by
    unfold x5
    rw [eig5, eg5, ey5, compT_unpack cG5 c26,
      compT_unpack (p := pcomp 3850 12 (mask 12) G5 (HC.F 26)) (CFSG.KD.HS3850.cn_pc cG5 c26) cG5i]
    rfl
  have p21 : permOK 3850 t2C = true := CFSG.KD.LQT.HN.cent_perm (k := 21) (by norm_num) c21
  have p23 : permOK 3850 (hsCentTbl 23) = true := CFSG.KD.LQT.HN.cent_perm (by norm_num) c23
  have p25 : permOK 3850 (hsCentTbl 25) = true := CFSG.KD.LQT.HN.cent_perm (by norm_num) c25
  have py7 : permOK 3850 y7 = true := CFSG.KD.LQT.HN.cent_perm (k := 28) (by norm_num) c28
  have py5 : permOK 3850 y5 = true := CFSG.KD.LQT.HN.cent_perm (k := 26) (by norm_num) c26
  have pg7 : permOK 3850 g7 = true := CFSG.KD.LQT.HN.cent_perm (k := 24) (by norm_num) c24
  have pg5 : permOK 3850 g5 = true := by rw [eg5]; exact permOK_unpack cG5 iG5
  have px7 : permOK 3850 x7 = true := by rw [ex7]; exact permOK_unpack cX7 iX7
  have px5 : permOK 3850 x5 = true := by rw [ex5]; exact permOK_unpack cX5 iX5
  have s7 : hsSift y7 = true :=
    CFSG.KD.HS3850.sift_true_of_word (by decide) (CFSG.KD.HS3850.cent_parts (k := 28) (by norm_num)).1
      w7
  have s5 : hsSift y5 = true :=
    CFSG.KD.HS3850.sift_true_of_word (by decide) (CFSG.KD.HS3850.cent_parts (k := 26) (by norm_num)).1
      w5
  have cm7 : commTT 3850 y7 t2C = true := by rw [ey7, et, commTT_unpack c28 c21]; exact c7
  have cm5 : commTT 3850 y5 t2C = true := by rw [ey5, et, commTT_unpack c26 c21]; exact c5
  have q7 : tblEq 3850 (powT 3850 7 y7) (idT 3850) = true := by
    rw [ey7, (pw_unpack c28 7).1, idT_eq, tblEq_unpack (pw_unpack c28 7).2 cIdn]
    exact o7
  have q5 : tblEq 3850 (powT 3850 5 y5) (idT 3850) = true := by
    rw [ey5, (pw_unpack c26 5).1, idT_eq, tblEq_unpack (pw_unpack c26 5).2 cIdn]
    exact o5
  have v7 : invOK 3850 g7 (invT 3850 g7) = true := by
    rw [eig7, eg7]
    exact invOK_unpack c24 c24i i24
  have v5 : invOK 3850 g5 (invT 3850 g5) = true := by
    rw [eig5, eg5]
    exact invOK_unpack cG5 cG5i iG5
  have b7 : big #[y7, x7] 200 169 = true := by
    obtain ⟨hp, hs⟩ := slices (K := 11) (by rw [m7c]; norm_num) C7.all
    refine big_of (all2 py7 px7) (fun j hj => m7G j hj) ⟨rfl, fun j hj => ?_⟩ m7h hp hs
      (by rw [m7c]; norm_num)
    interval_cases j
    · exact ⟨by rw [m7G0, ← ey7]; rfl, by rw [m7G0]; exact c28⟩
    · exact ⟨by rw [m7G1, ← ex7]; rfl, by rw [m7G1]; exact cX7⟩
  have b5 : big #[y5, x5] 400 361 = true := by
    obtain ⟨hp, hs⟩ := slices (K := 23) (by rw [m5c]; norm_num) C5.all
    refine big_of (all2 py5 px5) (fun j hj => m5G j hj) ⟨rfl, fun j hj => ?_⟩ m5h hp hs
      (by rw [m5c]; norm_num)
    interval_cases j
    · exact ⟨by rw [m5G0, ← ey5]; rfl, by rw [m5G0]; exact c26⟩
    · exact ⟨by rw [m5G1, ← ex5]; rfl, by rw [m5G1]; exact cX5⟩
  unfold hs2CCheck
  rw [p21, p23, p25, py7, s7, cm7, q7, py5, s5, cm5, q5, pg7, v7, pg5, v5, b7, b5]
  rfl

end CertificateChecks.KernelHS3850.H2C

end
