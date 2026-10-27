module

public import Certificates.Kernel.OmegaEight.SB3873T
public import Certificates.Kernel.OmegaEight.SB3884Data
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchL2Data
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchL2Gen

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3884

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872 CertificateChecks.KernelO8.SB3873

theorem t1Mul_eq {k m : ℕ} (z : ℕ) (hw : wOK k m = true) (hl : lOK k = true) :
    t1Mul (sFTab k m) z = MK k m z := by
  rw [t1Mul, sFTab_eq hw hl, sMul_eqK]
  rfl

theorem t1Inv_eq {k m : ℕ} (z : ℕ) (hw : wOK k m = true) (hl : lOK k = true) :
    t1Inv (sFTab k m) z = IK k m z := by
  rw [t1Inv, sFTab_eq hw hl, sMul_eqK, sInv_eqK]
  rfl

theorem nf_lt' (c : ℕ) : nfEK c < 128 ∧ nfAK c < 512 := by
  by_cases hc : c < 65536
  · exact nf_lt hc
  · rw [nfEK_ge hc, nfAK_ge hc]
    omega

@[expose] noncomputable def WAK (k m e : ℕ) : ℕ := wAll.getD (32 * k + m) 0 / 2 ^ (16 * e) % 2 ^ 16

@[expose] noncomputable def FAK (k m x : ℕ) : ℕ := mulK (WAK k m (nfEK x)) (LK k (nfAK x))

@[expose] noncomputable def wAOK (k m : ℕ) : Bool :=
  (List.range 128).all fun e => WAK k m e ==
    wprodN mulK 7 (fun l => mulK ((sH.getD k []).getD l 0) (linK (((sLeaves k).getD m []).getD l 0))) e

theorem sFm_eqA {k m : ℕ} (hw : wAOK k m = true) (hl : lOK k = true) : sFm k m = FAK k m := by
  unfold wAOK at hw
  unfold lOK at hl
  rw [List.all_eq_true] at hw hl
  have hw' : ∀ e < 128, WAK k m e = wprodN mulK 7
      (fun l => mulK ((sH.getD k []).getD l 0) (linK (((sLeaves k).getD m []).getD l 0))) e :=
    fun e he => beq_iff_eq.1 (hw e (List.mem_range.2 he))
  have hl' : ∀ a < 512, LK k a = linK (xorBits 9 (fun i => (sP.getD k []).getD i 0) a) :=
    fun a ha => beq_iff_eq.1 (hl a (List.mem_range.2 ha))
  funext c
  rw [sFm, AutData.F, sMul_eqK, FAK, hw' _ (nf_lt' c).1, hl' _ (nf_lt' c).2]
  simp only [sAutData, sNfTab_get, a9K_lin, ys_fun, AutData.Pk]
  rfl

@[expose] noncomputable def IWK (j e : ℕ) : ℕ := iotaW.getD j 0 / 2 ^ (17 * e) % 2 ^ 17

@[expose] noncomputable def ILK (j a : ℕ) : ℕ := iotaL.getD j 0 / 2 ^ (17 * a) % 2 ^ 17

@[expose] noncomputable def IoK (mul : ℕ → ℕ → ℕ) (j c : ℕ) : ℕ :=
  if c < 65536 then mul (IWK j (nfEK c)) (ILK j (nfAK c)) else 0

@[expose] noncomputable def iotaOK (mul : ℕ → ℕ → ℕ) (j : ℕ) : Bool :=
  ((List.range 128).all fun e => IWK j e == wprodN mul 7 (fun l => (s2Iota.getD j []).getD l 0) e) &&
    (List.range 512).all fun a =>
      ILK j a == wprodN mul 9 (fun i => (s2Iota.getD j []).getD (7 + i) 0) a

theorem iotaTab_get (mul : ℕ → ℕ → ℕ) {j : ℕ} (h : iotaOK mul j = true) (c : ℕ) :
    (s2IotaTab mul (s2Iota.getD j []))[c]! = IoK mul j c := by
  unfold iotaOK at h
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  unfold s2IotaTab IoK
  split
  · rename_i hc
    rw [getElem!_pos _ c (by simpa using hc), Array.getElem_map]
    simp only [List.getElem_toArray, List.getElem_range]
    obtain ⟨he, ha⟩ := nf_lt hc
    have hE : sAutData.nfE c = nfEK c := by simp only [sAutData, sNfTab_get]
    have hA : sAutData.nfA c = nfAK c := by simp only [sAutData, sNfTab_get]
    rw [hE, hA, if_pos he, if_pos ha, getElem!_pos _ _ (by simpa using he),
      getElem!_pos _ _ (by simpa using ha), Array.getElem_map, Array.getElem_map]
    simp only [List.getElem_toArray, List.getElem_range]
    rw [beq_iff_eq.1 (h.1 _ (List.mem_range.2 he)), beq_iff_eq.1 (h.2 _ (List.mem_range.2 ha))]
  · rename_i hc
    rw [getElem!_neg _ c (by simpa using hc)]
    rfl

theorem all_chunks {α : Type} {P : α → Bool} {L : List α} (n k : ℕ) (hL : L.length ≤ n * k)
    (h : ∀ s < k, ((chunks n k L).getD s []).all P = true) : L.all P = true := by
  rw [← chunks_flatten n k L hL]
  exact all_blocks _ _ fun s hs => h s (by rwa [chunks_length] at hs)

@[expose] def thPre (smul : ℕ → ℕ → ℕ) (e : ℕ) (gs : List ℕ) (ps : List (ℕ × ℕ)) : Bool :=
  decide (gs.length ≤ 5) &&
    (gs.all fun g => decide (g < 65536) && smul g (l2T.getD e 0) == smul (l2T.getD e 0) g) &&
    (ps.all fun st => decide (st.2 < gs.length) ||
      (decide (st.1 < 65536) && smul st.1 (l2T.getD e 0) == smul (l2T.getD e 0) st.1)) &&
    nodupM ((dblL smul gs ps).map Prod.fst) && (dblL smul gs ps).length == 16384 &&
    ((List.range 65536).filter fun c => smul c (l2T.getD e 0) == smul (l2T.getD e 0) c).length ==
      16384

@[expose] def thMask (smul : ℕ → ℕ → ℕ) (e : ℕ) (gs : List ℕ) (ps : List (ℕ × ℕ)) (b : ℕ) : Bool :=
  b == 0 || chiV 5 b (vecOf (dblL smul gs ps) (l2T.getD e 0)) ||
    (l2PLit.getD e []).contains
      (cntMask 5 b (fun c => smul c c == 0 && c != 0) (dblL smul gs ps),
        cntMask 5 b (fun c => smul c c != 0 && smul (smul c c) (smul c c) == 0) (dblL smul gs ps))

theorem l2THOK_of {e : ℕ} {gs : List ℕ} {ps : List (ℕ × ℕ)} (hp : thPre mulK e gs ps = true)
    (hm : ∀ s < 4, ((chunks 8 4 (List.range 32)).getD s []).all (thMask mulK e gs ps) = true) :
    l2THOK e gs ps = true := by
  have h : l2THOK e gs ps = (thPre sMul e gs ps && (List.range 32).all (thMask sMul e gs ps)) :=
    rfl
  rw [h, sMul_eqK, hp, Bool.true_and]
  exact all_chunks 8 4 (by simp) hm

@[expose] def actK (mul : ℕ → ℕ → ℕ) (io F : ℕ → ℕ) (w c : ℕ) : ℕ :=
  if c < 65536 then io (F c) else mul (io (F (c - 65536))) w

@[expose] noncomputable def chiK (c : ℕ) : Bool := decide (c < 131072) && (nfEK (c % 65536)).testBit 1

@[expose] noncomputable def l2ActK (mul : ℕ → ℕ → ℕ) (io F : ℕ → ℕ) (w v : ℕ)
    (recs : List (ℕ × List ℕ)) : Bool :=
  (recs.all fun q => l2Fix.contains q.1 || !q.2.contains (actK mul io F w q.1)) &&
    (t1Gens.all fun g => chiK (actK mul io F w g) == chiK g) && !chiK v

theorem s2F_eq {j k m : ℕ} (hk : s2K j = k) (hm : s2M j = m) : s2F j = sFTab k m := by
  rw [s2F, hk, hm]

theorem l2ActOK_eq {j k m z : ℕ} (hk : s2K j = k) (hm : s2M j = m) (hz : s2Z j = z)
    (hw : wOK k m = true) (hl : lOK k = true) (hio : iotaOK (MK k m z) j = true) {k' m' : ℕ}
    (hw' : wAOK k' m' = true) (hl' : lOK k' = true) (w v : ℕ) (recs : List (ℕ × List ℕ)) :
    l2ActOK j k' m' w v recs = l2ActK (MK k m z) (IoK (MK k m z) j) (FAK k' m') w v recs := by
  unfold l2ActOK l2ActK actK
  rw [s2F_eq hk hm, hz, t1Mul_eq z hw hl, sFm_eqA hw' hl']
  simp only [s2B, iotaTab_get _ hio, chiS_get, chiK]

@[expose] noncomputable def l2SurvK (k m z : ℕ) (I : List ℕ) (cents : List (ℕ × List ℕ × ℕ × ℕ))
    (recs : List (ℕ × List ℕ)) : Bool :=
  let C := t1Cls k m z
  (cents.all (centOK3 (MK k m z) (IK k m z) t1Gens 131072 32)) &&
    ((kRepsC C 8).all fun r => l2Like.contains r || kCount (MK k m z) I r != 1439) &&
    (l2Fix.all fun r => (cents.map Prod.fst).contains r) &&
    (cents.all fun e => !l2Fix.contains e.1 || !l2PLit.flatten.contains (e.2.2.1, e.2.2.2)) &&
    ((l2Like.zip l2O4).all fun p => cents.any fun e => e.1 == p.1 && e.2.2.1 == 1439 &&
      e.2.2.2 == p.2) &&
    ((kRepsC C 16).all fun r => recs.any fun q => q.1 == r &&
      q.2 == (recM (MK k m z) (IK k m z) t1Gens r).map Prod.fst)

@[expose] def l2SurvR (cents : List (ℕ × List ℕ × ℕ × ℕ)) : Bool :=
  (l2Fix.all fun r => (cents.map Prod.fst).contains r) &&
    (cents.all fun e => !l2Fix.contains e.1 || !l2PLit.flatten.contains (e.2.2.1, e.2.2.2)) &&
    ((l2Like.zip l2O4).all fun p => cents.any fun e => e.1 == p.1 && e.2.2.1 == 1439 &&
      e.2.2.2 == p.2)

theorem l2SurvK_of {k m z : ℕ} {I : List ℕ} {cents : List (ℕ × List ℕ × ℕ × ℕ)}
    {recs : List (ℕ × List ℕ)}
    (hc : (cents.all (centOK3 (MK k m z) (IK k m z) t1Gens 131072 32)) = true)
    (h8l : (kRepsC (t1Cls k m z) 8).length ≤ 4 * 4)
    (h8 : ∀ s < 4, ((chunks 4 4 (kRepsC (t1Cls k m z) 8)).getD s []).all
      (fun r => l2Like.contains r || kCount (MK k m z) I r != 1439) = true)
    (hR : l2SurvR cents = true)
    (h16l : (kRepsC (t1Cls k m z) 16).length ≤ 4 * 6)
    (h16 : ∀ s < 6, ((chunks 4 6 (kRepsC (t1Cls k m z) 16)).getD s []).all
      (fun r => recs.any fun q => q.1 == r &&
        q.2 == (recM (MK k m z) (IK k m z) t1Gens r).map Prod.fst) = true) :
    l2SurvK k m z I cents recs = true := by
  unfold l2SurvR at hR
  unfold l2SurvK
  dsimp only
  simp only [Bool.and_eq_true] at hR ⊢
  exact ⟨⟨⟨⟨⟨hc, all_chunks 4 4 h8l h8⟩, hR.1.1⟩, hR.1.2⟩, hR.2⟩, all_chunks 4 6 h16l h16⟩

theorem l2SurvOK_of {j k m z : ℕ} (hk : s2K j = k) (hm : s2M j = m) (hz : s2Z j = z)
    (hw : wOK k m = true) (hl : lOK k = true) {I : List ℕ} {cents : List (ℕ × List ℕ × ℕ × ℕ)}
    {recs : List (ℕ × List ℕ)} (hI : kInv (MK k m z) 131072 = I)
    (h : l2SurvK k m z I cents recs = true) : l2SurvOK j I cents recs = true := by
  unfold l2SurvK at h
  unfold l2SurvOK
  dsimp only
  rw [s2F_eq hk hm, hk, hm, hz, t1Mul_eq z hw hl, t1Inv_eq z hw hl, hI]
  simp only [Bool.and_eq_true] at h ⊢
  exact ⟨⟨⟨⟨⟨⟨h.1.1.1.1.1, beq_self_eq_true I⟩, h.1.1.1.1.2⟩, h.1.1.1.2⟩, h.1.1.2⟩, h.1.2⟩, h.2⟩

theorem l2SurvActOK_of {j k m z : ℕ} (hk : s2K j = k) (hm : s2M j = m) (hz : s2Z j = z)
    (hw : wOK k m = true) (hl : lOK k = true) (hio : iotaOK (MK k m z) j = true) {I : List ℕ}
    {cents : List (ℕ × List ℕ × ℕ × ℕ)} {recs : List (ℕ × List ℕ)}
    (hS : l2SurvOK j I cents recs = true)
    (hF : ∀ e ∈ s2Canon.getD j [], wAOK e.1 e.2.1 = true ∧ lOK e.1 = true)
    (hA : ((s2Canon.getD j []).all fun e =>
      l2ActK (MK k m z) (IoK (MK k m z) j) (FAK e.1 e.2.1) e.2.2.1 e.2.2.2 recs &&
        l2ActK (MK k m z) (IoK (MK k m z) j) (FAK e.1 e.2.1) e.2.2.1 (MK k m z e.2.2.2 24)
          recs) = true) :
    l2SurvActOK j I cents recs = true := by
  unfold l2SurvActOK
  rw [hS, Bool.true_and, List.all_eq_true]
  rw [List.all_eq_true] at hA
  intro e he
  rw [s2F_eq hk hm, hz, t1Mul_eq z hw hl]
  simp only [l2ActOK_eq hk hm hz hw hl hio (hF e he).1 (hF e he).2]
  exact hA e he

@[expose] def kEnt (smul : ℕ → ℕ → ℕ) (N : ℕ) (I : List ℕ) (tab : ℕ → ℕ) (gens : List ℕ)
    (L : List (ℕ × ℕ × ℕ × ℕ)) (i : ℕ) : Bool :=
  let ws := L.map Prod.fst
  let e := L.getD i (0, 0, 0, 0)
  decide (e.1 < N) &&
    (i == 0 || (decide (e.2.2.1 < i) && decide (e.2.2.2 < gens.length) &&
      e.1 == smul (ws.getD e.2.2.1 0) (gens.getD e.2.2.2 0))) &&
    (gens.all fun g => ws.contains (smul e.1 g)) &&
    (e.1 == 0 || (decide (e.2.1 < N) && tab e.2.1 == e.1 &&
      cInvC smul I e.1 != cInvC smul I e.2.1))

@[expose] def kDataF (smul : ℕ → ℕ → ℕ) (N : ℕ) (I : List ℕ) (tab : ℕ → ℕ) (gens : List ℕ)
    (L : List (ℕ × ℕ × ℕ × ℕ)) : Bool :=
  L.head? == some (0, 0, 0, 0) && (L.map Prod.fst).Nodup &&
    (gens.all fun g => decide (g < N)) &&
    (List.range L.length).all (kEnt smul N I tab gens L)

theorem kDataOK_eq (smul : ℕ → ℕ → ℕ) (N : ℕ) (I : List ℕ) (tab : Array ℕ) (gens : List ℕ)
    (L : List (ℕ × ℕ × ℕ × ℕ)) :
    kDataOK smul N I tab gens L = kDataF smul N I (fun c => tab[c]!) gens L := rfl

theorem kDataF_of {smul : ℕ → ℕ → ℕ} {N : ℕ} {I : List ℕ} {tab : ℕ → ℕ} {gens : List ℕ}
    {L : List (ℕ × ℕ × ℕ × ℕ)} (hL : L.length = 64)
    (h0 : (L.head? == some (0, 0, 0, 0) && (L.map Prod.fst).Nodup &&
      (gens.all fun g => decide (g < N))) = true)
    (hb : ∀ s < 8, (List.range' (8 * s) 8).all (kEnt smul N I tab gens L) = true) :
    (kDataF smul N I tab gens L && L.length == 64) = true := by
  unfold kDataF
  rw [h0, hL, Bool.true_and, beq_self_eq_true, Bool.and_true, List.all_eq_true]
  intro i hi
  have hi' := List.mem_range.1 hi
  have := List.all_eq_true.1 (hb (i / 8) (by omega)) i
    (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  exact this

theorem l2KOK_of {j k m z : ℕ} (hk : s2K j = k) (hm : s2M j = m) (hz : s2Z j = z)
    (hw : wOK k m = true) (hl : lOK k = true) (hio : iotaOK (MK k m z) j = true) {gs : List ℕ}
    {L : List (ℕ × ℕ × ℕ × ℕ)}
    (h : (kDataF mulK 65536 sInvListLit (IoK (MK k m z) j) gs L && L.length == 64) = true) :
    l2KOK j gs L = true := by
  unfold l2KOK
  rw [s2F_eq hk hm, hz, t1Mul_eq z hw hl, sMul_eqK, kInv_eq, kDataOK_eq]
  have hf : (fun c => (s2IotaTab (MK k m z) (s2Iota.getD j []))[c]!) = IoK (MK k m z) j :=
    funext (iotaTab_get _ hio)
  rw [hf]
  exact h

end CertificateChecks.KernelO8.SB3884

end
