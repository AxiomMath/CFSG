module

public import Certificates.Kernel.McL5Pairs.Checks
public import Certificates.Kernel.MaxD2.McLP.Glue
public import CFSG.Certificates.Kernel.McL5Pairs.Sound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMcL5Pairs

open CFSG.KS CFSG.KS.Raw CFSG.KS.MaxD2 CFSG.KS.McL5P CFSG.PSL3Four.Native
open Certificates.MaxD2Perm Certificates.MaxD2Heis Certificates.McLFivePairs
open CFSG.Certificates.Native (rawChainOK rawOrbitSizes)
open CertificateChecks.KernelMaxD2.McLP

theorem hc : HypsC mclFiveDataP KH := hypsH.toHypsBC.toHypsC

theorem hn : szOK 275 9 = true := hc.hn

theorem hU : perm275 (RE.G 0) (RGI 0) = true := (PK.allN_iff.1 k_rgi) 0 (by decide)
theorem hV : perm275 (RE.G 1) (RGI 1) = true := (PK.allN_iff.1 k_rgi) 1 (by decide)

theorem hu : (rGens mclFiveDataP)[0]! = unpack 275 9 (RE.G 0) := h_rg_get hypsH (by decide)
theorem hv : (rGens mclFiveDataP)[1]! = unpack 275 9 (RE.G 1) := h_rg_get hypsH (by decide)

theorem hR : ∀ i < 114, perm275 (REP i) (REPI i) = true := fun i hi => hc.hRi i hi

theorem hrep : ∀ i < 114, (repT mclFiveDataP).getD i (idTab 275) = unpack 275 9 (REP i) := by
  intro i hi
  rw [getD_get (by rw [c_rep_size hc]; exact hi)]
  exact c_rep_get hc hi

theorem hA : mclTabA = unpack 275 9 (GP 0) := gT_bind 0 (by decide)
theorem hB : mclTabB = unpack 275 9 (GP 1) := gT_bind 1 (by decide)

theorem hng : ∀ j < 4, (nGens mclFiveDataP)[j]! = unpack 275 9 (NE.G j) := fun j hj => c_ng_get hc hj
theorem hnp : ∀ j < 4, perm275 (NE.G j) (NGI j) = true := fun j hj => hc.hNI j hj
theorem hngs : (nGens mclFiveDataP).size = 4 := (c_ngens hc).1

abbrev b0 : Array Tab :=
  pairGens (rGens mclFiveDataP)[0]! (rGens mclFiveDataP)[1]!
    ((repT mclFiveDataP).getD excIdx (idTab 275))

theorem b0_eq : b0 = #[unpack 275 9 (B0 0), unpack 275 9 (B0 1), unpack 275 9 (B0 2),
    unpack 275 9 (B0 3)] := by
  have e : ∀ l < 4, B0 l = l4 (RE.G 0) (RE.G 1) (cj (REP 95) (REPI 95) (RE.G 0))
      (cj (REP 95) (REPI 95) (RE.G 1)) l :=
    fun l hl => Nat.eq_of_beq_eq_true ((PK.allN_iff.1 k_b0) l hl)
  have hr := hR 95 (by decide)
  have hg : ∀ j < 2, Cn 275 9 (RE.G j) := fun j hj => h_rg_canon hypsH hj
  unfold b0 pairGens excIdx
  rw [hu, hv, hrep 95 (by decide), conjBy_u hn hr (hg 0 (by decide)),
    conjBy_u hn hr (hg 1 (by decide)), e 0 (by decide), e 1 (by decide), e 2 (by decide),
    e 3 (by decide), l4_0, l4_1, l4_2, l4_3]

theorem hb0p : ∀ l < 4, perm275 (B0 l) (B0I l) = true := fun l hl => (PK.allN_iff.1 k_b0i) l hl

theorem b0_size : b0.size = 4 := by simp [b0_eq]

theorem hb0 : ∀ l < 4, b0[l]! = unpack 275 9 (B0 l) := by
  intro l hl
  rw [b0_eq]
  interval_cases l <;> rfl

abbrev hs : Array Tab := conjTabs (nGens mclFiveDataP) (nGensI mclFiveDataP)

theorem hs_size : hs.size = 3 := by simp [hs, conjTabs, conjWords]

theorem hhp : ∀ k < 3, perm275 (HK k) (HKI k) = true :=
  fun k hk => (band_e ((PK.allN_iff.1 k_h) k hk)).2

theorem hs_get : ∀ k < 3, hs[k]! = unpack 275 9 (HK k) := by
  intro k hk
  have hw := (band_e ((PK.allN_iff.1 k_h) k hk)).1
  unfold hs conjTabs
  rw [map_get _ (by simpa [conjWords] using hk)]
  exact wordT_u ⟨hngs, hng⟩ (PK.allN_iff.2 fun j hj => perm_of (hnp j hj)) hw

abbrev blocks : Array (Array Tab) := hs.map (blockGens b0)

theorem hbkp : ∀ q < 12, perm275 (BK q) (BKI q) = true := by
  intro q hq
  have h := (blkK_spec k_blk (q / 4) (by omega) (q % 4) (by omega)).2
  rw [Nat.div_add_mod q 4] at h
  exact h

theorem hblk : ∀ k < 3, (blocks.getD k #[]).size = 4 ∧
    ∀ l < 4, (blocks.getD k #[])[l]! = unpack 275 9 (BK (4 * k + l)) := by
  intro k hk
  have hk' : k < (hs.map (blockGens b0)).size := by simpa [hs_size] using hk
  rw [getD_get hk', map_get! _ (by simpa [hs_size] using hk)]
  refine ⟨by simp [blockGens, b0_size], fun l hl => ?_⟩
  unfold blockGens
  rw [map_get! _ (by rw [b0_size]; exact hl), hb0 l hl, hs_get k hk,
    conjBy_u hn (hhp k hk) (pc1 hn (hb0p l hl)), ← (blkK_spec k_blk k hk l hl).1]

theorem hns : ∀ j < 4, (nGens mclFiveDataP).getD j (idTab 275) = unpack 275 9 (NE.G j) :=
  fun j hj => by rw [getD_get (by rw [hngs]; exact hj)]; exact hng j hj

theorem t_pairs : pairWords.all (pairOK (rGens mclFiveDataP)[0]! (rGens mclFiveDataP)[1]!
    (repT mclFiveDataP)) = true := by
  rw [List.all_eq_true, hu, hv]
  intro e he
  have hk : pairK1 (GP 0) (GP 1) (RE.G 0) (RE.G 1) (RGI 0) (RGI 1) REP REPI e = true := by
    simp only [pairWords, List.mem_append] at he
    rcases he with (((((h | h) | h) | h) | h) | h) | h
    exacts [List.all_eq_true.1 k_pw0 e h, List.all_eq_true.1 k_pw1 e h,
      List.all_eq_true.1 k_pw2 e h, List.all_eq_true.1 k_pw3 e h,
      List.all_eq_true.1 k_pw4 e h, List.all_eq_true.1 k_pw5 e h,
      List.all_eq_true.1 k_pw6 e h]
  exact pairOK_of hn hU hV hrep hR hA hB hk

theorem t_acts : actWords.all (actOK blocks (nGens mclFiveDataP)) = true := by
  rw [List.all_eq_true]
  intro e he
  have hk : actK NE.G NGI BK BKI e = true := by
    simp only [actWords, List.mem_append] at he
    rcases he with h | h
    exacts [List.all_eq_true.1 k_act0 e h, List.all_eq_true.1 k_act1 e h]
  exact actOK_of hn hblk hbkp hns hnp hk

theorem t_joins : joinWords.all (joinOK blocks) = true := by
  rw [List.all_eq_true]
  intro e he
  exact joinOK_of hblk hbkp hA hB (List.all_eq_true.1 k_join e he)

theorem t_hasInvs : allBelow 3 (fun k => hasInv (hs.getD k (idTab 275))) = true := by
  rw [allBelow_iff']
  intro k hk
  rw [getD_get (by rw [hs_size]; exact hk), hs_get k hk]
  exact hasInv_u (hhp k hk)

theorem t_gens : allBelow 3 (fun k => gensOK (blocks.getD k #[])) = true := by
  rw [allBelow_iff']
  intro k hk
  exact gensOK_u (hblk k hk).1 (hblk k hk).2 (fun l hl => hbkp _ (by omega))

theorem chain_binds : Binds 275 9 CH.S 8 3 CH.BP (strongTabs b0) chainBase := by
  unfold Binds
  refine ⟨by decide, by decide, by decide, by simp [strongTabs, sgsWords], fun j hj => ?_,
    by decide, fun t ht => ?_⟩
  · unfold strongTabs
    rw [map_get _ (by simpa [sgsWords] using hj)]
    exact wordIn_u b0_size hb0 hb0p ((PK.allN_iff.1 k_sgs) j hj)
  · interval_cases t <;> decide +kernel

theorem t_chain : chainOK b0 = true := by
  unfold chainOK
  simp only [Bool.and_eq_true]
  have hW : rawChainOK 275 ((strongTabs b0).extract 0 4) (strongTabs b0) chainBase
      sgsWords.toArray 4 = rawChainOK 275 ((strongTabs b0).extract 0 4) (strongTabs b0) chainBase
      (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 4 8 dW) 4 := by
    refine rawChainOK_congrW (by simp [sgsWords, CFSG.Sporadic.Schreier.Co3.Native.wordsArr])
      fun j hj h4 => ?_
    have hj8 : j < 8 := by simpa [strongTabs, sgsWords] using hj
    have h4o : 4 ≤ j ∨ (strongTabs b0).size ≤ j := by simpa using h4
    have h4' : 4 ≤ j := by rcases h4o with h | h <;> omega
    interval_cases j <;> decide +kernel
  have hsz : rawOrbitSizes 275 (strongTabs b0) chainBase = [175, 72, 10] := by
    rw [rawOrbitSizesK_sound chain_binds (by exact k_chp) CH.hl]
    have er : List.range 3 = [0, 1, 2] := rfl
    rw [er, List.map_cons, List.map_cons, List.map_cons, List.map_nil,
      Nat.eq_of_beq_eq_true k_orb0, Nat.eq_of_beq_eq_true k_orb1, Nat.eq_of_beq_eq_true k_orb2]
  refine ⟨⟨gensOK_u b0_size hb0 hb0p, ?_⟩, ?_⟩
  · rw [hW]
    exact rawChainK_sound chain_binds CH.head CH.hl (by decide) CH.hs
  · simp [hsz, orbitLengths]

theorem check_true : Certificates.McLFivePairs.check () = true := by
  unfold Certificates.McLFivePairs.check
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c_invsN hc, by decide +kernel⟩, t_pairs⟩, ?_⟩, ?_⟩, by simp [conjTabs,
    conjWords]⟩, t_hasInvs⟩, t_gens⟩, by decide +kernel⟩, t_acts⟩, by decide +kernel⟩, t_joins⟩,
    t_chain⟩
  · unfold excIdx
    rw [hrep 95 (by decide)]
    exact hasInv_u (hR 95 (by decide))
  · exact gensOK_u b0_size hb0 hb0p

end CertificateChecks.KernelMcL5Pairs

end
