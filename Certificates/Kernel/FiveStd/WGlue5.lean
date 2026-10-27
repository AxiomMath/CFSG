module

public import Certificates.Kernel.FiveStd.WGlue4
public import Certificates.Data.Kernel.FiveStdKW5

public section

namespace CertificateChecks.FiveStd

open CFSG.KC.FiveStdK CFSG.GH74.GLS.LU.Local.FiveStd CFSG.GH74.GLS.LU.Local.Five

theorem conjLL_code (v : E) (L : List E) :
    (conjLL v L).map codeE = (L.map codeE).map (cjK (codeE v) (invK (codeE v))) := by
  unfold conjLL
  simp only [List.map_map, Function.comp_def, conjI_inv, conj_code]

theorem prod3_code (A B C : List E) : (prod3 A B C).map codeE =
    (A.map codeE).flatMap fun x => (B.map codeE).flatMap fun h => (C.map codeE).map fun e => mulK (mulK x h) e := by
  unfold prod3 mulLL
  simp only [List.map_flatMap, List.flatMap_map, List.flatMap_assoc, List.map_map, Function.comp_def,
    codeE_mulE]

theorem wl_code (u : E) : (WlOf u).map codeE = wlK K1c (codeE u) := by
  unfold WlOf wlK
  rw [map_filter_codeE _ _ (fun w => Nat.beq (mulK w w) zK && Nat.beq (cjK w (invK w) (codeE u)) (mulK (codeE u) zK))
    (fun x => by rw [beq_code, beq_code, codeE_mulE, codeE_zE, conj_code, codeE_mulE, codeE_zE]), K1l_codes]

theorem sylInv_code (a b : E) : (sylInv a b).map tripC = sylInvK SylT (codeE a) (codeE b) := by
  unfold sylInv sylInvK
  rw [← syl36_codes, List.filter_map]
  congr 1
  refine List.filter_congr fun q _ => ?_
  simp only [Function.comp_apply, tripC, normAll_code, List.map_cons, List.map_nil]

theorem checkX1_code (t g w : E) (S : List (E × E × List E)) :
    (commE w (conjE t w) && (eqL (closureL [g, w]) K1l && S.all fun q => (ppE w (conjE t w) 4 4).any fun v =>
      eqL q.2.2 (conjLL v (ppE g (conjE t g) 5 5)))) = x1K K1c (codeE t) (codeE g) (S.map tripC) (codeE w) := by
  unfold x1K
  rw [letB_eq, ← conj_code, ← conj_code, ← map_ppE, ← map_ppE]
  simp only [List.all_map, List.any_map, Function.comp_def, tripC, eqL_code, conjLL_code, commE_codeE,
    map_closureL, List.map_cons, List.map_nil, K1l_codes, Bool.and_assoc]

theorem checkW_of {t u a b g : E} (hgX : g ∈ X1cands) (hg : goodX1 t u a b (ppE a b 4 4) g = true)
    (h : checkWK K1c (codeE t) (codeE u) (codeE g) (sylInvK SylT (codeE a) (codeE b)) = true) :
    checkW t u a b = true := by
  unfold checkW
  dsimp only
  rw [List.all_eq_true]
  intro w hw
  have hw' : codeE w ∈ wlK K1c (codeE u) := by
    rw [← wl_code]
    exact List.mem_map_of_mem hw
  have hx := List.all_eq_true.1 h _ hw'
  rw [← sylInv_code, ← checkX1_code t g w, Bool.and_eq_true, Bool.and_eq_true] at hx
  obtain ⟨h1, h2, h3⟩ := hx
  unfold checkX1
  dsimp only
  rw [Bool.and_eq_true]
  refine ⟨h1, List.any_eq_true.2 ⟨g, List.mem_filter.2 ⟨hgX, hg⟩, ?_⟩⟩
  rw [Bool.and_eq_true]
  exact ⟨h2, h3⟩

theorem wt_cls0 : (Nat.beq (cjK 409405 (invK 409405) 82001) 78901 &&
    Nat.beq (cjK 412572 (invK 412572) (RP.getD 2 0)) 78901) = true :=
  List.all_eq_true.1 wc_cls (409405, 82001, 78901, 412572) (by decide)

theorem wt_cls1 : (Nat.beq (cjK 415680 (invK 415680) 82001) 78926 &&
    Nat.beq (cjK 409408 (invK 409408) (RP.getD 2 0)) 78926) = true :=
  List.all_eq_true.1 wc_cls (415680, 82001, 78926, 409408) (by decide)

theorem wt_cls2 : (Nat.beq (cjK 415680 (invK 415680) 29501) 79090 &&
    Nat.beq (cjK 409440 (invK 409440) (RP.getD 2 0)) 79090) = true :=
  List.all_eq_true.1 wc_cls (415680, 29501, 79090, 409440) (by decide)

theorem g2_of {tc gc g2c dc : Nat}
    (h : (Nat.beq (cjK tc (invK tc) gc) g2c && Nat.beq (cjK dc (invK dc) (RP.getD 2 0)) g2c) = true) :
    cjK tc (invK tc) gc = g2c := by
  rw [Bool.and_eq_true, beq_iff_eq'] at h
  exact h.1

theorem tp0 : TPc 0 = (79003, 79503) := rfl

theorem tp2 : TPc 2 = (19002, 116567) := rfl

theorem good0 {t u a b g : E} (ht : codeE t = 409405) (hg : codeE g = 82001) (ha : codeE a = 79003)
    (hb : codeE b = 79503) (hr : gRestK (codeE t) (codeE u) (codeE a) (codeE b) (codeE g) = true) :
    goodX1 t u a b (ppE a b 4 4) g = true := by
  have htv := valid_of_code ht (by decide +kernel)
  have hgv := valid_of_code hg (by decide +kernel)
  have hav := valid_of_code ha (by decide +kernel)
  have hbv := valid_of_code hb (by decide +kernel)
  have hcl : (Nat.beq (cjK (codeE t) (invK (codeE t)) (codeE g)) 78901 &&
      Nat.beq (cjK 412572 (invK 412572) (RP.getD 2 0)) 78901) = true := by
    rw [ht, hg]
    exact wt_cls0
  have hg2 : codeE (conjE t g) = 78901 := by rw [conj_code, ht, hg, g2_of wt_cls0]
  have hH : (ppE a b 4 4).map codeE = HT 0 := by rw [map_ppE, ha, hb, ht_eq 0 (by norm_num), tp0]
  have hXX : (ppE g (conjE t g) 5 5).map codeE = XXc 0 := by
    rw [map_ppE, hg, hg2, wx_xx 0 (by norm_num)]
    rfl
  have hNX : (prod3 (ppE g (conjE t g) 5 5) (ppE a b 4 4) [oneE, t]).map codeE = NXc 0 := by
    rw [prod3_code, hXX, hH, wx_nx 0 (by norm_num)]
    simp only [List.map_cons, List.map_nil, codeE_oneE, ht]
    rfl
  refine goodX1_of (norm_filter_of htv hgv hav hbv hcl (by decide +kernel) wc_sub0 wc_sup0 hH
    (by decide) wn0) (cen_filter_of htv hgv hcl (by decide +kernel) wc_sub0 wc_sup0)
    (nx_filter_of (W := WW 0) htv hgv hav hbv hXX hNX (wx_d 0 (by norm_num)).1 ?_ ?_ ?_) hr
  · rw [hg]
    exact (wx_d 0 (by norm_num)).2
  · rw [hg, hg2]
    exact wx0
  · rw [hg, hg2]
    exact wxs0

theorem good1 {t u a b g : E} (ht : codeE t = 415680) (hg : codeE g = 82001) (ha : codeE a = 79003)
    (hb : codeE b = 79503) (hr : gRestK (codeE t) (codeE u) (codeE a) (codeE b) (codeE g) = true) :
    goodX1 t u a b (ppE a b 4 4) g = true := by
  have htv := valid_of_code ht (by decide +kernel)
  have hgv := valid_of_code hg (by decide +kernel)
  have hav := valid_of_code ha (by decide +kernel)
  have hbv := valid_of_code hb (by decide +kernel)
  have hcl : (Nat.beq (cjK (codeE t) (invK (codeE t)) (codeE g)) 78926 &&
      Nat.beq (cjK 409408 (invK 409408) (RP.getD 2 0)) 78926) = true := by
    rw [ht, hg]
    exact wt_cls1
  have hg2 : codeE (conjE t g) = 78926 := by rw [conj_code, ht, hg, g2_of wt_cls1]
  have hH : (ppE a b 4 4).map codeE = HT 0 := by rw [map_ppE, ha, hb, ht_eq 0 (by norm_num), tp0]
  have hXX : (ppE g (conjE t g) 5 5).map codeE = XXc 1 := by
    rw [map_ppE, hg, hg2, wx_xx 1 (by norm_num)]
    rfl
  have hNX : (prod3 (ppE g (conjE t g) 5 5) (ppE a b 4 4) [oneE, t]).map codeE = NXc 1 := by
    rw [prod3_code, hXX, hH, wx_nx 1 (by norm_num)]
    simp only [List.map_cons, List.map_nil, codeE_oneE, ht]
    rfl
  refine goodX1_of (norm_filter_of htv hgv hav hbv hcl (by decide +kernel) wc_sub1 wc_sup1 hH
    (by decide) wn1) (cen_filter_of htv hgv hcl (by decide +kernel) wc_sub1 wc_sup1)
    (nx_filter_of (W := WW 1) htv hgv hav hbv hXX hNX (wx_d 1 (by norm_num)).1 ?_ ?_ ?_) hr
  · rw [hg]
    exact (wx_d 1 (by norm_num)).2
  · rw [hg, hg2]
    exact wx1
  · rw [hg, hg2]
    exact wxs1

theorem good2 {t u a b g : E} (ht : codeE t = 415680) (hg : codeE g = 29501) (ha : codeE a = 19002)
    (hb : codeE b = 116567) (hr : gRestK (codeE t) (codeE u) (codeE a) (codeE b) (codeE g) = true) :
    goodX1 t u a b (ppE a b 4 4) g = true := by
  have htv := valid_of_code ht (by decide +kernel)
  have hgv := valid_of_code hg (by decide +kernel)
  have hav := valid_of_code ha (by decide +kernel)
  have hbv := valid_of_code hb (by decide +kernel)
  have hcl : (Nat.beq (cjK (codeE t) (invK (codeE t)) (codeE g)) 79090 &&
      Nat.beq (cjK 409440 (invK 409440) (RP.getD 2 0)) 79090) = true := by
    rw [ht, hg]
    exact wt_cls2
  have hg2 : codeE (conjE t g) = 79090 := by rw [conj_code, ht, hg, g2_of wt_cls2]
  have hH : (ppE a b 4 4).map codeE = HT 2 := by rw [map_ppE, ha, hb, ht_eq 2 (by norm_num), tp2]
  have hXX : (ppE g (conjE t g) 5 5).map codeE = XXc 2 := by
    rw [map_ppE, hg, hg2, wx_xx 2 (by norm_num)]
    rfl
  have hNX : (prod3 (ppE g (conjE t g) 5 5) (ppE a b 4 4) [oneE, t]).map codeE = NXc 2 := by
    rw [prod3_code, hXX, hH, wx_nx 2 (by norm_num)]
    simp only [List.map_cons, List.map_nil, codeE_oneE, ht]
    rfl
  refine goodX1_of (norm_filter_of htv hgv hav hbv hcl (by decide +kernel) wc_sub2 wc_sup2 hH
    (by decide) wn2) (cen_filter_of htv hgv hcl (by decide +kernel) wc_sub2 wc_sup2)
    (nx_filter_of (W := WW 2) htv hgv hav hbv hXX hNX (wx_d 2 (by norm_num)).1 ?_ ?_ ?_) hr
  · rw [hg]
    exact (wx_d 2 (by norm_num)).2
  · rw [hg, hg2]
    exact wx2
  · rw [hg, hg2]
    exact wxs2

end CertificateChecks.FiveStd

end
